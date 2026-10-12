//! Test vectors for the model's `syscallDecodeG1` (core-model/Model/Bn254.lean):
//! how the `alt_bn128` syscalls read a 64-byte G1 point. The decoder is
//! observed through the addition syscall: `alt_bn128_addition(b ‖ 0)` fails
//! exactly when `b` does not decode, and otherwise returns the point `b`
//! decodes to, re-encoded. Prints the vectors as the GENERATED block of
//! `core-model/Tests/G1DecodeVectors.lean`.

use solana_bn254::prelude::{alt_bn128_addition, alt_bn128_multiplication};

/// BN254 base field modulus q, big-endian.
const Q: [u8; 32] = [
    0x30, 0x64, 0x4e, 0x72, 0xe1, 0x31, 0xa0, 0x29, 0xb8, 0x50, 0x45, 0xb6, 0x81, 0x81, 0x58, 0x5d,
    0x97, 0x81, 0x6a, 0x91, 0x68, 0x71, 0xca, 0x8d, 0x3c, 0x20, 0x8c, 0x16, 0xd8, 0x7c, 0xfd, 0x47,
];

fn be_u64(v: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..].copy_from_slice(&v.to_be_bytes());
    out
}

fn point(x: [u8; 32], y: [u8; 32]) -> [u8; 64] {
    let mut p = [0u8; 64];
    p[..32].copy_from_slice(&x);
    p[32..].copy_from_slice(&y);
    p
}

/// `x + k` for a big-endian `x` whose last byte does not overflow.
fn add_small(mut x: [u8; 32], k: u8) -> [u8; 32] {
    x[31] = x[31].checked_add(k).expect("no carry");
    x
}

struct Xorshift(u64);
impl Xorshift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        let mut out = [0u8; N];
        for b in out.iter_mut() {
            *b = self.next() as u8;
        }
        out
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn main() {
    let g = point(be_u64(1), be_u64(2));
    let vk = zkcash_core::verifying_key::VERIFYING_KEY;
    let mut inputs: Vec<(&str, [u8; 64])> = vec![("all zero (the identity)", [0u8; 64]), ("generator", g)];
    inputs.push(("vk alpha", vk.vk_alpha_g1));
    for ic in vk.vk_ic {
        inputs.push(("vk ic", ic));
    }
    let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
    for _ in 0..8 {
        let k: [u8; 32] = rng.bytes();
        let input = [&g[..], &k[..]].concat();
        let p: [u8; 64] = alt_bn128_multiplication(&input).unwrap().try_into().unwrap();
        inputs.push(("k * generator", p));
    }
    let mut neg_g = g;
    neg_g[32..].copy_from_slice(&add_small(Q, 0)); // y = q, fixed below to q - 2
    neg_g[63] -= 2;
    inputs.push(("-generator (y = q - 2)", neg_g));
    // Flags live in the top two bits of y's most significant byte (byte 32).
    let mut inf = [0u8; 64];
    inf[32] = 0x40;
    inputs.push(("infinity flag", inf));
    let mut inf_x = point(be_u64(5), be_u64(7));
    inf_x[32] |= 0x40;
    inputs.push(("infinity flag, other coordinates", inf_x));
    let mut both = g;
    both[32] |= 0xc0;
    inputs.push(("both flags", both));
    let mut neg_flag = g;
    neg_flag[32] |= 0x80;
    inputs.push(("y-negative flag on the generator", neg_flag));
    inputs.push(("x = q", point(Q, be_u64(2))));
    inputs.push(("generator with x + q", point(add_small(Q, 1), be_u64(2))));
    inputs.push(("generator with y + q", point(be_u64(1), add_small(Q, 2))));
    inputs.push(("(1, 3): not on the curve", point(be_u64(1), be_u64(3))));
    let mut inf_yq = point([0u8; 32], Q);
    inf_yq[32] |= 0x40;
    inputs.push(("infinity flag, y = q", inf_yq));
    for _ in 0..8 {
        inputs.push(("random bytes", rng.bytes()));
    }

    println!("-- BEGIN GENERATED");
    println!("/-- (description, input, `alt_bn128_addition(input ‖ 0)`) -/");
    println!("def g1DecodeVectors : List (String × String × Option String) := [");
    let n = inputs.len();
    for (i, (name, b)) in inputs.iter().enumerate() {
        let input = [&b[..], &[0u8; 64][..]].concat();
        let out = match alt_bn128_addition(&input) {
            Ok(v) => format!("some \"{}\"", hex(&v)),
            Err(_) => "none".to_string(),
        };
        let sep = if i + 1 == n { "" } else { "," };
        println!("  (\"{name}\", \"{}\", {out}){sep}", hex(b));
    }
    println!("]");
    println!("-- END GENERATED");
}
