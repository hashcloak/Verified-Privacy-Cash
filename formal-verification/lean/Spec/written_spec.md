# Expected functionality for Privacy Cash

As per the [documentation](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works). 

1. Assumptions (what we trust)
2. Definitions
3. State
4. Operations
5. Invariants

## (1) Assumptions (SOL only)

Note: This is only regarding the spec - not additional assumptions we make in the full project. 

- Groth16 (Verify fn)
    - soundness
    - completeness
    - zk?
- Poseidon 
    - collision-resistance of $H_i$
- SHA-256
    - collision-resistance
- Commitment
    - hiding
    - binding
    - correctness
- Solana runtime/execution related:
    - atomicity: an instruction is either completed or reverted with no state change
    - no outside influence can cause partial application. (Might be the same as the one above)
    - persistence: state of an account is kept under all circumstances
    - TODO a property regarding arithmetics behaviour in the program
    - TODO add more as needed
- Circuit correctness; we do not formally verify the Circom code, but assume it is used to generate a proof and verify the expected circuit as described. 
- The verifying key belong to the circuit
- TODO add more as needed


## (2) Definitions

### Solana values

This is not mentioned in the docs, but is used in the checks in code.  
- $rentExemptMin \in \mathbb{N}$, the rent-exempt minimum balance. Determined by the runtime.

### Domains
- $\mathbb{Z}_p$ scalar field for $p=$
- $\mathbb{B} = \{0,1\}$
- $Pubkey = \mathbb{B}^{256}$
- $\mathbb{B}^*$ finite bit string of arbitrary length

### Hash functions; 
- Poseidon: $H_i: \mathbb{Z}_p^i \rightarrow \mathbb{Z}_p$
- SHA256: $\mathbb{B}^* \rightarrow \mathbb{B}^{256}$

### Keys
- $sk \in \mathbb{Z}_p$ : Private key
- $pk \in \mathbb{Z}_p$ : Public key. $pk = H_1(sk)$ ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/commitments-and-nullifiers#commitment-scheme) for use in commitment scheme)

### Merkle tree ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/merkle-trees#merkle-proofs))
- $R\in \mathbb{Z_p}$ : Merkle tree root. Tree height is 26. 
- $Z_0,\dots,Z_{26}\in\mathbb{Z_p}$ "zero-hash" per level ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/merkle-trees#zero-values)).
- $O=(l, P)$ is the opening of a leaf at an index (also called "Merkle proof") with
    - leaf index $l \in [0,2^{26})$ (also called `pathIndices`). For $l=\sum_{i=0}^{25}{b_i2^i}$ bit $b_i$ encodes the location of the "accumulated" hash at level $i$; 0 means left, 1 means right. (source: Circom code)
    - ordered hashes $P=(p_0,\dots,p_{25})\in\mathbb{Z_p}^{26}$
- An opening is **valid** if given $leaf\in\mathbb{Z_p}$, root $R\in\mathbb{Z_p}$ and opening $(l, P)$: if the accumulated hash $h_i$ is defined as follows for $i=0,\dots,25$:
$$
h_0=leaf, \qquad
h_{i+1}=
\begin{cases} H_2(h_i, p_i) & \text{if } b_i= 0 \\ 
H_2(p_i, h_i) & \text{if } b_i= 1 \\ 
\end{cases}
$$

    it holds that $h_{26} = R$. 


### Commitment ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/commitments-and-nullifiers#commitment-scheme))
- $c \in \mathbb{Z}_p$ Commitment. $c = H_4(N, pk, r, mintAddr)$ for amount $N\in [0,2^{248})$, public key $pk\in \mathbb{Z}_p$, blinding factor $r\in \mathbb{Z}_p$, $mintAddr\in \mathbb{Z}_p$ (token type, SOL or SPL - encoded from a Solana adress, but that happens off-chain).

### Nullifier ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/commitments-and-nullifiers#nullifiers))
- $k \in \mathbb{Z}_p$ Nullifier of an input. $k = H_3(c, l, sign)$ for:
    - $(sk, pk)$ private/public keypair for this input
    - $c = H_4(inAmt, pk, r, mintAddr )$ the commitment of the input
    - $l$ is the leaf index associated to the opening for the input
    - $sign = H_3(sk, c, l)$
        
### ZKP - Relation definition
Relation $S$ from circuit in Circom (also using [doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/zero-knowledge-proofs#transaction-circuit)). (Will not be formally verified but we need the definition.) A valid proof implies that the prover knows a witness that satisfies this relation.
- Inputs. All in $\mathbb{Z}_p$, some are constrained in the circuit. 
    - Public values:
        - $R\in\mathbb{Z_p}$ merkle tree root
        - $pubAmt\in\mathbb{Z_p}$, External amount - fee
        - $extDataHash\in\mathbb{Z_p}$. Tied to the circuit but not constrained.
        - $k_0, k_1\in\mathbb{Z_p}$, input nullifiers
        - $outC_0, outC_1\in\mathbb{Z_p}$, output commitments
    - Private values: 
        - $mintAddr\in \mathbb{Z}_p$ token type
        - for each input $i \in \{0,1\}$:
            - $inAmt_i\in \mathbb{Z}_p$ input amount
            - $inSk_i\in \mathbb{Z}_p$ private key
            - $inR_i\in \mathbb{Z}_p$ blinding factor
            - $O_i = (l_i, P_i) \in \mathbb{Z}_p \times \mathbb{Z}_p^{26}$
        - for each output $j \in \{0,1\}$:
            - $outAmt_j\in \mathbb{Z}_p$ output amount
            - $outPk_j\in \mathbb{Z}_p$ output pubkey
            - $outR_j\in \mathbb{Z}_p$ output blinding factor
- Values derived from witness:
    - Public keys for inputs $inPk_i = H_1(inSk_i)$ for $i \in \{0,1\}$.
    - Input commitments $inC_i=H_4(inAmt_i, inPk_i, inR_i, mintAddr)$ for $i \in \{0,1\}$.
    - Input signature $sign_i=H_3(inSk_i, inC_i, l_i)$ for $i \in \{0,1\}$.
- Then $S[R, pubAmt, extDataHash, k_0, k_1, outC_0, outC_1]=$ I know a witness such that all of the following hold ([doc ref 1](https://privacy-cash-privacy-cash.mintlify.app/concepts/zero-knowledge-proofs#transaction-circuit), [doc ref 2](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#security-properties) + circom code as source):
    - Output commitment integrity $outC_j=H_4(outAmt_j, outPk_j, outR_j, mintAddr)$ for $j \in \{0,1\}$.
    - Nullifier correctness $k_i=H_3(inC_i, l_i, sign_i)$ for $i \in \{0,1\}$.
    - No duplicate nullifiers $k_0 \neq k_1$.
    - For each $i$ with $inAmt_i\neq0$: Merkle proof verification $O_i$ valid for $inC_i, R$. Note that this range-checks $l_i$ for real inputs (no dummy).
    - Amount conservation $inAmt_0 + inAmt_1 + pubAmt = outAmt_0 + outAmt_1$.
    - Output range $outAmt_j\in [0,2^{248})$ for $j \in \{0,1\}$.

Notes: 
- $inAmt_i$ is not range-checked. 
- $extDataHash$ is taken as a direct input, not built from inputs in the circuit; that is only done in the smart contract. 

### ZKP
- $\Pi$ a Groth16 proof object for circuit of relation $S$.
- $d_v$ the Groth16 verifying key for circuit of relation $S$ ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/zero-knowledge-proofs#verifying-key)). A fixed value (TODO add here). 
- Verify($\Pi, x, d_v$) $\in\{0,1\}$ for proof $\Pi$, public input vector $x\in\mathbb{Z_p}^7$ and verifying key $d_v$. If 1, then there exists a witness verifying $S$. 

### Config 
- $depositLimit$; default = 1_000_000_000_000 lamports (1000 SOL)([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#universal-joinsplit-transactions))
- $WithdrawalLimit$; no withdrawal limit
- $DepositFeeRate$; default = 0%
- $WithdrawalFeeRate$; default = 25; (0.25%)
- $FeeErrorMargin$; default = 500; (5%)
- $Authority$: Responsible for updating the config. Only authority can undate it.

### Fee([ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#fee-structure))
- $DepositFeeRate$: 0% (free) but is adjustable
- $WithdrawalFeeRate$; default = 25; adjustable
- $InternalTransfer$; 0%
- $FeeErrorMargin$; default = 500; (5%) adjustable. minimum_acceptable_fee = expected_fee × (1 - fee_error_margin) where expected_fee = amount × fee_rate / 10000 and fee_error_margin = 500.


Inconsistency of doc:
- According to [these](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#security-properties) security properties, the zkp "Public amount correctly accounts for external transfers and fees". But this is **not** the case; it is only enforced in the program. What **is** checked in the circuit is the amount conservation w.r.t inputs and outputs. 

## (3) State

[Doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/merkle-trees#parameters) for Merkle Trees and how it's stored [here](https://privacy-cash-privacy-cash.mintlify.app/concepts/merkle-trees#sparse-tree-optimization). 

- Merkle tree of height 26.
    - $nextIndex\in \{0,\dots,2^{26}\}$ next leaf position. Initialized at 0. 
    - $subtrees\in\mathbb{Z_p}^{26}$, the 26 left siblings of the next leaf to stored on the path to root. This is initialized for all leaves being zero. 
    - $R$ current root
    - $\mathcal{R}$: roots history. Circular buffer of 100 most recent roots, initialized with empty-tree root in every slot
    - $rootIndex\in\{0,\dots,99\}$ initialized at $0$
- $\mathcal{N}$: set of nullifiers
- SOL balance $\in \mathbb{N}$: total SOL value held in pool in lamports
- $config$, todo ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#fee-structure))

Optional, depending on what we decide:
- $balances$: $Pubkey \rightarrow \mathbb{N}$ balances of external accounts in lamports

## (4) Operations

**Append**
- **Given**
    - $c\in\mathbb{Z_p}$ leaf 
- **Preconditions**
    - **Tree is not full**: $nextIndex < 2^{26}-1$. TODO in the docs it says check is $2^{26}$, but shouldn't it be $2^{26}-1$?
- **Effects**


**Transact**
- **Given**
    - $R\in\mathbb{Z_p}$ Merkle root
    - $pubAmt \in \mathbb{Z_p}$ public amount
    - $extDataHash\in \mathbb{Z_p}$ external data hash
    - $k_0, k_1\in \mathbb{Z_p}$ input nullifiers
    - $outC_0, outC_1\in\mathbb{Z_p}$ output commitments
    - $extAmt\in\mathbb{Z}$ external amount
    - $f\in\mathbb{N}$ fee
    - $s \in Pubkey$ (signer, only needed if we keep track of external balances)
    - $A\in Pubkey$ recipient address
    - $t \in Pubkey$ fee recipient
    - $encOut_0, encOut_1\in B^*$ encrypted outputs (see note below)
    - $\Pi$ Groth16 proof for relation $S$
    - $mintAddr\in \mathbb{Z}_p$ token type
- **Preconditions**
    1. **Root must be in last 100 roots**: $R\in \mathcal{R}$ and $R\neq 0$. Root verification [doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/merkle-trees#root-verification). 
    2. **External data binding**. **Note: this is not complete in [documentation](https://privacy-cash-privacy-cash.mintlify.app/concepts/zero-knowledge-proofs#generation-process)**: $extDataHash=hash(recipient, extAmount, fee, ...)$. Definition according to code (note that this introduces a tautology): $SHA256(A, extAmt, encOut_0, encOut_1, f, t, mintAddr)$
        - Is this definition complete?
    3. **Fee larger than minimum acceptable**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#fee-structure)): minimum_acceptable_fee = expected_fee × (1 - fee_error_margin) where 
        - fee_error_margin=500
        - expected_fee = amount × fee_rate / 10000
    4. **Public amount consistency**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#security-properties)): "Public amount correctly accounts for external transfers and fees" - this is said to be included in the ZKP but given the circuit, that is not the case. No further definition in the docs. Definition from code (note that this introduces a tautology):
        - $extAmt \neq$ i64::MIN
        - if $extAmt>0; extAmt > f$
        - $pubAmt = extAmt-f$ in $\mathbb{Z_p}$, with $extAmt$ in $\mathbb{Z_p}$
    5. **Valid ZKP**. $Verify(\Pi, (R, pubAmt, extDataHash, k_0, k_1, outC_0, outC_1), d_v)==1$
    6. **Nullifiers do not exist**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#security-properties)): $k_0\notin \mathcal{N}, k_1\notin \mathcal{N}$
    7. **Distinct nullifiers**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#security-properties)): $k_0\neq k_1$
    8. **Satisfies deposit limit**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#security-properties)): if $extAmt\gt 0; extAmt \le depositLimit$
    9. **Pool solvency**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#security-properties)): docs says "pool has sufficient balance for withdrawal", no further specification.  Definition according to code (note that this introduces a tautology): 
        - if $extAmt < 0; \text{SOL balance} \ge |extAmt| + f +rentExemptMin$
        - if $extAmt \ge 0$ AND $f > 0; \text{SOL balance} \ge f +rentExemptMin$
    10. **Tree is not full**: $nextIndex < 2^{26}-2$. 2 output UTXOs are added to the Merkle tree ([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#utxo-model)). 
- **Effects**
    - **Transfer**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#universal-joinsplit-transactions)):
        - (deposit) if $extAmt>0;$ SOL balance' = SOL balance $+ extAmt$ and $balances(s)' = balances(s) - extAmt$
        - (withdrawal) if $extAmt<0;$ SOL balance' = SOL balance $- |extAmt|$ and $balances(A)' = balances(A) + |extAmt|$
        - (transfer) if $extAmt=0;$ no changes to balances
    - **Insert nullifiers**: $\mathcal{N'}=\mathcal{N}\cup\{k_0, k_1\}$
    - **Insert output commitments** $c_j$ to the merkle tree $\tau$.([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/merkle-trees#appending-commitments))
    - Compute the **updated Merkle root** $R'$
    - **Fee transfer**

Note on encrypted outputs: $encOut_0, encOut_1$ are ciphertexts on the 2 UTXOs data, encrypted under the keys of the recipients. The recipients can then scan the chain and decrypt. 

Note on difference with Tornado Cash: $A, f, t$ are not public inputs to the circuit. 


## (5) Invariants (what is true in every state)

TODO review, add sources and expand where needed.

- ~~#roots = 100~~ <- this is already covered by the root history having length 100
- root consistency: every entry in roots is "real"; either the initial value or is an added root
- SOL balance equals net deposits minus withdrawals and fees paid out
- set of nullifiers only grows
- no double-spend
    - across transaction
    - within transaction
- only deposited coins can be withdrawn
- a note can only be withdrawn with knowledge of $k$, $r$ because we assume a Groth16 proof can only be created with that knowledge. (This one seems to be exactly the axiom of soundness, but consider the situation where withdrawing does not even check the proof. Then the soundness of the proof doesn't matter.)
