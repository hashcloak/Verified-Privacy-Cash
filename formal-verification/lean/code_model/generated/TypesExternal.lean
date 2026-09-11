-- FORWARDER. Aeneas writes `import code_model.generated.TypesExternal` into the generated
-- Types.lean, so this module name is fixed by the tool and cannot be moved. It holds NO
-- trusted content: the hand-written trusted base lives in code_model/hand_written/.
-- Everything under generated/ is machine output except this file and its Funs counterpart,
-- both of which are a single import.
import code_model.hand_written.TrustedTypes
