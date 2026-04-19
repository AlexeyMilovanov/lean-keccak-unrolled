import Init.Data.BitVec
import KeccakEngine.Spec
import KeccakEngine.Verify.Final

namespace KeccakEngine

/--
  DUAL-ENGINE CORE (VERIFIED)

  Theoretical implementation (used by the Lean kernel during type-checking and proofs):
  Our clean, formally verified modular circuit `Verify.keccakF1600_unrolled`.
  We have mathematically proven (in Verify/Final.lean) that it is absolutely identical
  to the FIPS 202 standard.

  Runtime implementation (used in the compiled binary):
  The `Spec.keccakF1600` specification, which uses in-place array mutations via loops.
  This provides maximum C-code execution speed and eliminates garbage collection overhead.

  LEGALIZATION: The @[implemented_by] attribute is mathematically justified by the `keccakF1600_correct` theorem.
-/
@[implemented_by Spec.keccakF1600]
def keccakF1600_core (state : Array (BitVec 64)) : Array (BitVec 64) :=
  -- Array bounds protection
  if state.size = 25 then
    -- Convert array to a pure function as required by our unrolled engine
    let state_fn := fun x : Fin 25 => state[x.val]!
    -- Process through the verified unrolled circuit
    let out_fn := Verify.keccakF1600_unrolled state_fn
    -- Reassemble into an array for compatibility with the external API
    #[out_fn 0, out_fn 1, out_fn 2, out_fn 3, out_fn 4,
      out_fn 5, out_fn 6, out_fn 7, out_fn 8, out_fn 9,
      out_fn 10, out_fn 11, out_fn 12, out_fn 13, out_fn 14,
      out_fn 15, out_fn 16, out_fn 17, out_fn 18, out_fn 19,
      out_fn 20, out_fn 21, out_fn 22, out_fn 23, out_fn 24]
  else
    state

end KeccakEngine
