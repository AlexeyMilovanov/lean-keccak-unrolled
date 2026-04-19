import Init.Data.BitVec
import KeccakEngine.Core
import KeccakEngine.Sponge

namespace KeccakEngine.Streaming

/--
  Dynamic Sponge context for the Streaming API (Extendable-Output Functions).
  Allows absorbing data in chunks and squeezing out hashes of arbitrary length.
-/
structure SpongeContext where
  state : Array (BitVec 64)
  buffer : ByteArray
  config : SpongeConfig
  isSqueezing : Bool

/-- Initializes a new streaming hash context. -/
def init (config : SpongeConfig) : SpongeContext :=
  { state := Array.replicate 25 (0#64),
    buffer := ByteArray.empty,
    config := config,
    isSqueezing := false }

/-- Strictly terminating loop for absorbing data chunks based on rateBytes. -/
def absorbLoop (state : Array (BitVec 64)) (buf : ByteArray) (rateBytes : Nat) (rate_pos : rateBytes > 0) : Array (BitVec 64) × ByteArray :=
  if h : buf.size >= rateBytes then
    let state' := absorbBlock state buf 0 rateBytes
    let state'' := keccakF1600_core state'
    have proof_term : buf.size - rateBytes < buf.size := by omega
    let leftover := buf.extract rateBytes buf.size
    absorbLoop state'' leftover rateBytes rate_pos
  else
    (state, buf)
termination_by buf.size

/-- Absorbs a chunk of data into the context. -/
def absorb (ctx : SpongeContext) (chunk : ByteArray) : SpongeContext :=
  if ctx.isSqueezing then
    ctx -- Cannot absorb data after squeezing has started
  else
    let combined := ctx.buffer ++ chunk
    let (newState, newBuf) := absorbLoop ctx.state combined ctx.config.rateBytes ctx.config.rateBytes_pos
    { ctx with state := newState, buffer := newBuf }

/-- Applies padding before the first squeeze operation. -/
def finalizeAbsorb (ctx : SpongeContext) : SpongeContext :=
  let padded := padBlock ctx.buffer ctx.config
  let state' := absorbBlock ctx.state padded 0 ctx.config.rateBytes
  let state'' := keccakF1600_core state'
  -- The buffer is cleared so it can now accumulate output bytes
  { ctx with state := state'', buffer := ByteArray.empty, isSqueezing := true }

/-- Strictly terminating loop for squeezing blocks (using pattern matching by block count). -/
def squeezeBlocks (state : Array (BitVec 64)) (blocks : Nat) (rateBytes : Nat) : Array (BitVec 64) × ByteArray :=
  match blocks with
  | 0 => (state, ByteArray.empty)
  | n + 1 =>
    let outBlock := squeeze state rateBytes
    let state' := keccakF1600_core state
    let (finalState, restBytes) := squeezeBlocks state' n rateBytes
    (finalState, outBlock ++ restBytes)

/-- Squeezes the requested number of bytes from the context (XOF). -/
def squeezeOut (ctx : SpongeContext) (bytesWanted : Nat) : ByteArray × SpongeContext :=
  -- If not already squeezing, apply padding and switch modes
  let ctx' := if ctx.isSqueezing then ctx else finalizeAbsorb ctx

  if ctx'.buffer.size >= bytesWanted then
    -- We already have enough bytes accumulated in the buffer
    let result := ctx'.buffer.extract 0 bytesWanted
    let leftover := ctx'.buffer.extract bytesWanted ctx'.buffer.size
    (result, { ctx' with buffer := leftover })
  else
    -- We need to run the Sponge permutation a few more times
    let deficit := bytesWanted - ctx'.buffer.size
    let blocksNeeded := (deficit + ctx'.config.rateBytes - 1) / ctx'.config.rateBytes
    let (newState, newBytes) := squeezeBlocks ctx'.state blocksNeeded ctx'.config.rateBytes

    let totalBuf := ctx'.buffer ++ newBytes
    let result := totalBuf.extract 0 bytesWanted
    let leftover := totalBuf.extract bytesWanted totalBuf.size
    (result, { ctx' with state := newState, buffer := leftover })

end KeccakEngine.Streaming
