import Init.Data.BitVec
import KeccakEngine.Core

/-!
# SHA-3 Sponge Construction (Unrolled Engine)

This module implements the Keccak sponge construction. It relies on the dual-engine
architecture defined in `Core.lean` (`keccakF1600_core`) to perform the Keccak-f[1600] permutation.
This architectural choice bypasses Lean's elaborator memory limits, allowing for fully
computable Keccak hashes (and EVM selectors) at compile-time without axioms, while
falling back to a fast C-like loop for runtime execution.
-/

namespace KeccakEngine

/-- Configuration for the SHA-3 / Keccak family variants. -/
structure SpongeConfig where
  rateBytes : Nat
  rateBytes_pos : rateBytes > 0
  paddingByte : UInt8
  outputBytes : Nat

/-- Standard Ethereum Keccak-256 configuration. -/
def config_keccak256 : SpongeConfig :=
  { rateBytes := 136, rateBytes_pos := by decide, paddingByte := 0x01, outputBytes := 32 }

/-- Standard NIST SHA3-224 configuration. -/
def config_sha3_224 : SpongeConfig :=
  { rateBytes := 144, rateBytes_pos := by decide, paddingByte := 0x06, outputBytes := 28 }

/-- Standard NIST SHA3-256 configuration. -/
def config_sha3_256 : SpongeConfig :=
  { rateBytes := 136, rateBytes_pos := by decide, paddingByte := 0x06, outputBytes := 32 }

/-- Standard NIST SHA3-384 configuration. -/
def config_sha3_384 : SpongeConfig :=
  { rateBytes := 104, rateBytes_pos := by decide, paddingByte := 0x06, outputBytes := 48 }

/-- Standard NIST SHA3-512 configuration. -/
def config_sha3_512 : SpongeConfig :=
  { rateBytes := 72, rateBytes_pos := by decide, paddingByte := 0x06, outputBytes := 64 }

/-- Standard NIST SHAKE-128 configuration (outputBytes is ignored in XOF). -/
def config_shake_128 : SpongeConfig :=
  { rateBytes := 168, rateBytes_pos := by decide, paddingByte := 0x1f, outputBytes := 0 }

/-- Standard NIST SHAKE-256 configuration (outputBytes is ignored in XOF). -/
def config_shake_256 : SpongeConfig :=
  { rateBytes := 136, rateBytes_pos := by decide, paddingByte := 0x1f, outputBytes := 0 }


/--
Safely reads 1 byte from a `ByteArray`.
Returns 0 if out of bounds, avoiding runtime `panic!` during kernel evaluation.
-/
@[always_inline, inline]
def safeGetByte (bytes : ByteArray) (idx : Nat) : BitVec 64 :=
  let b := bytes[idx]? |>.getD 0
  BitVec.ofNat 64 b.toNat

/--
Reads 8 bytes from `ByteArray` starting at `offset` into a 64-bit word
using Little-Endian encoding.
-/
@[always_inline, inline]
def bytesToWordLE (bytes : ByteArray) (offset : Nat) : BitVec 64 :=
  let b0 := safeGetByte bytes (offset + 0)
  let b1 := safeGetByte bytes (offset + 1)
  let b2 := safeGetByte bytes (offset + 2)
  let b3 := safeGetByte bytes (offset + 3)
  let b4 := safeGetByte bytes (offset + 4)
  let b5 := safeGetByte bytes (offset + 5)
  let b6 := safeGetByte bytes (offset + 6)
  let b7 := safeGetByte bytes (offset + 7)

  b0 ||| (b1 <<< 8)  ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

/-- Safely sets a value in the state array. -/
@[always_inline, inline]
def safeSet (arr : Array (BitVec 64)) (idx : Nat) (val : BitVec 64) : Array (BitVec 64) :=
  arr.set! idx val

/-- Absorbs `rateBytes` into the Keccak state. -/
def absorbBlock (state : Array (BitVec 64)) (bytes : ByteArray) (offset : Nat) (rateBytes : Nat) : Array (BitVec 64) :=
  let absorbWord (s : Array (BitVec 64)) (i : Nat) :=
    let word := bytesToWordLE bytes (offset + i * 8)
    let oldWord := s.getD i 0#64
    safeSet s i (oldWord ^^^ word)

  let rateWords := rateBytes / 8
  let indices := List.range rateWords
  indices.foldl absorbWord state

/-- Pads the message tail to a full block based on the sponge rate. -/
def padBlock (leftover : ByteArray) (config : SpongeConfig) : ByteArray :=
  let arr1 := leftover.data.push config.paddingByte
  let padLen := config.rateBytes - arr1.size
  let arr2 := arr1 ++ Array.replicate padLen 0
  let lastIdx := config.rateBytes - 1
  let lastVal := arr2[lastIdx]? |>.getD 0
  let arr3 := arr2.set! lastIdx (lastVal ||| 0x80)
  ⟨arr3⟩

/--
Main Sponge Loop.
Mathematically verified termination using `omega` to prove strict reduction of remaining bytes.
-/
def spongeLoop (state : Array (BitVec 64)) (data : ByteArray) (offset : Nat) (config : SpongeConfig) : Array (BitVec 64) :=
  let remaining := data.size - offset
  if h : remaining >= config.rateBytes then
    let state' := absorbBlock state data offset config.rateBytes
    let state'' := keccakF1600_core state'
    have proof_of_termination : data.size - (offset + config.rateBytes) < data.size - offset := by
      have h_pos := config.rateBytes_pos
      omega
    spongeLoop state'' data (offset + config.rateBytes) config
  else
    let leftover := data.extract offset data.size
    let padded := padBlock leftover config
    let state' := absorbBlock state padded 0 config.rateBytes
    keccakF1600_core state'
termination_by data.size - offset

/-- Converts a 64-bit word to 8 bytes (Little-Endian). -/
def wordToBytesLE (word : BitVec 64) : Array UInt8 :=
  #[
    UInt8.ofNat (word &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 8) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 16) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 24) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 32) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 40) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 48) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 56) &&& 0xFF#64).toNat
  ]

/-- Extracts the specified number of bytes from the final state. -/
def squeeze (state : Array (BitVec 64)) (outBytes : Nat) : ByteArray :=
  let outWords := outBytes / 8
  let wordList := List.range outWords |>.map (fun i => wordToBytesLE (state.getD i 0#64))
  let allBytes := wordList.foldl (· ++ ·) #[]
  ⟨allBytes⟩

def hash_core (data : ByteArray) (config : SpongeConfig) : ByteArray :=
  let initialState := Array.replicate 25 (0#64)
  let finalState := spongeLoop initialState data 0 config
  squeeze finalState config.outputBytes

/-- Computes the Keccak-256 hash (Ethereum standard). -/
def keccak256 (data : ByteArray) : ByteArray :=
  hash_core data config_keccak256

/-- Computes the SHA3-224 hash (NIST standard). -/
def sha3_224 (data : ByteArray) : ByteArray :=
  hash_core data config_sha3_224

/-- Computes the SHA3-256 hash (NIST standard). -/
def sha3_256 (data : ByteArray) : ByteArray :=
  hash_core data config_sha3_256

/-- Computes the SHA3-384 hash (NIST standard). -/
def sha3_384 (data : ByteArray) : ByteArray :=
  hash_core data config_sha3_384

/-- Computes the SHA3-512 hash (NIST standard). -/
def sha3_512 (data : ByteArray) : ByteArray :=
  hash_core data config_sha3_512

/-- Computes the Keccak-256 hash of a UTF-8 encoded string. -/
def keccak256_str (s : String) : ByteArray :=
  keccak256 s.toUTF8

/-- Extracts the 4-byte EVM function selector from a hash (Big-Endian). -/
def getSelector (hash : ByteArray) : BitVec 32 :=
  let b0 := BitVec.ofNat 32 (hash[0]? |>.getD 0).toNat
  let b1 := BitVec.ofNat 32 (hash[1]? |>.getD 0).toNat
  let b2 := BitVec.ofNat 32 (hash[2]? |>.getD 0).toNat
  let b3 := BitVec.ofNat 32 (hash[3]? |>.getD 0).toNat
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Computes the 4-byte EVM selector directly from a function signature string. -/
def keccak256_selector (s : String) : BitVec 32 :=
  getSelector (keccak256_str s)

end KeccakEngine
