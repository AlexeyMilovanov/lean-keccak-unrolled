import Init.Data.BitVec

/-!
# Keccak-f[1600] Specification
Standard FIPS 202 implementation using loops and in-place array mutations.
This module is optimized for C-code generation and runtime performance.
-/

namespace KeccakEngine.Spec

private def roundConstants : Array (BitVec 64) :=
  #[0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64,
    0x8000000080008000#64, 0x000000000000808b#64, 0x0000000080000001#64,
    0x8000000080008081#64, 0x8000000000008009#64, 0x000000000000008a#64,
    0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
    0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64,
    0x8000000000008003#64, 0x8000000000008002#64, 0x8000000000000080#64,
    0x000000000000800a#64, 0x800000008000000a#64, 0x8000000080008081#64,
    0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64]

private def rotationValues : Array Nat :=
  #[0, 1, 62, 28, 27,
    36, 44, 6, 55, 20,
    3, 10, 43, 25, 39,
    41, 45, 15, 21, 8,
    18, 2, 61, 56, 14]

def theta (A : Array (BitVec 64)) : Array (BitVec 64) := Id.run do
  let mut C := Array.replicate 5 0#64
  let mut D := Array.replicate 5 0#64
  for x in [:5] do
    let mut cx := A[x]!
    for y in [1:5] do cx := cx ^^^ A[x + 5 * y]!
    C := C.set! x cx
  for x in [:5] do
    let rot := (C[(x + 1) % 5]!).rotateLeft 1
    D := D.set! x (C[(x + 4) % 5]! ^^^ rot)
  let mut newA := A
  for x in [:5] do
    for y in [:5] do
      newA := newA.set! (x + 5 * y) (A[x + 5 * y]! ^^^ D[x]!)
  return newA

def rhoPi (A : Array (BitVec 64)) : Array (BitVec 64) := Id.run do
  let mut A' := Array.replicate 25 0#64
  for x in [:5] do
    for y in [:5] do
      let i := (x + 3 * y) % 5 + 5 * x
      let rot := rotationValues[i]!
      A' := A'.set! (x + 5 * y) (A[i]!.rotateLeft rot)
  return A'

def chi (A' : Array (BitVec 64)) : Array (BitVec 64) := Id.run do
  let mut A := Array.replicate 25 0#64
  for x in [:5] do
    for y in [:5] do
      let a_next1 := A'[(x + 1) % 5 + 5 * y]!
      let a_next2 := A'[(x + 2) % 5 + 5 * y]!
      A := A.set! (x + 5 * y) (A'[x + 5 * y]! ^^^ (~~~a_next1 &&& a_next2))
  return A

def iota (A : Array (BitVec 64)) (round : Nat) : Array (BitVec 64) :=
  A.set! 0 (A[0]! ^^^ roundConstants[round]!)

/-- Executes a single round of the Keccak-f[1600] permutation. -/
def keccakF1600_round (A : Array (BitVec 64)) (round : Nat) : Array (BitVec 64) :=
  iota (chi (rhoPi (theta A))) round

/-- Executes the full 24-round Keccak-f[1600] permutation. -/
def keccakF1600 (state : Array (BitVec 64)) : Array (BitVec 64) := Id.run do
  let mut s := state
  for r in [:24] do
    s := keccakF1600_round s r
  return s

end KeccakEngine.Spec
