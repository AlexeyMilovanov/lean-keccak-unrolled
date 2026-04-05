# KeccakEngine

A Lean 4 implementation of the Keccak-256 (SHA-3) hash function, optimized for kernel evaluation.

### Purpose
Standard recursive implementations of Keccak-256 in Lean 4 often trigger Out-of-Memory (OOM) errors or exceed recursion depth limits during compile-time evaluation (elaboration). 

This project bypasses these limitations by using a **pre-generated unrolled static circuit** split into 24 round chunks. This architecture enables the Lean kernel to successfully compute hashes and EVM selectors without relying on `axiom` definitions.

### Project Structure
* **`Circuit.lean`** — Instruction set and Tracer mechanism.
* **`CircuitData.lean`** — Generated unrolled circuit data (3,720 instructions).
* **`Sponge.lean`** — Sponge construction (Absorb, Padding, Squeeze) and core API.
* **`SpongeTest.lean`** — NIST/Ethereum test vectors and EVM selector proofs.

### Usage
To verify a hash or a function selector at compile-time:

```lean
import KeccakEngine.Sponge

-- Verified by the kernel during type-checking
theorem transfer_selector_correct : 
  keccak256_selector "transfer(address,uint256)" = 0xa9059cbb#32 := by 
  native_decide
```

### Build
```bash
lake build
```
