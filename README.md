# KeccakEngine 🛡️

A high-performance, **formally verified**, and fully computable implementation of the Keccak-256 and SHA-3 family hash functions in Lean 4.

This library provides standard one-shot hashing (Keccak-256, SHA3-224/256/384/512) and an Extendable-Output Function (XOF) Streaming API (SHAKE-128/256).

### The Problem: Lean's Kernel Limits
Standard recursive or loop-based implementations of Keccak-256 in Lean 4 trigger Out-of-Memory (OOM) errors or exceed recursion depth limits during compile-time evaluation (elaboration/kernel type-checking). Because the Lean Kernel strictly evaluates definitions to prove theorems, complex state mutations inside loops cause an exponential AST blowup.

### The Solution: Dual-Engine Architecture
This project solves the Kernel memory limitations without sacrificing runtime performance or relying on "dirty" axioms. It utilizes a **Dual-Engine Architecture** linked by a formal mathematical proof:

1. **The Spec Engine (`Spec.keccakF1600`):** A fast, in-place, loop-based implementation optimized for the Lean-to-C compiler. This provides maximum runtime execution speed and zero garbage collection overhead.
2. **The Verified Unrolled Engine (`Verify.keccakF1600_unrolled`):** A purely functional, flat, 24-step modular circuit designed specifically to be easily digested by the Lean Kernel during type-checking.
3. **The Golden Theorem (`keccakF1600_correct`):** We use SAT solvers (`bv_decide`) and a modular inductive proof chain to mathematically guarantee that the Unrolled Engine is **bit-for-bit identical** to the Spec Engine for all $2^{1600}$ possible states. 

By applying the `@[implemented_by Spec.keccakF1600]` attribute to our verified core, KeccakEngine achieves instantaneous compile-time evaluation for proofs, while generating blazing-fast native binaries for runtime.

---

## 🌟 Real-World Adoption: The Verity Compiler

This engine (and its foundational unrolled-circuit architecture) was instrumental in solving a critical trust-reduction issue in **[Verity](https://github.com/lfglabs-dev/verity)**, a formally verified smart contract compiler written in Lean 4.

Prior to this engine, evaluating EVM function selectors (e.g., `bytes4(keccak256("transfer(address,uint256)"))`) at compile-time in Lean required opaque, unprovable `axiom`s. By integrating the unrolled Keccak-256 architecture, Verity was able to compute and mathematically prove these selectors directly inside the Lean kernel. 

This integration allowed Verity to eliminate its cryptographic axioms and achieve a **zero-axiom proof stack** for its verified compilation pipeline. *(See Verity Issue [#1683](https://github.com/lfglabs-dev/verity/issues/1683) for the historical integration).*

---

## 🛠️ Building the Project (Important!)

Proving the mathematical equivalence of 24 rounds of Keccak-f[1600] at the bit level requires massive symbolic evaluation (`Zeta reduction`) by the Lean Kernel. 

If you run a standard `lake build` from scratch on a multi-core machine, Lean will attempt to prove all 24 rounds concurrently. This will exhaust your system's RAM and trigger the **Linux OOM (Out-Of-Memory) Killer**, causing the build to crash.

To safely build the project and cache the proofs, **you must use the provided Makefile** for the initial build:

```bash
make safe-build

**What `make safe-build` does:**
1. Removes the stack size limit (`ulimit -s unlimited`) to prevent stack overflows during deep SAT-solver evaluation.
2. Clears any corrupted cache (`lake clean`).
3. Compiles the 24 round proofs **strictly sequentially**, keeping RAM usage stable.
4. Links the final verified project.

Once `make safe-build` has completed successfully, the proofs are cached in `.lake/build`. For all subsequent development, you can safely use the standard, instantaneous command:
```bash
lake build

---

## 📂 Detailed Project Structure

### 1. The Cryptographic Core
* **`Spec.lean`** — The standard FIPS 202 Keccak-f[1600] specification. It contains pure `Id.run` loops and in-place array mutations. This is the "reference" code that actually runs in the compiled binary for maximum performance.
* **`Core.lean`** — The "Bridge" file. It defines `keccakF1600_core`, which directs the Lean Kernel to use the verified unrolled engine during proofs, but uses the `@[implemented_by]` attribute to map to `Spec.lean` for runtime execution.
* **`Sponge.lean`** — Implements the Keccak Sponge construction (padding, absorb, squeeze). It contains mathematically proven termination metrics (`omega`) for the absorption loops. It exposes the **One-Shot APIs**: `keccak256`, `sha3_256`, `sha3_512`, etc.
* **`Streaming.lean`** — Implements the **Extendable-Output Function (XOF)** API. It introduces `SpongeContext` to allow absorbing data in chunks and squeezing arbitrary lengths of bytes (required for SHAKE-128 and SHAKE-256).
* **`SpongeTest.lean`** — Formal smoke tests and test vectors. It proves alignment with NIST standards and Ethereum EVM ABI expectations directly at compile-time using `native_decide`.

### 2. The Verification Pipeline
* **`UnrolledRounds.lean`** — Contains the 24 completely flat, unrolled mathematical functions for the permutation. This is the "Kernel-friendly" version of the algorithm.
* **`Verify/Round0.lean` to `Round23.lean`** — Heavy SAT-solver (`bv_decide`) proof files. Each file mathematically proves that a single unrolled round is bit-for-bit identical to a single loop iteration of the `Spec` engine.
* **`Verify/Chain/`** — A modular, step-by-step inductive chain. Because the Lean Kernel cannot handle composing all 24 rounds at once without memory explosion (Zeta reduction blowup), this chain proves the accumulation step-by-step.
* **`Verify/Final.lean`** — The culmination of the project. Contains `keccakF1600_correct` (The Golden Theorem) which certifies the entire dual-engine architecture.

### 3. Tooling
* **`gen_final.py`** — A Python script used to autonomously generate the `Chain/` directory and `Verify/Final.lean`. It ensures the inductive proof chain is free of human error and optimally structured for the Lean elaborator.

---

## 🚀 Usage

### Compile-time Evaluation
Because the engine is fully verified and kernel-friendly, you can compute Keccak hashes and EVM function selectors strictly at compile-time using `native_decide` (which is now mathematically justified by our proofs, avoiding "dirty" axioms):

```lean
import KeccakEngine.Sponge

-- Verified by the kernel during compile-time type-checking!
theorem transfer_selector_correct : 
  keccak256_selector "transfer(address,uint256)" = 0xa9059cbb#32 := by 
  native_decide

  ### Streaming API (XOF)
For SHAKE or scenarios where data arrives in chunks (like reading a large file or network stream), you can use the `SpongeContext`:

```lean
import KeccakEngine.Streaming

def custom_shake_hash (data_chunk1 data_chunk2 : ByteArray) : ByteArray :=
  -- 1. Initialize context with desired configuration
  let ctx := KeccakEngine.Streaming.init KeccakEngine.config_shake_128
  
  -- 2. Absorb data in chunks
  let ctx := KeccakEngine.Streaming.absorb ctx data_chunk1
  let ctx := KeccakEngine.Streaming.absorb ctx data_chunk2
  
  -- 3. Squeeze out as many bytes as needed
  -- (result is a ByteArray, _ctx is the updated state for further squeezing)
  let (result, _ctx) := KeccakEngine.Streaming.squeezeOut ctx 100
  result