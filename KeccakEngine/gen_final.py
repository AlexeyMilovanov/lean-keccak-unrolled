import os

def generate_pure():
    os.makedirs("KeccakEngine/Verify/Chain", exist_ok=True)

    args_str = " ".join([f"s{i}" for i in range(25)])
    args_typed = " ".join([f"s{i}" for i in range(25)]) + " : BitVec 64"
    arr_literal = "#[" + ", ".join([f"s{i}" for i in range(25)]) + "]"

    # 1. CHAIN BASE (No let-bindings!)
    base_content = """import Init.Data.BitVec
import KeccakEngine.Spec
import KeccakEngine.UnrolledRounds

namespace KeccakEngine.Verify.Chain

set_option maxHeartbeats 0

theorem state_eq (state : Fin 25 → BitVec 64) :
  (fun x : Fin 25 =>
    if x == 0 then state 0 else if x == 1 then state 1 else if x == 2 then state 2
    else if x == 3 then state 3 else if x == 4 then state 4 else if x == 5 then state 5
    else if x == 6 then state 6 else if x == 7 then state 7 else if x == 8 then state 8
    else if x == 9 then state 9 else if x == 10 then state 10 else if x == 11 then state 11
    else if x == 12 then state 12 else if x == 13 then state 13 else if x == 14 then state 14
    else if x == 15 then state 15 else if x == 16 then state 16 else if x == 17 then state 17
    else if x == 18 then state 18 else if x == 19 then state 19 else if x == 20 then state 20
    else if x == 21 then state 21 else if x == 22 then state 22 else if x == 23 then state 23
    else state 24) = state := by
  funext x
  match x with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl
  | ⟨15, _⟩ => rfl | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl | ⟨24, _⟩ => rfl
  | ⟨n + 25, h⟩ => omega

"""
    base_content += f"def u_state_0 ({args_typed}) : Fin 25 → BitVec 64 := fun x => {arr_literal}[x.val]!\n"
    base_content += f"def s_state_0 ({args_typed}) : Array (BitVec 64) := {arr_literal}\n\n"

    for r in range(24):
        base_content += f"def u_state_{r+1} ({args_typed}) := Unrolled.round_{r} (u_state_{r} {args_str})\n"
        # Direct composition without let bindings
        unpack_str = ", ".join([f"(s_state_{r} {args_str})[{i}]!" for i in range(25)])
        base_content += f"def s_state_{r+1} ({args_typed}) := Spec.keccakF1600_round #[{unpack_str}] {r}\n\n"

    base_content += "end KeccakEngine.Verify.Chain\n"
    with open("KeccakEngine/Verify/Chain/Chain_Base.lean", "w", encoding="utf-8") as f:
        f.write(base_content)

    # 2. CHAIN FILES
    for r in range(24):
        import_prev = "Chain_Base" if r == 0 else f"Chain_{r-1:02d}"
        chain_content = f"""import KeccakEngine.Verify.Chain.{import_prev}
import KeccakEngine.Verify.Round{r}

namespace KeccakEngine.Verify.Chain

set_option maxHeartbeats 0

theorem cumul_{r} ({args_typed}) (i : Fin 25) :
  u_state_{r+1} {args_str} i = (s_state_{r+1} {args_str})[i.val]! := by
  unfold u_state_{r+1} s_state_{r+1}
"""
        if r == 0:
            chain_content += f"  have h_state : u_state_0 {args_str} = fun x => (s_state_0 {args_str})[x.val]! := by funext x; rfl\n"
        else:
            chain_content += f"  have h_state : u_state_{r} {args_str} = fun x => (s_state_{r} {args_str})[x.val]! := by funext x; exact cumul_{r-1} {args_str} x\n"

        prev_args_direct = " ".join([f"(s_state_{r} {args_str})[{i}]!" for i in range(25)])
        chain_content += f"""  rw [h_state]
  match i with
"""
        for idx in range(25):
            chain_content += f"  | ⟨{idx}, _⟩ => rw [← state_eq (fun x => (s_state_{r} {args_str})[x.val]!)]; exact round_{r}_correct_{idx} {prev_args_direct}\n"
        chain_content += "  | ⟨n + 25, h⟩ => omega\n\nend KeccakEngine.Verify.Chain\n"

        with open(f"KeccakEngine/Verify/Chain/Chain_{r:02d}.lean", "w", encoding="utf-8") as f:
            f.write(chain_content)

    # 3. FINAL MODULAR ENGINE FILE
    final_content = f"""import Init.Data.BitVec
import KeccakEngine.Spec
import KeccakEngine.UnrolledRounds
import KeccakEngine.Verify.Chain.Chain_23

namespace KeccakEngine.Verify

-- Modular steps (Independent of Proof files)
def e_step_0 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := state
"""
    for r in range(24):
        final_content += f"def e_step_{r+1} (state : Fin 25 → BitVec 64) := Unrolled.round_{r} (e_step_{r} state)\n"
    
    final_content += "\n-- The main engine function is now modular and strictly pure\n"
    final_content += "def keccakF1600_unrolled (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := e_step_24 state\n\n"

    final_content += "def s_step_0 (arr : Array (BitVec 64)) : Array (BitVec 64) := arr\n"
    for r in range(24):
        unpack = ", ".join([f"(s_step_{r} arr)[{i}]!" for i in range(25)])
        final_content += f"def s_step_{r+1} (arr : Array (BitVec 64)) := Spec.keccakF1600_round #[{unpack}] {r}\n"
    
    final_content += "\ndef spec_loop_unrolled (arr : Array (BitVec 64)) : Array (BitVec 64) := s_step_24 arr\n\n"

    final_content += f"""/--
 THE GOLDEN THEOREM (Absolute Mathematical Equivalence)
-/
theorem keccakF1600_correct ({args_typed}) (i : Fin 25) :
  let args := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let state_fn := fun x : Fin 25 => args[x.val]!
  keccakF1600_unrolled state_fn i = (spec_loop_unrolled args)[i.val]! := by
  
  -- The Lean kernel instantly proves structural identity
  -- between our independent modules (e_step) and proven chains (u_state).
  change Chain.u_state_24 {args_str} i = (Chain.s_state_24 {args_str})[i.val]!
  exact Chain.cumul_23 {args_str} i

end KeccakEngine.Verify
"""
    with open("KeccakEngine/Verify/Final.lean", "w", encoding="utf-8") as f:
        f.write(final_content)
    print("Clean Modular Architecture generated!")

if __name__ == "__main__":
    generate_pure()