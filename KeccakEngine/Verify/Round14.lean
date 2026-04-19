import Init.Data.BitVec
import KeccakEngine.Spec
import KeccakEngine.UnrolledRounds
import Std.Tactic.BVDecide

namespace KeccakEngine.Verify

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

def eval_unrolled_14_0 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 0

def eval_spec_14_0 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[0]!

theorem round_14_correct_0 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_0 eval_spec_14_0 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_1 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 1

def eval_spec_14_1 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[1]!

theorem round_14_correct_1 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_1 eval_spec_14_1 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_2 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 2

def eval_spec_14_2 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[2]!

theorem round_14_correct_2 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_2 eval_spec_14_2 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_3 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 3

def eval_spec_14_3 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[3]!

theorem round_14_correct_3 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_3 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_3 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_3 eval_spec_14_3 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_4 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 4

def eval_spec_14_4 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[4]!

theorem round_14_correct_4 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_4 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_4 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_4 eval_spec_14_4 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_5 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 5

def eval_spec_14_5 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[5]!

theorem round_14_correct_5 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_5 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_5 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_5 eval_spec_14_5 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_6 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 6

def eval_spec_14_6 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[6]!

theorem round_14_correct_6 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_6 eval_spec_14_6 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_7 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 7

def eval_spec_14_7 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[7]!

theorem round_14_correct_7 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_7 eval_spec_14_7 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_8 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 8

def eval_spec_14_8 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[8]!

theorem round_14_correct_8 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_8 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_8 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_8 eval_spec_14_8 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_9 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 9

def eval_spec_14_9 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[9]!

theorem round_14_correct_9 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_9 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_9 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_9 eval_spec_14_9 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_10 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 10

def eval_spec_14_10 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[10]!

theorem round_14_correct_10 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_10 eval_spec_14_10 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_11 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 11

def eval_spec_14_11 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[11]!

theorem round_14_correct_11 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_11 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_11 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_11 eval_spec_14_11 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_12 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 12

def eval_spec_14_12 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[12]!

theorem round_14_correct_12 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_12 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_12 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_12 eval_spec_14_12 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_13 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 13

def eval_spec_14_13 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[13]!

theorem round_14_correct_13 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_13 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_13 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_13 eval_spec_14_13 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_14 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 14

def eval_spec_14_14 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[14]!

theorem round_14_correct_14 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_14 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_14 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_14 eval_spec_14_14 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_15 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 15

def eval_spec_14_15 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[15]!

theorem round_14_correct_15 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_15 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_15 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_15 eval_spec_14_15 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_16 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 16

def eval_spec_14_16 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[16]!

theorem round_14_correct_16 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_16 eval_spec_14_16 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_17 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 17

def eval_spec_14_17 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[17]!

theorem round_14_correct_17 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_17 eval_spec_14_17 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_18 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 18

def eval_spec_14_18 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[18]!

theorem round_14_correct_18 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_18 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_18 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_18 eval_spec_14_18 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_19 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 19

def eval_spec_14_19 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[19]!

theorem round_14_correct_19 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_19 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_19 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_19 eval_spec_14_19 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_20 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 20

def eval_spec_14_20 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[20]!

theorem round_14_correct_20 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_20 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_20 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_20 eval_spec_14_20 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_21 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 21

def eval_spec_14_21 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[21]!

theorem round_14_correct_21 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_21 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_21 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_21 eval_spec_14_21 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_22 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 22

def eval_spec_14_22 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[22]!

theorem round_14_correct_22 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_22 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_22 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_22 eval_spec_14_22 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_23 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 23

def eval_spec_14_23 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[23]!

theorem round_14_correct_23 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_23 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_23 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_23 eval_spec_14_23 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

def eval_unrolled_14_24 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let state := fun x : Fin 25 => if x == 0 then s0 else if x == 1 then s1 else if x == 2 then s2 else if x == 3 then s3 else if x == 4 then s4 else if x == 5 then s5 else if x == 6 then s6 else if x == 7 then s7 else if x == 8 then s8 else if x == 9 then s9 else if x == 10 then s10 else if x == 11 then s11 else if x == 12 then s12 else if x == 13 then s13 else if x == 14 then s14 else if x == 15 then s15 else if x == 16 then s16 else if x == 17 then s17 else if x == 18 then s18 else if x == 19 then s19 else if x == 20 then s20 else if x == 21 then s21 else if x == 22 then s22 else if x == 23 then s23 else s24
  Unrolled.round_14 state 24

def eval_spec_14_24 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : BitVec 64 :=
  let arr := #[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24]
  let out := Spec.keccakF1600_round arr 14
  out[24]!

theorem round_14_correct_24 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) : eval_unrolled_14_24 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_24 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 := by
  unfold eval_unrolled_14_24 eval_spec_14_24 Unrolled.round_14 Spec.keccakF1600_round Spec.iota Spec.chi Spec.rhoPi Spec.theta
  simp (config := { ground := true }) <;> try bv_decide

theorem round_14_correct (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 : BitVec 64) :
  eval_unrolled_14_0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_3 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_3 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_4 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_4 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_5 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_5 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_8 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_8 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_9 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_9 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_11 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_11 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_12 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_12 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_13 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_13 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_14 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_14 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_15 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_15 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_18 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_18 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_19 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_19 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_20 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_20 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_21 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_21 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_22 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_22 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_23 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_23 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 ∧
  eval_unrolled_14_24 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 = eval_spec_14_24 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 :=
  ⟨round_14_correct_0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_3 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_4 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_5 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_8 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_9 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_11 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_12 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_13 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_14 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_15 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_18 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_19 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_20 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_21 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_22 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_23 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24, round_14_correct_24 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24⟩

end KeccakEngine.Verify
