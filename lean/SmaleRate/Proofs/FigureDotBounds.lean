/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.EarlierComparisons

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

theorem fujikawa_rational_upper (degree : ℕ) (hdegree : 8 ≤ degree) :
    fujikawa degree ≤ 4*(1+((degree : ℝ)-2)*
      (1-(1386/1000 : ℝ)/((degree : ℝ)-1)+((1386/1000 : ℝ)/((degree : ℝ)-1))^2/2))/((degree : ℝ)+1) := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hden : 0 < (degree : ℝ)-1 := by linarith
  have hdminus : 0 ≤ (degree : ℝ)-2 := by linarith
  have hlog : (1386/1000 : ℝ) ≤ Real.log 4 := by
    rw [earlier_log_four]
    linarith [Real.log_two_gt_d9]
  have he := exp_lower ((1386/1000 : ℝ)/((degree : ℝ)-1)) (by positivity)
  have hq : (4 : ℝ)^(-1/((degree : ℝ)-1)) ≤
      1-(1386/1000 : ℝ)/((degree : ℝ)-1)+((1386/1000 : ℝ)/((degree : ℝ)-1))^2/2 := by
    rw [earlier_q_exp]
    have hmono := Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right hlog hden.le))
    exact hmono.trans (by linarith)
  unfold fujikawa
  rw [Nat.cast_sub (by omega : 2 ≤ degree)]
  norm_num only [Nat.cast_ofNat]
  gcongr
  norm_num at hq
  exact hq

theorem fujikawa_simple_lower (degree : ℕ) (hdegree : 8 ≤ degree) :
    4-4*(339/100 : ℝ)/((degree : ℝ)+1) < fujikawa degree := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hbracket := (earlier_bracket_bound_proved degree hdegree).1.trans
    (earlier_bracket_bound_proved degree hdegree).2
  have hid : 4-fujikawa degree =
      4*(((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2)/((degree : ℝ)+1) := by
    unfold fujikawa
    rw [Nat.cast_sub (by omega : 2 ≤ degree)]
    norm_num only [Nat.cast_ofNat]
    field_simp
    <;> ring
  have hgap : 4-fujikawa degree < 4*(339/100 : ℝ)/((degree : ℝ)+1) := by
    rw [hid]
    apply (div_lt_div_iff_of_pos_right (by linarith : 0 < (degree : ℝ)+1)).2
    linarith
  linarith

theorem figure1_six_dots_above_proved : ∀ entry ∈
    ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271)] : List (ℕ × ℕ)),
    min (fujikawa entry.1) (crane entry.1) < (entry.2 : ℝ)/1000 := by
  have h8 := fujikawa_rational_upper 8 (by norm_num)
  have h9 := fujikawa_rational_upper 9 (by norm_num)
  have h10 := fujikawa_rational_upper 10 (by norm_num)
  have h11 := fujikawa_rational_upper 11 (by norm_num)
  have h12 := fujikawa_rational_upper 12 (by norm_num)
  have h16 := fujikawa_rational_upper 16 (by norm_num)
  norm_num at h8 h9 h10 h11 h12 h16
  intro entry hentry
  apply (min_le_left (fujikawa entry.1) (crane entry.1)).trans_lt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num only [Prod.fst, Prod.snd, Nat.cast_ofNat]; linarith

theorem figure1_three_dots_below_proved : ∀ entry ∈
    ([(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    (entry.2 : ℝ)/1000 < min (fujikawa entry.1) (crane entry.1) := by
  have h25 := fujikawa_simple_lower 25 (by norm_num)
  have h100 := fujikawa_simple_lower 100 (by norm_num)
  have h10000 := fujikawa_simple_lower 10000 (by norm_num)
  norm_num at h25 h100 h10000
  intro entry hentry
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl
  all_goals
    norm_num only [Prod.fst, Prod.snd, Nat.cast_ofNat]
    exact lt_min (by linarith) (by norm_num [crane])

theorem figure1_excluded_regions_of_corollary (degree : ℕ) (hdegree : 8 ≤ degree)
    (hKd : Kd degree < (target degree : EReal)) (hbest : bestBound degree < target degree) :
    Kd degree ≤ ((min (fujikawa degree) (crane degree) : ℝ) : EReal) ∧
      bestBound degree < min (fujikawa degree) (crane degree) := by
  have htarget : target degree < min (fujikawa degree) (crane degree) :=
    lt_min (earlier_fujikawa_comparison_proved degree hdegree) (earlier_crane_comparison_proved degree hdegree)
  exact ⟨(hKd.trans (by exact_mod_cast htarget)).le, hbest.trans htarget⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.figure1_six_dots_above_proved
#print axioms SmaleRate.Proofs.figure1_six_dots_above_proved
#check SmaleRate.Proofs.figure1_three_dots_below_proved
#print axioms SmaleRate.Proofs.figure1_three_dots_below_proved
#check SmaleRate.Proofs.figure1_excluded_regions_of_corollary
#print axioms SmaleRate.Proofs.figure1_excluded_regions_of_corollary
