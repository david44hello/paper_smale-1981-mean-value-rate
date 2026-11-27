/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.FigureDotBounds

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

theorem fujikawa_eight_printed_upper : fujikawa 8 ≤ (26321/10000 : ℝ) := by
  have hpower : ((4 : ℝ)^(-1/7 : ℝ))^7 = 1/4 := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (7 : ℝ)*(Real.log 4* -(1/7)) = -Real.log 4 by ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hqnonneg : 0 ≤ (4 : ℝ)^(-1/7 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hq : (4 : ℝ)^(-1/7 : ℝ) ≤ (82034/100000 : ℝ) := by
    by_contra hnot
    have horder : (82034/100000 : ℝ) ≤ (4 : ℝ)^(-1/7 : ℝ) := (lt_of_not_ge hnot).le
    have hpow : (82034/100000 : ℝ)^7 ≤ ((4 : ℝ)^(-1/7 : ℝ))^7 := by gcongr
    rw [hpower] at hpow
    norm_num at hpow
  norm_num [fujikawa]
  linarith

theorem earlier_least_fujikawa (degree : ℕ) (hdegree : 8 ≤ degree) (number : ℝ)
    (hcrane : fujikawa degree ≤ crane degree) (hnumeric : fujikawa degree ≤ number) :
    IsLeast ({fujikawa degree, conte degree, beardon degree, dubinin degree, crane degree, number} : Set ℝ)
      (fujikawa degree) := by
  have hthree := earlier_three_comparisons_proved degree hdegree
  refine ⟨by simp, ?_⟩
  intro value hvalue
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvalue
  rcases hvalue with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact le_rfl | exact hthree.1 | exact hthree.2.1.le | exact hthree.2.2.le | exact hcrane | exact hnumeric

theorem earlier_least_numeric (degree : ℕ) (hdegree : 8 ≤ degree) (number : ℝ)
    (hfujikawa : number ≤ fujikawa degree) (hcrane : number ≤ crane degree) :
    IsLeast ({fujikawa degree, conte degree, beardon degree, dubinin degree, crane degree, number} : Set ℝ) number := by
  have hthree := earlier_three_comparisons_proved degree hdegree
  refine ⟨by simp, ?_⟩
  intro value hvalue
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvalue
  rcases hvalue with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact le_rfl | exact hfujikawa | exact hfujikawa.trans hthree.1 | exact hfujikawa.trans hthree.2.1.le | exact hfujikawa.trans hthree.2.2.le | exact hcrane

theorem table2_earlier_eight_proved :
    IsLeast ({fujikawa 8, conte 8, beardon 8, dubinin 8, crane 8, (3124/1000 : ℝ)} : Set ℝ) (fujikawa 8) ∧
      fujikawa 8 ≤ (26321/10000 : ℝ) := by
  refine ⟨earlier_least_fujikawa 8 (by norm_num) (3124/1000) ?_ ?_, fujikawa_eight_printed_upper⟩
  · have hsqrt : (5/2 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
    have hsqrtpos : 0 < Real.sqrt (8 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hdiv : (2263/1000 : ℝ)/Real.sqrt 8 < 1 := (div_lt_one hsqrtpos).2 (by linarith)
    unfold crane
    linarith [fujikawa_eight_printed_upper]
  · linarith [fujikawa_eight_printed_upper]

theorem table2_earlier_hundred_proved :
    IsLeast ({fujikawa 100, conte 100, beardon 100, dubinin 100, crane 100, (3621/1000 : ℝ)} : Set ℝ)
      (3621/1000 : ℝ) ∧ (3621/1000 : ℝ) ≤ 3621/1000 := by
  have h := figure1_three_dots_below_proved (100,3621) (by simp)
  norm_num only [Prod.fst, Prod.snd, Nat.cast_ofNat] at h
  exact ⟨earlier_least_numeric 100 (by norm_num) (3621/1000)
    (lt_min_iff.mp h).1.le (lt_min_iff.mp h).2.le, le_rfl⟩

theorem table2_earlier_ten_thousand_proved :
    IsLeast ({fujikawa 10000, conte 10000, beardon 10000, dubinin 10000, crane 10000, (3955/1000 : ℝ)} : Set ℝ)
      (3955/1000 : ℝ) ∧ (3955/1000 : ℝ) ≤ 3955/1000 := by
  have h := figure1_three_dots_below_proved (10000,3955) (by simp)
  norm_num only [Prod.fst, Prod.snd, Nat.cast_ofNat] at h
  exact ⟨earlier_least_numeric 10000 (by norm_num) (3955/1000)
    (by linarith [(lt_min_iff.mp h).1]) (by linarith [(lt_min_iff.mp h).2]), le_rfl⟩

theorem table2_earlier_million_proved :
    IsLeast ({fujikawa 1000000, conte 1000000, beardon 1000000, dubinin 1000000, crane 1000000} : Set ℝ)
      (crane 1000000) ∧ crane 1000000 ≤ (39978/10000 : ℝ) := by
  have hlow := fujikawa_simple_lower 1000000 (by norm_num)
  have hcrane : crane 1000000 = (3997737/1000000 : ℝ) := by norm_num [crane]
  have hfujikawa : crane 1000000 ≤ fujikawa 1000000 := by
    rw [hcrane]
    norm_num at hlow
    linarith
  have hthree := earlier_three_comparisons_proved 1000000 (by norm_num)
  refine ⟨⟨by simp, ?_⟩, by rw [hcrane]; norm_num⟩
  intro value hvalue
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvalue
  rcases hvalue with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact le_rfl | exact hfujikawa | exact hfujikawa.trans hthree.1 | exact hfujikawa.trans hthree.2.1.le | exact hfujikawa.trans hthree.2.2.le

end SmaleRate.Proofs

#check SmaleRate.Proofs.table2_earlier_eight_proved
#print axioms SmaleRate.Proofs.table2_earlier_eight_proved
#check SmaleRate.Proofs.table2_earlier_hundred_proved
#print axioms SmaleRate.Proofs.table2_earlier_hundred_proved
#check SmaleRate.Proofs.table2_earlier_ten_thousand_proved
#print axioms SmaleRate.Proofs.table2_earlier_ten_thousand_proved
#check SmaleRate.Proofs.table2_earlier_million_proved
#print axioms SmaleRate.Proofs.table2_earlier_million_proved
