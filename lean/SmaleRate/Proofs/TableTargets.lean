/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.CraneNumbers
import SmaleRate.Proofs.TableCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

theorem table2_target_bounds : target 8 ≤ (20765/10000 : ℝ) ∧
    target 100 ≤ (31315/10000 : ℝ) ∧ target 10000 ≤ (35658/10000 : ℝ) ∧
    target 1000000 ≤ (37105/10000 : ℝ) := by
  have hlog (index : ℕ) : Real.log (((2 : ℝ)*5)^index) = (index : ℝ)*(Real.log 2+Real.log 5) := by
    rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
  have h100 : ell 100 = 2*(Real.log 2+Real.log 5) := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (100 : ℝ) = ((2 : ℝ)*5)^2 by norm_num, hlog]
    norm_num
  have h10000 : ell 10000 = 4*(Real.log 2+Real.log 5) := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (10000 : ℝ) = ((2 : ℝ)*5)^4 by norm_num, hlog]
    norm_num
  have hmillion : ell 1000000 = 6*(Real.log 2+Real.log 5) := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (1000000 : ℝ) = ((2 : ℝ)*5)^6 by norm_num, hlog]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [table3_rounding_eight.2.2]
  · apply le_of_lt
    apply target_lt_from_log_upper 100 (46052/10000) (31315/10000)
    · linarith [ell_gt_one 100 (by norm_num)]
    · rw [h100]; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    · norm_num
    · norm_num
  · apply le_of_lt
    apply target_lt_from_log_upper 10000 (92104/10000) (35658/10000)
    · linarith [ell_gt_one 10000 (by norm_num)]
    · rw [h10000]; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    · norm_num
    · norm_num
  · apply le_of_lt
    apply target_lt_from_log_upper 1000000 (138156/10000) (37105/10000)
    · linarith [ell_gt_one 1000000 (by norm_num)]
    · rw [hmillion]; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    · norm_num
    · norm_num

theorem table2_point_of_beta (degree : ℕ) (length targetBound betaBound : ℝ)
    (hlength : 0 < length) (htarget : target degree ≤ targetBound)
    (hbeta : beta degree length ≤ betaBound) :
    target degree ≤ targetBound ∧ beta degree length ≤ betaBound ∧ bestBound degree ≤ betaBound := by
  exact ⟨htarget, hbeta, (best_bound_le_beta degree length hlength).trans hbeta⟩

theorem figure_gap_lower_of_beta (degree : ℕ) (hdegree : 8 ≤ degree) (length bound : ℝ)
    (hlength : 0 < length) (hbeta : beta degree length ≤ bound) :
    (4-bound)*ell degree ≤ gap degree := by
  have hbest := (best_bound_le_beta degree length hlength).trans hbeta
  have hepos : 0 ≤ ell degree := by linarith [ell_gt_one degree hdegree]
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left hbest 4) hepos

theorem best_bound_upper_of_beta_strict (degree : ℕ) (length bound : ℝ)
    (hlength : 0 < length) (hbeta : beta degree length < bound) : bestBound degree < bound :=
  (best_bound_le_beta degree length hlength).trans_lt hbeta

end SmaleRate.Proofs

#check SmaleRate.Proofs.table2_target_bounds
#print axioms SmaleRate.Proofs.table2_target_bounds
#check SmaleRate.Proofs.table2_point_of_beta
#print axioms SmaleRate.Proofs.table2_point_of_beta
#check SmaleRate.Proofs.figure_gap_lower_of_beta
#print axioms SmaleRate.Proofs.figure_gap_lower_of_beta
