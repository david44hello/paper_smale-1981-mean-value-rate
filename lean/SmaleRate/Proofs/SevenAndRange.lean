/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.BoundOrders
public import SmaleRate.Proofs.CraneNumbers

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

theorem degree_seven_target_upper : target 7 < (19445/10000 : ℝ) := by
  have hsmall : (25753/10000 : ℝ) ≤ Real.exp (94599/100000) := by
    have h := exp_lower_eight (94599/100000) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  have he : (271828/100000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlog7 : Real.log (7 : ℝ) < (194599/100000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    calc
      (7 : ℝ) < (271828/100000 : ℝ)*(25753/10000) := by norm_num
      _ ≤ Real.exp 1*Real.exp (94599/100000) := mul_le_mul he hsmall (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp (194599/100000) := by rw [← Real.exp_add]; congr 1; norm_num
  apply target_lt_from_log_upper 7 (194599/100000) (19445/10000)
  · unfold ell; norm_num only [Nat.cast_ofNat]; exact Real.log_pos (by norm_num)
  · simpa only [ell, Nat.cast_ofNat] using hlog7
  · norm_num
  · norm_num

theorem fujikawa_seven_scalar :
    fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧
      (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 := by
  have hpower : ((4 : ℝ)^(-1/6 : ℝ))^3 = 1/2 := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [earlier_log_four]
    rw [show (3 : ℝ)*(2*Real.log 2* -(1/6)) = -Real.log 2 by ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hqnonneg : 0 ≤ (4 : ℝ)^(-1/6 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hqlo : (79368/100000 : ℝ) < (4 : ℝ)^(-1/6 : ℝ) := by
    by_contra hnot
    have horder : (4 : ℝ)^(-1/6 : ℝ) ≤ (79368/100000 : ℝ) := le_of_not_gt hnot
    have hpow : ((4 : ℝ)^(-1/6 : ℝ))^3 ≤ (79368/100000 : ℝ)^3 := by gcongr
    rw [hpower] at hpow
    norm_num at hpow
  have hqhi : (4 : ℝ)^(-1/6 : ℝ) < (79372/100000 : ℝ) := by
    by_contra hnot
    have horder : (79372/100000 : ℝ) ≤ (4 : ℝ)^(-1/6 : ℝ) := le_of_not_gt hnot
    have hpow : (79372/100000 : ℝ)^3 ≤ ((4 : ℝ)^(-1/6 : ℝ))^3 := by gcongr
    rw [hpower] at hpow
    norm_num at hpow
  have hfuj : fujikawa 7 = (1/2 : ℝ)+(5/2)*(4 : ℝ)^(-1/6 : ℝ) := by norm_num [fujikawa]; ring
  have hbeardon := beardon_as_q 7 (by norm_num)
  norm_num at hbeardon
  have hlow : (24842/10000 : ℝ) < fujikawa 7 := by rw [hfuj]; linarith
  have hhigh : fujikawa 7 < (24843/10000 : ℝ) := by rw [hfuj]; linarith
  refine ⟨?_, ?_, ?_, hlow, hhigh⟩
  · norm_num [conte]; linarith
  · rw [hbeardon]; linarith
  · unfold dubinin
    rw [hbeardon]
    norm_num
    linarith

theorem range_seven_best_improvement_of_bounds
    (hlower : (20190/10000 : ℝ) < bestBound 7) (hKd : Kd 7 ≤ (bestBound 7 : EReal)) :
    target 7 < bestBound 7 ∧ Kd 7 ≤ (bestBound 7 : EReal) ∧
      fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧
      (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 := by
  exact ⟨by linarith [degree_seven_target_upper], hKd, fujikawa_seven_scalar⟩

theorem range_eight_gap_upper_of_lower (hlower : (20549/10000 : ℝ) < bestBound 8) :
    gap 8 < (4045/1000 : ℝ) := by
  have hepos : 0 < ell 8 := by linarith [ell_gt_one 8 (by norm_num)]
  have hscaled := mul_lt_mul_of_pos_right (sub_lt_sub_left hlower 4) hepos
  have hlog8 : ell 8 = 3*Real.log 2 := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num, Real.log_pow]; norm_num
  unfold gap
  rw [hlog8] at hscaled ⊢
  linarith [Real.log_two_lt_d9]

theorem range_eight_gap_lower_of_upper (hupper : bestBound 8 < (20550/10000 : ℝ)) :
    (4 : ℝ) < gap 8 := by
  have hepos : 0 < ell 8 := by linarith [ell_gt_one 8 (by norm_num)]
  have hscaled := mul_lt_mul_of_pos_right (sub_lt_sub_left hupper 4) hepos
  have hlog8 : ell 8 = 3*Real.log 2 := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num, Real.log_pow]; norm_num
  unfold gap
  rw [hlog8] at hscaled ⊢
  linarith [Real.log_two_gt_d9]

end SmaleRate.Proofs

#check SmaleRate.Proofs.degree_seven_target_upper
#print axioms SmaleRate.Proofs.degree_seven_target_upper
#check SmaleRate.Proofs.fujikawa_seven_scalar
#print axioms SmaleRate.Proofs.fujikawa_seven_scalar
#check SmaleRate.Proofs.range_seven_best_improvement_of_bounds
#print axioms SmaleRate.Proofs.range_seven_best_improvement_of_bounds
#check SmaleRate.Proofs.range_eight_gap_upper_of_lower
#print axioms SmaleRate.Proofs.range_eight_gap_upper_of_lower
