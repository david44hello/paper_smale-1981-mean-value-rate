/-
SmaleRate — strict printed tail inequality identified in independent review.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.PrintedCases

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set

theorem range_tail_strict_from_dlmf
    (hdlmf : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
        mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
    (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8) (length : ℝ) (hlength : 1 ≤ length) :
    (235/100 : ℝ) < Real.exp (6/7) ∧ Real.exp (6/7) < beta degree length := by
  have hdegree_two : 2 ≤ degree := by rcases hdegree with rfl | rfl <;> omega
  have hlength_pos : 0 < length := by linarith
  have hexponent : (6/7 : ℝ) ≤ (1 - 1/(degree : ℝ)) * length := by
    rcases hdegree with rfl | rfl <;> norm_num <;> linarith
  exact ⟨(range_tail_proved hdlmf degree hdegree length hlength).1,
    (Real.exp_le_exp.mpr hexponent).trans_lt
      (beta_gt_simple_exponential hdlmf degree hdegree_two length hlength_pos)⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.range_tail_strict_from_dlmf
#print axioms SmaleRate.Proofs.range_tail_strict_from_dlmf
