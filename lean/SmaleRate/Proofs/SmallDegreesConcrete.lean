/-
SmaleRate — exact degree-two and degree-three constants.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.BinomialWitness
public import SmaleRate.Proofs.SmallDegreeUpper

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs

theorem kd_two_eq : Kd 2 = ((1 / 2 : ℝ) : EReal) := by
  apply le_antisymm kd_two_upper
  have hbound := kd_binomial_lower 2 (by omega)
  norm_num at hbound ⊢
  exact hbound

theorem kd_three_eq : Kd 3 = ((2 / 3 : ℝ) : EReal) := by
  apply le_antisymm kd_three_upper
  have hbound := kd_binomial_lower 3 (by omega)
  norm_num at hbound ⊢
  exact hbound

theorem small_degrees_two_three (degree : ℕ) (hlower : 2 ≤ degree) (hupper : degree ≤ 3) :
    Kd degree = ((((degree : ℝ) - 1) / degree : ℝ) : EReal) := by
  interval_cases degree
  · convert kd_two_eq using 1 <;> norm_num
  · convert kd_three_eq using 1 <;> norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.kd_two_eq
#check SmaleRate.Proofs.kd_three_eq
#check SmaleRate.Proofs.small_degrees_two_three
#print axioms SmaleRate.Proofs.kd_two_eq
#print axioms SmaleRate.Proofs.kd_three_eq
#print axioms SmaleRate.Proofs.small_degrees_two_three
