/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.Basic

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Polynomial

theorem polynomial_class_nonempty (degree : ℕ) (hdegree : 2 ≤ degree) :
    ∃ poly : ℂ[X], IsPd degree poly := by
  refine ⟨X^degree + X, ?_, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp only [natDegree_X, natDegree_X_pow]
      omega
  · simp [show degree ≠ 0 by omega]
  · simp [derivative_add, derivative_pow, show degree - 1 ≠ 0 by omega]

theorem kd_ne_bot (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≠ ⊥ := by
  obtain ⟨poly, hpoly⟩ := polynomial_class_nonempty degree hdegree
  have hle : (S poly : EReal) ≤ Kd degree := le_iSup_of_le ⟨poly, hpoly⟩ le_rfl
  intro heq
  rw [heq] at hle
  simpa using hle

end SmaleRate.Proofs
