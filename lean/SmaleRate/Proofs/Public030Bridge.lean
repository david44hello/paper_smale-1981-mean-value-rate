/-
SmaleRate — exact bridge to the pinned Smale-equals-4 proof.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
Source: david44hello/paper_smale-mean-value-constant-equals-4, v2.70,
commit abf7f9d748ec78e71535814167f77ff185143dbd. Original Smale modules are byte-identical.
-/
module

public import Smale.P030.Contract
public import SmaleRate.Proofs.KdMonotone
public import SmaleRate.Proofs.PolynomialWitness

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Topology Polynomial

/-- The two retained derivative-one definitions have identical bodies. -/
theorem legacy_kd_eq_public030 (degree : ℕ) : Legacy009.Kd degree = Smale.Kd degree := by
  rfl

/-- The nonzero-derivative class and actual quotient were already normalized in kd_eq_legacy. -/
theorem kd_eq_public030 (degree : ℕ) : Kd degree = Smale.Kd degree :=
  (kd_eq_legacy degree).trans (legacy_kd_eq_public030 degree)

theorem kstar_eq_public030 : Kstar = Smale.Kstar := by
  simp only [Kstar, Smale.Kstar, kd_eq_public030]

theorem kstar_eq_four_public030 : Kstar = (4 : EReal) :=
  kstar_eq_public030.trans Smale.P030.kstar_eq_four

theorem kd_limit_and_sup_public030 : Tendsto Kd atTop (𝓝 (4 : EReal)) ∧ Kstar = 4 := by
  have hfunction : Kd = Smale.Kd := funext kd_eq_public030
  refine ⟨?_, kstar_eq_four_public030⟩
  rw [hfunction]
  exact Smale.P030.tendsto_Kd_four

theorem smale_bound_public030 (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ (4 : EReal) := by
  rw [kd_eq_public030]
  exact Smale.Koebe.Kd_le_four hdegree

theorem cfl_bound_public030 (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≤ ((4*((degree : ℝ)-1)/((degree : ℝ)+1) : ℝ) : EReal) := by
  rw [kd_eq_public030]
  exact Smale.Koebe.Kd_le_cfl hdegree

theorem conte_bound_public030 (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≤ (conte degree : EReal) := cfl_bound_public030 degree hdegree

theorem kd_lt_four_public030 (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree < (4 : EReal) := by
  rw [kd_eq_public030]
  exact Smale.P030.Kd_lt_four hdegree

theorem kd_finite_public030 (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≠ ⊥ ∧ Kd degree ≠ ⊤ := by
  refine ⟨kd_ne_bot degree hdegree, ne_of_lt ?_⟩
  exact (smale_bound_public030 degree hdegree).trans_lt (EReal.coe_lt_top (4 : ℝ))

theorem counterexample_exists_public030 : ∃ degree : ℕ, 2 ≤ degree ∧ (1 : EReal) < Kd degree := by
  have hlower : (1 : EReal) < Kstar := by rw [kstar_eq_four_public030]; norm_num
  obtain ⟨degree, hdegree⟩ := lt_iSup_iff.mp hlower
  exact ⟨degree.val, degree.property, hdegree⟩

theorem jatar_ng_lower_public030 : ((11018/10000 : ℝ) : EReal) < Kstar := by
  rw [kstar_eq_four_public030]
  change ((11018/10000 : ℝ) : EReal) < ((4 : ℝ) : EReal)
  exact EReal.coe_lt_coe_iff.mpr (by norm_num)

theorem koebe_quarter_omission_public030 (inverse : ℂ → ℂ)
    (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (point : ℂ) (homit : point ∉ inverse '' disk 1) : ‖deriv inverse 0‖/4 ≤ ‖point‖ := by
  have hbound := Smale.Koebe.koebe_quarter_general hinverse hzero
    (w := point) (fun source hsource heq => homit ⟨source, hsource, heq⟩)
  linarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.legacy_kd_eq_public030
#check SmaleRate.Proofs.kd_eq_public030
#check SmaleRate.Proofs.kstar_eq_public030
#check SmaleRate.Proofs.kstar_eq_four_public030
#check SmaleRate.Proofs.kd_limit_and_sup_public030
#check SmaleRate.Proofs.smale_bound_public030
#check SmaleRate.Proofs.cfl_bound_public030
#check SmaleRate.Proofs.conte_bound_public030
#check SmaleRate.Proofs.kd_lt_four_public030
#check SmaleRate.Proofs.kd_finite_public030
#check SmaleRate.Proofs.counterexample_exists_public030
#check SmaleRate.Proofs.jatar_ng_lower_public030
#check SmaleRate.Proofs.koebe_quarter_omission_public030
#print axioms Smale.P030.kstar_eq_four
#print axioms Smale.P030.tendsto_Kd_four
#print axioms Smale.Koebe.Kd_le_four
#print axioms Smale.Koebe.Kd_le_cfl
#print axioms SmaleRate.Proofs.legacy_kd_eq_public030
#print axioms SmaleRate.Proofs.kd_eq_public030
#print axioms SmaleRate.Proofs.kstar_eq_public030
#print axioms SmaleRate.Proofs.kstar_eq_four_public030
#print axioms SmaleRate.Proofs.kd_limit_and_sup_public030
#print axioms SmaleRate.Proofs.smale_bound_public030
#print axioms SmaleRate.Proofs.cfl_bound_public030
#print axioms SmaleRate.Proofs.conte_bound_public030
#print axioms SmaleRate.Proofs.kd_lt_four_public030
#print axioms SmaleRate.Proofs.kd_finite_public030
#print axioms SmaleRate.Proofs.counterexample_exists_public030
#print axioms SmaleRate.Proofs.jatar_ng_lower_public030
#print axioms SmaleRate.Proofs.koebe_quarter_omission_public030
