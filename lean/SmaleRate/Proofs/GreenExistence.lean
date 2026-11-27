/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.GreenFromDisk
import SmaleRate.Proofs.RiemannBridge
import SmaleRate.Defs.BackgroundFacts

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric
open scoped Topology

theorem finite_green_given_jordan (hjordan : Background.JordanCurveFact)
    (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain)
    (pole : ℂ) (hpole : pole ∈ domain) :
    ∃ green : ℂ → ℝ, IsClassicalGreen domain pole green := by
  classical
  have hproper : domain ≠ univ := by
    intro heq
    have hbounded := hdomain.2.2.2.1
    rw [heq] at hbounded
    exact NormedSpace.unbounded_univ ℂ ℂ hbounded
  obtain ⟨forward, hdiff, hbij, hzero, hderivative⟩ :=
    Complex.exists_bijOn_unitBall_map_eq_zero_and_deriv_ne_zero
      hdomain.1 (hjordan domain hdomain).1 hproper hpole
  have hanalytic : AnalyticOnNhd ℂ forward domain :=
    (Complex.analyticOnNhd_iff_differentiableOn hdomain.1).mpr hdiff
  have hforward_open : ∀ subset ⊆ domain, IsOpen subset → IsOpen (forward '' subset) := by
    apply (hanalytic.is_constant_or_isOpen hdomain.2.1).resolve_left
    rintro ⟨constant, hconstant⟩
    have heq : EqOn forward (Function.const ℂ constant) domain := hconstant
    have hderiv_eq := (heq.eventuallyEq_of_mem (hdomain.1.mem_nhds hpole)).deriv_eq
    exact hderivative (hderiv_eq.trans (deriv_const pole constant))
  have hopen_restrict : IsOpenMap (domain.domRestrict forward) := by
    intro subset hsubset
    have hval_open : IsOpen ((Subtype.val : domain → ℂ) '' subset) :=
      hdomain.1.isOpenMap_subtype_val subset hsubset
    have hval_subset : (Subtype.val : domain → ℂ) '' subset ⊆ domain := by
      rintro point ⟨member, _, rfl⟩
      exact member.property
    change IsOpen ((fun member : domain => forward member.val) '' subset)
    simpa only [image_image, Function.comp_def] using hforward_open _ hval_subset hval_open
  let equiv : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hbij.toPartialEquiv forward domain (disk 1))
      hdiff.continuousOn hopen_restrict hdomain.1
  exact ⟨conformalDiskGreen equiv, green_from_disk_equivalence equiv rfl hdomain.2.2.2.1
    pole hpole hzero hanalytic hderivative⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.finite_green_given_jordan
#print axioms SmaleRate.Proofs.finite_green_given_jordan
