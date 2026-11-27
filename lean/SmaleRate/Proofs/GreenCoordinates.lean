/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.GreenUniqueness
import SmaleRate.Proofs.GreenExistence

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric
open scoped Topology

theorem disk_equivalence_given_jordan (hjordan : Background.JordanCurveFact)
    (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain)
    (pole : ℂ) (hpole : pole ∈ domain) :
    ∃ equiv : OpenPartialHomeomorph ℂ ℂ, equiv.source = domain ∧
      equiv.target = disk 1 ∧ equiv pole = 0 ∧
      AnalyticOnNhd ℂ (equiv : ℂ → ℂ) domain ∧ deriv (equiv : ℂ → ℂ) pole ≠ 0 := by
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
  exact ⟨equiv, rfl, rfl, hzero, hanalytic, hderivative⟩

theorem green_eq_disk_coordinate (equiv : OpenPartialHomeomorph ℂ ℂ)
    (hunit : equiv.target = disk 1) (hconnected : IsPreconnected equiv.source)
    (pole : ℂ) (hpole : pole ∈ equiv.source) (hzero : equiv pole = 0)
    (hanalytic : AnalyticOnNhd ℂ (equiv : ℂ → ℂ) equiv.source)
    (hderivative : deriv (equiv : ℂ → ℂ) pole ≠ 0)
    (green : ℂ → ℝ) (hgreen : IsClassicalGreen equiv.source pole green)
    (point : ℂ) (hpoint : point ∈ equiv.source) (hne : point ≠ pole) :
    green point = -Real.log ‖equiv point‖ := by
  have hconstructed := green_from_disk_equivalence equiv hunit hgreen.1 pole hpole
    hzero hanalytic hderivative
  have heq := finite_green_unique equiv.source equiv.open_source hconnected pole green
    (conformalDiskGreen equiv) hgreen hconstructed point hne
  simpa only [conformalDiskGreen, if_pos hpoint] using heq

end SmaleRate.Proofs

#check SmaleRate.Proofs.disk_equivalence_given_jordan
#print axioms SmaleRate.Proofs.disk_equivalence_given_jordan
#check SmaleRate.Proofs.green_eq_disk_coordinate
#print axioms SmaleRate.Proofs.green_eq_disk_coordinate
