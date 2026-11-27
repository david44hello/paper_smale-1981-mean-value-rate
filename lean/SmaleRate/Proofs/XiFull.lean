/-
SmaleRate — full polynomial extension and xi bound.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.ExteriorGeometry
import SmaleRate.Proofs.XiEstimate
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem branch_is_univalent (poly : ℂ[X]) (inverse : ℂ → ℂ)
    (hinverse : IsInverseBranch poly inverse) : IsUnivalentOn inverse (disk 1) := by
  refine ⟨hinverse.1, ?_⟩
  intro first hfirst second hsecond heq
  exact (hinverse.2.2 first hfirst).symm.trans
    ((congrArg poly.eval heq).trans (hinverse.2.2 second hsecond))

theorem normalized_critical_ne_zero (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical) : critical ≠ 0 := by
  intro heq
  have hnorm := hnormal.2.1
  rw [heq, hpoly.2.1, norm_zero] at hnorm
  norm_num at hnorm

theorem exterior_frontier_polynomial_norm (poly : ℂ[X]) (inverse : ℂ → ℂ)
    (hinverse : IsInverseBranch poly inverse) (height : ℝ) (hheight : height ∈ Ioo 0 1)
    (critical : ℂ) (hcritical : critical ≠ 0) :
    ∀ point ∈ frontier (exteriorImage inverse height critical),
      ‖poly.eval (inversion critical point)‖ = height := by
  have hunivalent := branch_is_univalent poly inverse hinverse
  have hgeometry := (inverse_jordan_domain_proved inverse hunivalent hinverse.2.1 height hheight).1
  intro point hpoint
  have hfrontier := invertedExterior_frontier_subset (inverseDomain inverse height)
    hgeometry.2.2.2.1 critical hcritical point hpoint
  rw [inverse_image_frontier inverse hunivalent height hheight] at hfrontier
  obtain ⟨source, hsource, heq⟩ := hfrontier
  rw [← heq, hinverse.2.2 source
    (smaller_closed_disk_subset height hheight (sphere_subset_closedBall hsource))]
  exact mem_sphere_zero_iff_norm.mp hsource

theorem xi_polynomial_holomorphic_extension_proved (degree : ℕ) (_hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) (critical : ℂ)
    (hnormal : NormalizedCriticalValues poly critical) (inverse : ℂ → ℂ)
    (hinverse : IsInverseBranch poly inverse) (height : ℝ) (hheight : height ∈ Ioo 0 1)
    (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func (disk 1) (exteriorImage inverse height critical))
    (hzero : func 0 = 0) :
    ∃ extension : ℂ → ℂ, DifferentiableOn ℂ extension (disk 1) ∧
      (∀ point ∈ disk 1, point ≠ 0 →
        extension point = point^degree * poly.eval (inversion critical (func point))) ∧
      ∀ point ∈ disk 1, ‖extension point‖ ≤ height := by
  have hcritical := normalized_critical_ne_zero degree poly hpoly critical hnormal
  have hunivalent := branch_is_univalent poly inverse hinverse
  have hgeometry := (inverse_jordan_domain_proved inverse hunivalent hinverse.2.1 height hheight).1
  have hbase : (0 : ℂ) ∈ inverseDomain inverse height := by
    exact ⟨0, by simp [disk, hheight.1], hinverse.2.1⟩
  obtain ⟨extension, hextension, hformula⟩ :=
    polynomial_pole_cancellation degree poly hpoly.1 critical hcritical func hfunc.1 hzero
  refine ⟨extension, hextension, hformula, ?_⟩
  apply polynomial_extension_norm_bound degree poly critical (exteriorImage inverse height critical)
    (invertedExterior_open _ hgeometry.2.2.2.1 critical hcritical)
    (invertedExterior_bounded _ hgeometry.1 hbase critical hcritical)
    func hfunc hzero extension hextension hformula height
  intro point hpoint
  exact (exterior_frontier_polynomial_norm poly inverse hinverse height hheight critical hcritical
    point hpoint).le

theorem xi_bound_proved (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsPd degree poly) (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical)
    (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func (disk 1) (exteriorImage inverse height critical))
    (hzero : func 0 = 0) (xi : ℂ) (hxi : xi ∈ disk 1) (hminusone : func xi = -1) :
    xi ≠ 0 ∧ ‖xi‖ ≤ height ^ (1 / (degree : ℝ)) := by
  obtain ⟨extension, _, hformula, hbound⟩ :=
    xi_polynomial_holomorphic_extension_proved degree hdegree poly hpoly critical hnormal
      inverse hinverse height hheight func hfunc hzero
  exact xi_bound_of_extension degree (by omega) poly critical hnormal.2.1 func hzero
    extension hformula height hheight.1.le hbound xi hxi hminusone

end SmaleRate.Proofs


