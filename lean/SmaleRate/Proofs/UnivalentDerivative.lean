/-
SmaleRate — nonzero derivatives of univalent disk maps.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.RiemannBridge
public import SmaleRate.Proofs.InverseGeometry

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem univalent_deriv_ne_zero (func : ℂ → ℂ) (hfunc : IsUnivalentOn func (disk 1))
    (point : ℂ) (hpoint : point ∈ disk 1) : deriv func point ≠ 0 := by
  classical
  have hzero : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hhalf : (1/2 : ℂ) ∈ disk 1 := by norm_num [disk, mem_ball_zero_iff]
  have hconnected : IsPreconnected (disk (1 : ℝ)) := (convex_ball (0 : ℂ) 1).isPreconnected
  have hanalytic : AnalyticOnNhd ℂ func (disk 1) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hfunc.1
  have hsome : ∃ base ∈ disk 1, deriv func base ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero hconnected hfunc.1 hnone hzero hhalf
    have hsame := hfunc.2 hzero hhalf hconst
    norm_num at hsame
  obtain ⟨base, hbase, hbase_deriv⟩ := hsome
  have hmapopen : ∀ subset ⊆ disk 1, IsOpen subset → IsOpen (func '' subset) := by
    apply (hanalytic.is_constant_or_isOpen hconnected).resolve_left
    rintro ⟨constant, hconstant⟩
    have hsame := hfunc.2 hzero hhalf ((hconstant 0 hzero).trans (hconstant (1/2) hhalf).symm)
    norm_num at hsame
  have hrestrict_open : IsOpenMap ((disk 1).domRestrict func) := by
    intro subset hsubset
    have hval_open : IsOpen ((Subtype.val : disk 1 → ℂ) '' subset) :=
      isOpen_ball.isOpenMap_subtype_val subset hsubset
    have hval_subset : (Subtype.val : disk 1 → ℂ) '' subset ⊆ disk 1 := by
      rintro member ⟨source, _, rfl⟩
      exact source.property
    change IsOpen ((fun member : disk 1 => func member.val) '' subset)
    simpa only [image_image, Function.comp_def] using hmapopen _ hval_subset hval_open
  let equiv : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hfunc.2.toPartialEquiv func (disk 1))
      hfunc.1.continuousOn hrestrict_open isOpen_ball
  have hinverse_diff : DifferentiableOn ℂ equiv.symm equiv.target :=
    open_partial_inverse_differentiable equiv hconnected hanalytic base hbase hbase_deriv
  have htarget : equiv point ∈ equiv.target := equiv.map_source hpoint
  have hdiff_inv := hinverse_diff.differentiableAt (equiv.open_target.mem_nhds htarget)
  have hdiff_func := hfunc.1.differentiableAt (isOpen_ball.mem_nhds hpoint)
  have hcompose := hdiff_inv.hasDerivAt.comp point hdiff_func.hasDerivAt
  have heventual : equiv.symm ∘ (equiv : ℂ → ℂ) =ᶠ[𝓝 point] (fun member : ℂ => member) :=
    equiv.eventually_left_inverse hpoint
  have hidentity : HasDerivAt (fun member : ℂ => member)
      (deriv equiv.symm (func point) * deriv func point) point :=
    hcompose.congr_of_eventuallyEq heventual.symm
  have hproduct : deriv equiv.symm (func point) * deriv func point = 1 :=
    hidentity.unique (hasDerivAt_id point)
  intro hzero_deriv
  simp [hzero_deriv] at hproduct

theorem inverse_analytic_boundary_proved (inverse : ℂ → ℂ)
    (hinverse : IsUnivalentOn inverse (disk 1)) (_hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    AnalyticOnNhd ℂ inverse (sphere 0 height) ∧
    (∀ point ∈ sphere 0 height, deriv inverse point ≠ 0) ∧
    frontier (inverseDomain inverse height) = inverse '' sphere 0 height := by
  have hsubset : sphere (0 : ℂ) height ⊆ disk 1 :=
    sphere_subset_closedBall.trans (smaller_closed_disk_subset height hheight)
  refine ⟨((Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hinverse.1).mono hsubset,
    fun point hpoint => univalent_deriv_ne_zero inverse hinverse point (hsubset hpoint),
    inverse_image_frontier inverse hinverse height hheight⟩

end SmaleRate.Proofs


