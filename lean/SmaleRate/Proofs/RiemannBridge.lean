/-
SmaleRate — disk-to-domain Riemann bridge.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Vendor.RiemannMap
import SmaleRate.Defs.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem open_partial_inverse_differentiable
    (equiv : OpenPartialHomeomorph ℂ ℂ) (hconnected : IsPreconnected equiv.source)
    (hanalytic : AnalyticOnNhd ℂ equiv equiv.source)
    (base : ℂ) (hbase : base ∈ equiv.source) (hderivative : deriv equiv base ≠ 0) :
    DifferentiableOn ℂ equiv.symm equiv.target := by
  have hderiv_analytic : AnalyticOnNhd ℂ (deriv equiv) equiv.source :=
    hanalytic.deriv_of_isOpen equiv.open_source
  have hpunctured : ∀ point ∈ equiv.source, ∀ᶠ other in 𝓝[≠] point, deriv equiv other ≠ 0 := by
    intro point hpoint
    apply (hderiv_analytic point hpoint).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    intro hzero
    have hzero_all := hderiv_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconnected hpoint hzero
    exact hderivative (hzero_all hbase)
  intro point hpoint
  have hinverse_cont : ContinuousAt equiv.symm point := equiv.symm.continuousAt hpoint
  have hpreimage : equiv.symm point ∈ equiv.source := equiv.map_target hpoint
  have haway : ∀ᶠ other in 𝓝[≠] point, DifferentiableAt ℂ equiv.symm other := by
    have hne_source := eventually_nhdsWithin_iff.mp (hpunctured (equiv.symm point) hpreimage)
    have hpullback := hinverse_cont.tendsto.eventually hne_source
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [hpullback, equiv.open_target.mem_nhds hpoint] with other hother htarget hdistinct
    have hpreimage_ne : equiv.symm other ≠ equiv.symm point := by
      intro heq
      apply hdistinct
      calc
        other = equiv (equiv.symm other) := (equiv.right_inv htarget).symm
        _ = equiv (equiv.symm point) := congrArg equiv heq
        _ = point := equiv.right_inv hpoint
    have hderiv_ne : deriv equiv (equiv.symm other) ≠ 0 := hother hpreimage_ne
    exact (HasDerivAt.of_local_left_inverse (equiv.symm.continuousAt htarget)
      (hanalytic _ (equiv.map_target htarget)).differentiableAt.hasDerivAt hderiv_ne
      (equiv.eventually_right_inverse htarget)).differentiableAt
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    haway hinverse_cont).differentiableAt.differentiableWithinAt

theorem riemann_map_disk_to_domain (domain : Set ℂ) (hopen : IsOpen domain)
    (hsimply : IsSimplyConnected domain) (hproper : domain ≠ univ)
    (base : ℂ) (hbase : base ∈ domain) :
    ∃ func : ℂ → ℂ, IsConformalOnto func (disk 1) domain ∧ func 0 = base := by
  classical
  obtain ⟨forward, hdiff, hbij, hzero, hderivative⟩ :=
    Complex.exists_bijOn_unitBall_map_eq_zero_and_deriv_ne_zero hopen hsimply hproper hbase
  have hconnected : IsPreconnected domain := hsimply.isPathConnected.isConnected.isPreconnected
  have hanalytic : AnalyticOnNhd ℂ forward domain :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).mpr hdiff
  have hforward_open : ∀ subset ⊆ domain, IsOpen subset → IsOpen (forward '' subset) := by
    apply (hanalytic.is_constant_or_isOpen hconnected).resolve_left
    rintro ⟨constant, hconstant⟩
    have heq : EqOn forward (Function.const ℂ constant) domain := hconstant
    have hderiv_eq := (heq.eventuallyEq_of_mem (hopen.mem_nhds hbase)).deriv_eq
    have hconstant_deriv : deriv (Function.const ℂ constant) base = 0 := deriv_const base constant
    exact hderivative (hderiv_eq.trans hconstant_deriv)
  have hopen_restrict : IsOpenMap (domain.domRestrict forward) := by
    intro subset hsubset
    have hval_open : IsOpen ((Subtype.val : domain → ℂ) '' subset) :=
      hopen.isOpenMap_subtype_val subset hsubset
    have hval_subset : (Subtype.val : domain → ℂ) '' subset ⊆ domain := by
      rintro point ⟨member, _, rfl⟩
      exact member.property
    change IsOpen ((fun member : domain => forward member.val) '' subset)
    simpa only [image_image, Function.comp_def] using hforward_open _ hval_subset hval_open
  let equiv : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hbij.toPartialEquiv forward domain (disk 1))
      hdiff.continuousOn hopen_restrict hopen
  have hinverse_diff : DifferentiableOn ℂ equiv.symm (disk 1) :=
    open_partial_inverse_differentiable equiv hconnected hanalytic base hbase hderivative
  refine ⟨equiv.symm, ⟨⟨hinverse_diff, equiv.symm.injOn⟩, equiv.symm.image_source_eq_target⟩, ?_⟩
  change equiv.symm 0 = base
  rw [← hzero]
  exact equiv.left_inv hbase

end SmaleRate.Proofs


