/-
SmaleRate — exact open equivalences and nonzero derivatives on arbitrary domains.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.RiemannBridge

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem univalent_nonconstant_on_open (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hnonempty : domain.Nonempty) (hinjective : InjOn func domain) :
    ∃ first ∈ domain, ∃ second ∈ domain, func first ≠ func second := by
  obtain ⟨base, hbase⟩ := hnonempty
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hbase)
  have hsecond : base + ((radius/2 : ℝ) : ℂ) ∈ domain := by
    apply hball
    change dist (base + ((radius/2 : ℝ) : ℂ)) base < radius
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hradius)]
    linarith
  have hscalar : ((radius/2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (half_pos hradius))
  refine ⟨base, hbase, base + ((radius/2 : ℝ) : ℂ), hsecond, ?_⟩
  intro heq
  have hpoints := hinjective hbase hsecond heq
  have hsubtract := congrArg (fun member : ℂ => member - base) hpoints
  apply hscalar
  simpa only [sub_self, add_sub_cancel_left] using hsubtract.symm

theorem univalent_some_deriv_ne_zero (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) : ∃ base ∈ domain, deriv func base ≠ 0 := by
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    univalent_nonconstant_on_open func domain hopen hnonempty hfunc.2
  by_contra hnone
  push Not at hnone
  exact hne (hopen.is_const_of_deriv_eq_zero hconnected hfunc.1 hnone hfirst hsecond)

theorem univalent_domain_isOpenMap (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) : IsOpenMap (domain.domRestrict func) := by
  have hanalytic : AnalyticOnNhd ℂ func domain :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).mpr hfunc.1
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    univalent_nonconstant_on_open func domain hopen hnonempty hfunc.2
  have hmapopen : ∀ subset ⊆ domain, IsOpen subset → IsOpen (func '' subset) := by
    apply (hanalytic.is_constant_or_isOpen hconnected).resolve_left
    rintro ⟨constant, hconstant⟩
    exact hne ((hconstant first hfirst).trans (hconstant second hsecond).symm)
  intro subset hsubset
  have hval_open : IsOpen ((Subtype.val : domain → ℂ) '' subset) :=
    hopen.isOpenMap_subtype_val subset hsubset
  have hval_subset : (Subtype.val : domain → ℂ) '' subset ⊆ domain := by
    rintro member ⟨source, _, rfl⟩
    exact source.property
  change IsOpen ((fun member : domain => func member.val) '' subset)
  simpa only [image_image, Function.comp_def] using hmapopen _ hval_subset hval_open

/-- The supplied function is retained globally; source and target are exact, not just equivalent sets. -/
noncomputable def univalentOpenPartialHomeomorph (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) : OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hfunc.2.toPartialEquiv func domain)
    hfunc.1.continuousOn (univalent_domain_isOpenMap func domain hopen hconnected hnonempty hfunc) hopen

theorem univalentOpenPartialHomeomorph_source (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) :
    (univalentOpenPartialHomeomorph func domain hopen hconnected hnonempty hfunc).source = domain := rfl

theorem univalentOpenPartialHomeomorph_target (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) :
    (univalentOpenPartialHomeomorph func domain hopen hconnected hnonempty hfunc).target = func '' domain := rfl

theorem univalentOpenPartialHomeomorph_coe (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) :
    (univalentOpenPartialHomeomorph func domain hopen hconnected hnonempty hfunc : ℂ → ℂ) = func := rfl

theorem univalent_domain_inverse_differentiable (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) :
    DifferentiableOn ℂ (univalentOpenPartialHomeomorph func domain hopen hconnected hnonempty hfunc).symm
      (func '' domain) := by
  obtain ⟨base, hbase, hderivative⟩ :=
    univalent_some_deriv_ne_zero func domain hopen hconnected hnonempty hfunc
  have hanalytic : AnalyticOnNhd ℂ func domain :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).mpr hfunc.1
  exact open_partial_inverse_differentiable
    (univalentOpenPartialHomeomorph func domain hopen hconnected hnonempty hfunc)
    hconnected hanalytic base hbase hderivative

theorem univalent_domain_deriv_ne_zero (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) (point : ℂ) (hpoint : point ∈ domain) :
    deriv func point ≠ 0 := by
  let equiv := univalentOpenPartialHomeomorph func domain hopen hconnected hnonempty hfunc
  have hinverse_diff : DifferentiableOn ℂ equiv.symm equiv.target :=
    univalent_domain_inverse_differentiable func domain hopen hconnected hnonempty hfunc
  have htarget : equiv point ∈ equiv.target := equiv.map_source hpoint
  have hdiff_inv := hinverse_diff.differentiableAt (equiv.open_target.mem_nhds htarget)
  have hdiff_func := hfunc.1.differentiableAt (hopen.mem_nhds hpoint)
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

theorem univalent_domain_open_equivalence (func : ℂ → ℂ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hfunc : IsUnivalentOn func domain) :
    ∃ equiv : OpenPartialHomeomorph ℂ ℂ,
      equiv.source = domain ∧ equiv.target = func '' domain ∧ (equiv : ℂ → ℂ) = func ∧
      DifferentiableOn ℂ equiv.symm equiv.target ∧
      ∀ point ∈ domain, deriv func point ≠ 0 := by
  exact ⟨univalentOpenPartialHomeomorph func domain hopen hconnected hnonempty hfunc,
    rfl, rfl, rfl, univalent_domain_inverse_differentiable func domain hopen hconnected hnonempty hfunc,
    univalent_domain_deriv_ne_zero func domain hopen hconnected hnonempty hfunc⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.univalentOpenPartialHomeomorph_source
#check SmaleRate.Proofs.univalentOpenPartialHomeomorph_target
#check SmaleRate.Proofs.univalentOpenPartialHomeomorph_coe
#check SmaleRate.Proofs.univalent_domain_inverse_differentiable
#check SmaleRate.Proofs.univalent_domain_deriv_ne_zero
#check SmaleRate.Proofs.univalent_domain_open_equivalence
#print axioms SmaleRate.Proofs.univalent_nonconstant_on_open
#print axioms SmaleRate.Proofs.univalent_some_deriv_ne_zero
#print axioms SmaleRate.Proofs.univalent_domain_isOpenMap
#print axioms SmaleRate.Proofs.univalent_domain_inverse_differentiable
#print axioms SmaleRate.Proofs.univalent_domain_deriv_ne_zero
#print axioms SmaleRate.Proofs.univalent_domain_open_equivalence
