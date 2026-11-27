/-
SmaleRate — maximum modulus with boundary upper limits.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.PoleCancellation

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

/-- The boundary upper-limit version of the maximum modulus principle.
No value or continuity of the function on the frontier is assumed. -/
theorem norm_le_of_boundary_limsup (domain : Set ℂ) (hopen : IsOpen domain)
    (hbounded : Bornology.IsBounded domain) (func : ℂ → ℂ)
    (hdiff : DifferentiableOn ℂ func domain) (bound : ℝ)
    (hboundary : ∀ point ∈ frontier domain, ∀ upper : ℝ, bound < upper →
      ∀ᶠ nearby in 𝓝[domain] point, ‖func nearby‖ < upper) :
    ∀ point ∈ domain, ‖func point‖ ≤ bound := by
  intro point hpoint
  apply le_of_forall_gt_imp_ge_of_dense
  intro upper hupper
  let superlevel : Set ℂ := {nearby | nearby ∈ domain ∧ upper < ‖func nearby‖}
  have hsubset : superlevel ⊆ domain := fun _ h => h.1
  have hclosure : closure superlevel ⊆ domain := by
    intro nearby hnearby
    by_contra hout
    have hfrontier : nearby ∈ frontier domain := by
      rw [frontier, hopen.interior_eq]
      exact ⟨closure_mono hsubset hnearby, hout⟩
    have hlocal : ∀ᶠ other in 𝓝 nearby, other ∈ domain → ‖func other‖ < upper :=
      eventually_nhdsWithin_iff.mp (hboundary nearby hfrontier upper hupper)
    have hexclude : superlevelᶜ ∈ 𝓝 nearby := by
      filter_upwards [hlocal] with other hother
      exact fun hsuper => (hother hsuper.1).not_gt hsuper.2
    obtain ⟨other, hother_not, hother⟩ := mem_closure_iff_nhds.mp hnearby _ hexclude
    exact hother_not hother
  have hcont : ContinuousOn func (closure superlevel) := hdiff.continuousOn.mono hclosure
  have hfrontier_bound : ∀ nearby ∈ frontier superlevel, ‖func nearby‖ ≤ upper := by
    intro nearby hnearby
    by_contra hnot
    have hlarge : upper < ‖func nearby‖ := lt_of_not_ge hnot
    have hdomain : nearby ∈ domain := hclosure (frontier_subset_closure hnearby)
    have hlocal : superlevel ∈ 𝓝 nearby := by
      have hnorm : ContinuousAt (fun other => ‖func other‖) nearby :=
        (hdiff.differentiableAt (hopen.mem_nhds hdomain)).continuousAt.norm
      filter_upwards [hopen.mem_nhds hdomain, hnorm.eventually (Ioi_mem_nhds hlarge)]
        with other hother hnorm_other
      exact ⟨hother, hnorm_other⟩
    exact hnearby.2 (mem_interior_iff_mem_nhds.mpr hlocal)
  by_contra hnot
  have hsuper : point ∈ superlevel := ⟨hpoint, lt_of_not_ge hnot⟩
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le (hbounded.subset hsubset)
    ⟨hdiff.mono hsubset, hcont⟩ hfrontier_bound (subset_closure hsuper)
  exact hsuper.2.not_ge hle

theorem conformal_disk_inverse (domain : Set ℂ) (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func (disk 1) domain) :
    ∃ inverse : ℂ → ℂ, DifferentiableOn ℂ inverse domain ∧
      MapsTo inverse domain (disk 1) ∧
      (∀ point ∈ disk 1, inverse (func point) = point) ∧
      ∀ point ∈ domain, func (inverse point) = point := by
  classical
  have hzero : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hanalytic : AnalyticOnNhd ℂ func (disk 1) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hfunc.1.1
  have hmapopen : ∀ subset ⊆ disk 1, IsOpen subset → IsOpen (func '' subset) := by
    apply (hanalytic.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected).resolve_left
    rintro ⟨constant, hconstant⟩
    have hhalf : (1/2 : ℂ) ∈ disk 1 := by norm_num [disk, mem_ball_zero_iff]
    have heq := hfunc.1.2 hzero hhalf
      ((hconstant 0 hzero).trans (hconstant (1/2) hhalf).symm)
    norm_num at heq
  have hrestrict_open : IsOpenMap ((disk 1).domRestrict func) := by
    intro subset hsubset
    have hval_open : IsOpen ((Subtype.val : disk 1 → ℂ) '' subset) :=
      isOpen_ball.isOpenMap_subtype_val subset hsubset
    have hval_subset : (Subtype.val : disk 1 → ℂ) '' subset ⊆ disk 1 := by
      rintro member ⟨source, _, rfl⟩
      exact source.property
    change IsOpen ((fun member : disk 1 => func member.val) '' subset)
    simpa only [image_image, Function.comp_def] using hmapopen _ hval_subset hval_open
  have hbij : BijOn func (disk 1) domain := by
    refine ⟨?_, hfunc.1.2, ?_⟩
    · intro point hpoint
      rw [← hfunc.2]
      exact mem_image_of_mem func hpoint
    · intro point hpoint
      rw [← hfunc.2] at hpoint
      exact hpoint
  let equiv : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hbij.toPartialEquiv func (disk 1) domain)
      hfunc.1.1.continuousOn hrestrict_open isOpen_ball
  refine ⟨equiv.symm, ?_, (fun _ hp => equiv.map_target hp),
    (fun _ hp => equiv.left_inv hp), (fun _ hp => equiv.right_inv hp)⟩
  exact open_partial_inverse_differentiable equiv (convex_ball (0 : ℂ) 1).isPreconnected
    hanalytic 0 hzero (univalent_deriv_ne_zero func hfunc.1 0 hzero)

/-- Interior norm bound obtained in inverse coordinates. The two geometric hypotheses
are discharged by the exterior-domain construction; they are not background facts. -/
theorem polynomial_extension_norm_bound (degree : ℕ) (poly : ℂ[X])
    (critical : ℂ) (domain : Set ℂ) (hopen : IsOpen domain)
    (hbounded : Bornology.IsBounded domain) (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func (disk 1) domain) (hzero : func 0 = 0)
    (extension : ℂ → ℂ) (hextension : DifferentiableOn ℂ extension (disk 1))
    (hformula : ∀ point ∈ disk 1, point ≠ 0 →
      extension point = point^degree * poly.eval (inversion critical (func point)))
    (height : ℝ)
    (hboundary : ∀ point ∈ frontier domain, ‖poly.eval (inversion critical point)‖ ≤ height) :
    ∀ point ∈ disk 1, ‖extension point‖ ≤ height := by
  obtain ⟨inverse, hinverse, hmaps, hleft, hright⟩ := conformal_disk_inverse domain func hfunc
  have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hbase_domain : (0 : ℂ) ∈ domain := by
    rw [← hzero, ← hfunc.2]
    exact mem_image_of_mem func hbase
  have hdiff : DifferentiableOn ℂ (extension ∘ inverse) domain :=
    hextension.comp hinverse hmaps
  have hlimsup : ∀ point ∈ frontier domain, ∀ upper : ℝ, height < upper →
      ∀ᶠ nearby in 𝓝[domain] point, ‖(extension ∘ inverse) nearby‖ < upper := by
    intro point hpoint upper hupper
    have hpoint_ne : point ≠ 0 := by
      intro heq
      subst point
      exact hpoint.2 (by simpa only [hopen.interior_eq] using hbase_domain)
    have hinversion : ContinuousAt (inversion critical) point := by
      exact continuousAt_const.div continuousAt_id hpoint_ne
    have hpoly : ContinuousAt (fun nearby => ‖poly.eval (inversion critical nearby)‖) point :=
      (poly.continuous.continuousAt.comp hinversion).norm
    have hbound : ‖poly.eval (inversion critical point)‖ < upper :=
      (hboundary point hpoint).trans_lt hupper
    have hlocal : ∀ᶠ nearby in 𝓝 point,
        nearby ≠ 0 ∧ ‖poly.eval (inversion critical nearby)‖ < upper :=
      (eventually_ne_nhds hpoint_ne).and (hpoly.eventually (Iio_mem_nhds hbound))
    filter_upwards [hlocal.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
      nearby hnearby hnearby_domain
    have hinverse_ne : inverse nearby ≠ 0 := by
      intro heq
      have hvalue := hright nearby hnearby_domain
      rw [heq, hzero] at hvalue
      exact hnearby.1 hvalue.symm
    have hnorm : ‖inverse nearby‖ ≤ 1 :=
      (mem_ball_zero_iff.mp (hmaps hnearby_domain)).le
    change ‖extension (inverse nearby)‖ < upper
    rw [hformula _ (hmaps hnearby_domain) hinverse_ne, hright nearby hnearby_domain, norm_mul,
      norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hnorm)).trans_lt
      hnearby.2
  have hnorm := norm_le_of_boundary_limsup domain hopen hbounded _ hdiff height hlimsup
  intro point hpoint
  have himage : func point ∈ domain := by
    rw [← hfunc.2]
    exact mem_image_of_mem func hpoint
  simpa only [Function.comp_apply, hleft point hpoint] using hnorm (func point) himage

end SmaleRate.Proofs


