/-
SmaleRate — existence and finiteness of the genuine maximal univalent radius.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.JnComponents
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem inverse_image_eq_lemniscate (poly : ℂ[X]) (height : ℝ) (hheight : 0 < height)
    (inverse : ℂ → ℂ) (hcontinuous : ContinuousOn inverse (disk height))
    (hzero : inverse 0 = 0) (hright : ∀ point ∈ disk height, poly.eval (inverse point) = point)
    (hopen : IsOpen (inverse '' disk height)) :
    inverse '' disk height = lemniscateComponent poly height := by
  have hbase : (0 : ℂ) ∈ disk height := by simp [disk, hheight]
  have hpoly_zero : poly.eval 0 = 0 := by simpa only [hzero] using hright 0 hbase
  have himage_base : (0 : ℂ) ∈ inverse '' disk height := ⟨0, hbase, hzero⟩
  have himage_subset : inverse '' disk height ⊆ poly.eval ⁻¹' disk height := by
    rintro point ⟨source, hsource, rfl⟩
    change poly.eval (inverse source) ∈ disk height
    rw [hright source hsource]
    exact hsource
  apply subset_antisymm
  · have hpreconnected := (convex_ball (0 : ℂ) height).isPreconnected.image inverse hcontinuous
    exact hpreconnected.subset_connectedComponentIn himage_base himage_subset
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hopen
      ⟨0, lemniscate_zero poly hpoly_zero height hheight, himage_base⟩
    intro point hpoint
    have hvalue : poly.eval point ∈ disk height :=
      connectedComponentIn_subset (poly.eval ⁻¹' disk height) 0 hpoint.2
    have hpoly_cont : ContinuousAt (fun member : ℂ => poly.eval member) point :=
      poly.continuous.continuousAt
    have hcont : ContinuousAt (fun member : ℂ => inverse (poly.eval member)) point :=
      (hcontinuous.continuousAt (isOpen_ball.mem_nhds hvalue)).comp
        (f := fun member : ℂ => poly.eval member) hpoly_cont
    haveI : NeBot (𝓝[inverse '' disk height] point) :=
      mem_closure_iff_nhdsWithin_neBot.mp hpoint.1
    have heq : (fun member : ℂ => inverse (poly.eval member)) =ᶠ[𝓝[inverse '' disk height] point]
        (fun member : ℂ => member) := by
      filter_upwards [self_mem_nhdsWithin] with member hmember
      obtain ⟨source, hsource, rfl⟩ := hmember
      rw [hright source hsource]
    have hidentity : Tendsto (fun member : ℂ => member) (𝓝[inverse '' disk height] point) (𝓝 point) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hvalue_eq : inverse (poly.eval point) = point := tendsto_nhds_unique
      (hcont.tendsto.mono_left nhdsWithin_le_nhds) (hidentity.congr' heq.symm)
    exact ⟨poly.eval point, hvalue, hvalue_eq⟩

theorem univalentRadii_nonempty (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (univalentRadii poly).Nonempty := by
  classical
  have hstrict := (poly.hasStrictDerivAt 0).hasStrictFDerivAt_equiv hpoly.2.2
  let equiv := hstrict.toOpenPartialHomeomorph poly.eval
  have hsource : (0 : ℂ) ∈ equiv.source := hstrict.mem_toOpenPartialHomeomorph_source
  have htarget : (0 : ℂ) ∈ equiv.target := by
    simpa only [hpoly.2.1] using hstrict.image_mem_toOpenPartialHomeomorph_target
  obtain ⟨height, hheight, hball⟩ := Metric.mem_nhds_iff.mp (equiv.open_target.mem_nhds htarget)
  have hzero : equiv.symm 0 = 0 := by
    calc
      equiv.symm 0 = equiv.symm (poly.eval 0) := by rw [hpoly.2.1]
      _ = 0 := equiv.left_inv hsource
  have hright : ∀ point ∈ disk height, poly.eval (equiv.symm point) = point :=
    fun point hp => equiv.right_inv (hball hp)
  have hopen : IsOpen (equiv.symm '' disk height) :=
    equiv.symm.isOpen_image_of_subset_source isOpen_ball hball
  have himage := inverse_image_eq_lemniscate poly height hheight equiv.symm
    (equiv.symm.continuousOn.mono hball) hzero hright hopen
  refine ⟨height, hheight, ⟨poly.differentiable.differentiableOn, ?_⟩, ?_⟩
  · intro first hfirst second hsecond heq
    rw [← himage] at hfirst hsecond
    obtain ⟨left, hleft, rfl⟩ := hfirst
    obtain ⟨right, hright_mem, rfl⟩ := hsecond
    exact equiv.injOn (equiv.map_target (hball hleft))
      (equiv.map_target (hball hright_mem)) heq
  · apply subset_antisymm
    · rintro point ⟨source, hsource, rfl⟩
      exact connectedComponentIn_subset (poly.eval ⁻¹' disk height) 0 hsource
    · intro point hpoint
      refine ⟨equiv.symm point, ?_, hright point hpoint⟩
      rw [← himage]
      exact mem_image_of_mem equiv.symm hpoint

theorem polynomial_has_other_zero (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) : ∃ point : ℂ, point ≠ 0 ∧ poly.eval point = 0 := by
  have hdegree_div : 0 < (divX poly).degree := by
    rw [← natDegree_pos_iff_degree_pos, natDegree_divX_eq_natDegree_tsub_one, hpoly.1]
    omega
  obtain ⟨point, hpoint⟩ := Complex.exists_root hdegree_div
  have hdiv_zero : (divX poly).eval 0 ≠ 0 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_divX, coeff_derivative,
      Nat.zero_add, Nat.cast_one, Nat.cast_zero, zero_add, one_mul, mul_one] using hpoly.2.2
  refine ⟨point, ?_, ?_⟩
  · rintro rfl
    exact hdiv_zero hpoint.eq_zero
  · have heq := congrArg (eval point) (divX_mul_X_add poly)
    rw [eval_add, eval_mul, eval_X, eval_C, coeff_zero_eq_eval_zero, hpoly.2.1,
      hpoint.eq_zero, zero_mul, zero_add] at heq
    exact heq.symm

theorem univalentRadii_bddAbove (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) : BddAbove (univalentRadii poly) := by
  obtain ⟨point, hpoint_ne, hpoint_zero⟩ := polynomial_has_other_zero degree hdegree poly hpoly
  have hsegment_compact : IsCompact (segment ℝ (0 : ℂ) point) := by
    rw [segment_eq_image]
    exact (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).image (by fun_prop)
  have hcompact : IsCompact (poly.eval '' segment ℝ (0 : ℂ) point) :=
    hsegment_compact.image poly.continuous
  obtain ⟨bound, hbound, hnorm⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨bound, ?_⟩
  intro height hheight
  by_contra hnot
  have hlarge : bound < height := lt_of_not_ge hnot
  have hsegment : segment ℝ (0 : ℂ) point ⊆ poly.eval ⁻¹' disk height := by
    intro member hmember
    have hle := hnorm (poly.eval member) (mem_image_of_mem poly.eval hmember)
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hle hlarge)
  have hcomponent := (convex_segment (0 : ℂ) point).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ (0 : ℂ) point) hsegment
  have heq := hheight.2.1.2 (hcomponent (left_mem_segment ℝ (0 : ℂ) point))
    (hcomponent (right_mem_segment ℝ (0 : ℂ) point)) (hpoly.2.1.trans hpoint_zero.symm)
  exact hpoint_ne heq.symm

theorem jn_radius_well_defined_proved (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (univalentRadii poly).Nonempty ∧ BddAbove (univalentRadii poly) ∧
      0 < maxUnivalentRadius poly ∧ maxUnivalentRadius poly ∈ univalentRadii poly := by
  have hnonempty := univalentRadii_nonempty degree poly hpoly
  have hbounded := univalentRadii_bddAbove degree hdegree poly hpoly
  exact ⟨hnonempty, hbounded, radius_sup_positive poly hnonempty hbounded,
    radius_sup_mem poly hpoly.2.1 hnonempty hbounded⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.jn_radius_well_defined_proved
#print axioms SmaleRate.Proofs.inverse_image_eq_lemniscate
#print axioms SmaleRate.Proofs.univalentRadii_nonempty
#print axioms SmaleRate.Proofs.univalentRadii_bddAbove
#print axioms SmaleRate.Proofs.jn_radius_well_defined_proved
