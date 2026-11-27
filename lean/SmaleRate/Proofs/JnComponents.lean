/-
SmaleRate — actual polynomial lemniscate components and maximal univalent radius.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.AnalyticBackground
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem lemniscate_open (poly : ℂ[X]) (height : ℝ) : IsOpen (lemniscateComponent poly height) :=
  (isOpen_ball.preimage poly.continuous).connectedComponentIn

theorem lemniscate_zero (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (height : ℝ) (hheight : 0 < height) : (0 : ℂ) ∈ lemniscateComponent poly height := by
  apply mem_connectedComponentIn
  simp [hzero, disk, hheight]

theorem lemniscate_mono (poly : ℂ[X]) {first second : ℝ} (horder : first ≤ second) :
    lemniscateComponent poly first ⊆ lemniscateComponent poly second :=
  connectedComponentIn_mono 0 (preimage_mono (ball_subset_ball horder))

theorem radius_sup_positive (poly : ℂ[X]) (hne : (univalentRadii poly).Nonempty)
    (hbounded : BddAbove (univalentRadii poly)) : 0 < maxUnivalentRadius poly := by
  obtain ⟨height, hheight⟩ := hne
  exact hheight.1.trans_le (le_csSup hbounded hheight)

theorem lemniscate_at_radius_sup (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (hne : (univalentRadii poly).Nonempty) (hbounded : BddAbove (univalentRadii poly)) :
    lemniscateComponent poly (maxUnivalentRadius poly) =
      ⋃ height ∈ univalentRadii poly, lemniscateComponent poly height := by
  let combined : Set ℂ := ⋃ height ∈ univalentRadii poly, lemniscateComponent poly height
  have hopen : IsOpen combined := isOpen_iUnion (fun height => isOpen_iUnion
    (fun _ => lemniscate_open poly height))
  have hbase : (0 : ℂ) ∈ combined := by
    obtain ⟨height, hheight⟩ := hne
    exact mem_iUnion.mpr ⟨height, mem_iUnion.mpr ⟨hheight,
      lemniscate_zero poly hzero height hheight.1⟩⟩
  have hclosure : closure combined ∩ lemniscateComponent poly (maxUnivalentRadius poly) ⊆
      combined := by
    intro point hpoint
    have hvalue : ‖poly.eval point‖ < maxUnivalentRadius poly :=
      mem_ball_zero_iff.mp (connectedComponentIn_subset
        (poly.eval ⁻¹' disk (maxUnivalentRadius poly)) 0 hpoint.2)
    obtain ⟨height, hheight, hheight_value⟩ := exists_lt_of_lt_csSup hne hvalue
    let neighborhood := connectedComponentIn (poly.eval ⁻¹' disk height) point
    have hpoint_height : point ∈ poly.eval ⁻¹' disk height := mem_ball_zero_iff.mpr hheight_value
    have hpoint_neighborhood : point ∈ neighborhood := mem_connectedComponentIn hpoint_height
    have hneighborhood_open : IsOpen neighborhood :=
      (isOpen_ball.preimage poly.continuous).connectedComponentIn
    obtain ⟨nearby, hnearby_neighborhood, hnearby_combined⟩ :=
      mem_closure_iff_nhds.mp hpoint.1 _ (hneighborhood_open.mem_nhds hpoint_neighborhood)
    obtain ⟨other, hother, hnearby_other⟩ := mem_iUnion.mp hnearby_combined
      |>.imp (fun _ => mem_iUnion.mp)
    let upper := max height other
    have hupper : upper ∈ univalentRadii poly := by
      rcases le_total height other with horder | horder
      · simpa only [upper, max_eq_right horder] using hother
      · simpa only [upper, max_eq_left horder] using hheight
    have hunion_preconnected : IsPreconnected (neighborhood ∪ lemniscateComponent poly other) :=
      IsPreconnected.union nearby hnearby_neighborhood hnearby_other
        isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn
    have hunion_base : (0 : ℂ) ∈ neighborhood ∪ lemniscateComponent poly other :=
      Or.inr (lemniscate_zero poly hzero other hother.1)
    have hunion_subset : neighborhood ∪ lemniscateComponent poly other ⊆ poly.eval ⁻¹' disk upper := by
      intro member hmember
      rcases hmember with hmember | hmember
      · exact ball_subset_ball (le_max_left height other)
          (connectedComponentIn_subset (poly.eval ⁻¹' disk height) point hmember)
      · exact ball_subset_ball (le_max_right height other)
          (connectedComponentIn_subset (poly.eval ⁻¹' disk other) 0 hmember)
    have hin_upper := hunion_preconnected.subset_connectedComponentIn hunion_base hunion_subset
    exact mem_iUnion.mpr ⟨upper, mem_iUnion.mpr ⟨hupper,
      hin_upper (Or.inl hpoint_neighborhood)⟩⟩
  apply subset_antisymm
  · exact isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hopen
      ⟨0, lemniscate_zero poly hzero _ (radius_sup_positive poly hne hbounded), hbase⟩ hclosure
  · intro point hpoint
    obtain ⟨height, hpoint⟩ := mem_iUnion.mp hpoint
    obtain ⟨hheight, hpoint⟩ := mem_iUnion.mp hpoint
    exact lemniscate_mono poly (le_csSup hbounded hheight) hpoint

theorem radius_sup_mem (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (hne : (univalentRadii poly).Nonempty) (hbounded : BddAbove (univalentRadii poly)) :
    maxUnivalentRadius poly ∈ univalentRadii poly := by
  have hcomponent := lemniscate_at_radius_sup poly hzero hne hbounded
  refine ⟨radius_sup_positive poly hne hbounded, ⟨poly.differentiable.differentiableOn, ?_⟩, ?_⟩
  · intro first hfirst second hsecond heq
    rw [hcomponent] at hfirst hsecond
    obtain ⟨left, hfirst⟩ := mem_iUnion.mp hfirst
    obtain ⟨hleft, hfirst⟩ := mem_iUnion.mp hfirst
    obtain ⟨right, hsecond⟩ := mem_iUnion.mp hsecond
    obtain ⟨hright, hsecond⟩ := mem_iUnion.mp hsecond
    rcases le_total left right with horder | horder
    · exact hright.2.1.2 (lemniscate_mono poly horder hfirst) hsecond heq
    · exact hleft.2.1.2 hfirst (lemniscate_mono poly horder hsecond) heq
  · apply subset_antisymm
    · rintro value ⟨point, hpoint, rfl⟩
      exact connectedComponentIn_subset (poly.eval ⁻¹' disk (maxUnivalentRadius poly)) 0 hpoint
    · intro value hvalue
      have hnorm : ‖value‖ < maxUnivalentRadius poly := mem_ball_zero_iff.mp hvalue
      obtain ⟨height, hheight, hlarge⟩ := exists_lt_of_lt_csSup hne hnorm
      have hvalue_height : value ∈ disk height := mem_ball_zero_iff.mpr hlarge
      rw [← hheight.2.2] at hvalue_height
      obtain ⟨point, hpoint, heq⟩ := hvalue_height
      exact ⟨point, lemniscate_mono poly (le_csSup hbounded hheight) hpoint, heq⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.radius_sup_mem
#print axioms SmaleRate.Proofs.lemniscate_at_radius_sup
#print axioms SmaleRate.Proofs.radius_sup_mem
