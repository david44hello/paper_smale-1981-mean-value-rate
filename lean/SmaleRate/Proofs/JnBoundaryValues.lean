/-
SmaleRate — boundary values and elementary normalized-polynomial facts.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.JnBoundary

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem lemniscate_frontier_norm (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (height : ℝ) (hheight : 0 < height) (point : ℂ)
    (hpoint : point ∈ frontier (lemniscateComponent poly height)) :
    ‖poly.eval point‖ = height := by
  have hle : ‖poly.eval point‖ ≤ height := by
    apply mem_closedBall_zero_iff.mp
    apply closure_minimal (t := poly.eval ⁻¹' closedBall 0 height)
      (fun member hmember => ball_subset_closedBall
        (connectedComponentIn_subset (poly.eval ⁻¹' disk height) 0 hmember))
      (isClosed_closedBall.preimage poly.continuous) hpoint.1
  apply le_antisymm hle
  by_contra hnot
  have hsmall : ‖poly.eval point‖ < height := lt_of_not_ge hnot
  let neighborhood := connectedComponentIn (poly.eval ⁻¹' disk height) point
  have hpoint_neighborhood : point ∈ neighborhood :=
    mem_connectedComponentIn (mem_ball_zero_iff.mpr hsmall)
  have hopen : IsOpen neighborhood :=
    (isOpen_ball.preimage poly.continuous).connectedComponentIn
  obtain ⟨nearby, hnearby_neighborhood, hnearby_component⟩ :=
    mem_closure_iff_nhds.mp hpoint.1 _ (hopen.mem_nhds hpoint_neighborhood)
  have hunion : IsPreconnected (lemniscateComponent poly height ∪ neighborhood) :=
    IsPreconnected.union nearby hnearby_component hnearby_neighborhood
      isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn
  have hsubset : lemniscateComponent poly height ∪ neighborhood ⊆ poly.eval ⁻¹' disk height := by
    intro member hmember
    rcases hmember with hmember | hmember
    · exact connectedComponentIn_subset (poly.eval ⁻¹' disk height) 0 hmember
    · exact connectedComponentIn_subset (poly.eval ⁻¹' disk height) point hmember
  have hmember := hunion.subset_connectedComponentIn
    (Or.inl (lemniscate_zero poly hzero height hheight)) hsubset (Or.inr hpoint_neighborhood)
  apply hpoint.2
  rwa [(lemniscate_open poly height).interior_eq]

theorem schlicht_leading_coefficient_pos (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) : 0 < ‖poly.leadingCoeff‖ := by
  apply norm_pos_iff.mpr
  apply leadingCoeff_ne_zero.mpr
  intro heq
  have hdeg := hpoly.1.1
  rw [heq, natDegree_zero] at hdeg
  omega

theorem schlicht_boundary_critical_witness (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) :
    ∃ point ∈ frontier (lemniscateComponent poly 1),
      point ∈ criticalPoints poly ∧ ‖poly.eval point‖ = 1 := by
  obtain ⟨point, hfrontier, hcritical⟩ := jatar_ng_boundary_critical_exists_proved degree hdegree poly hpoly
  exact ⟨point, hfrontier, hcritical,
    lemniscate_frontier_norm poly hpoly.1.2.1 1 (by norm_num) point hfrontier⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.lemniscate_frontier_norm
#check SmaleRate.Proofs.schlicht_boundary_critical_witness
#print axioms SmaleRate.Proofs.lemniscate_frontier_norm
#print axioms SmaleRate.Proofs.schlicht_leading_coefficient_pos
#print axioms SmaleRate.Proofs.schlicht_boundary_critical_witness
