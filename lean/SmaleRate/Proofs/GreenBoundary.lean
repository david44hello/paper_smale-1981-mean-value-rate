/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.DiskGreen

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric
open scoped Topology

theorem disk_equivalence_norm_boundary (equiv : OpenPartialHomeomorph ℂ ℂ)
    (hunit : equiv.target = disk 1) (point : ℂ) (hpoint : point ∈ frontier equiv.source) :
    Tendsto (fun member : ℂ => ‖equiv member‖) (𝓝[equiv.source] point) (𝓝 1) := by
  have hpoint_outside : point ∉ equiv.source := by
    simpa only [equiv.open_source.interior_eq] using hpoint.2
  apply tendsto_order.mpr
  constructor
  · intro lower hlower
    by_cases hnegative : lower < 0
    · exact Eventually.of_forall (fun member => hnegative.trans_le (norm_nonneg _))
    have hnonneg : 0 ≤ lower := le_of_not_gt hnegative
    have hclosed_subset : closedBall (0 : ℂ) lower ⊆ equiv.target := by
      rw [hunit]
      intro member hmember
      exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hmember).trans_lt hlower)
    have hcompact : IsCompact (equiv.symm '' closedBall (0 : ℂ) lower) :=
      (isCompact_closedBall (0 : ℂ) lower).image_of_continuousOn
        (equiv.symm.continuousOn.mono hclosed_subset)
    have hnot : point ∉ equiv.symm '' closedBall (0 : ℂ) lower := by
      rintro ⟨source, hsource, heq⟩
      exact hpoint_outside (heq ▸ equiv.map_target (hclosed_subset hsource))
    have hneighborhood : (equiv.symm '' closedBall (0 : ℂ) lower)ᶜ ∈ 𝓝 point :=
      hcompact.isClosed.isOpen_compl.mem_nhds hnot
    have hwithin : ∀ᶠ member : ℂ in 𝓝[equiv.source] point,
        member ∉ equiv.symm '' closedBall (0 : ℂ) lower :=
      nhdsWithin_le_nhds hneighborhood
    filter_upwards [hwithin, self_mem_nhdsWithin] with member houtside hmember
    by_contra hnotlt
    exact houtside ⟨equiv member, mem_closedBall_zero_iff.mpr (le_of_not_gt hnotlt),
      equiv.left_inv hmember⟩
  · intro upper hupper
    filter_upwards [self_mem_nhdsWithin] with member hmember
    have hmem := equiv.map_source hmember
    rw [hunit] at hmem
    exact (mem_ball_zero_iff.mp hmem).trans hupper

end SmaleRate.Proofs

#check SmaleRate.Proofs.disk_equivalence_norm_boundary
#print axioms SmaleRate.Proofs.disk_equivalence_norm_boundary
