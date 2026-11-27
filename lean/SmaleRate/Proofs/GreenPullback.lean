/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.GreenInversion
public import SmaleRate.Proofs.UnivalentDomain

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric InnerProductSpace
open scoped Topology

theorem green_superlevel_closure_subset (domain : Set ℂ) (hopen : IsOpen domain)
    (green : ℂ → ℝ)
    (hboundary : ∀ point ∈ frontier domain, Tendsto green (𝓝[domain] point) (𝓝 0))
    (level : ℝ) (hlevel : 0 < level) :
    closure {point : ℂ | point ∈ domain ∧ level ≤ green point} ⊆ domain := by
  intro point hpoint
  by_contra hout
  have hclosure : point ∈ closure domain :=
    closure_mono (fun _ hmember => hmember.1) hpoint
  have hfrontier : point ∈ frontier domain :=
    ⟨hclosure, by simpa only [hopen.interior_eq] using hout⟩
  have hsmall : ∀ᶠ member in 𝓝[domain] point, green member < level :=
    (tendsto_order.mp (hboundary point hfrontier)).2 level hlevel
  have hsmall_nhds := eventually_nhdsWithin_iff.mp hsmall
  obtain ⟨member, hmember, hbad⟩ :=
    (mem_closure_iff_nhds.mp hpoint) _ hsmall_nhds
  exact (not_lt_of_ge hbad.2) (hmember hbad.1)

theorem finite_green_boundary_comp (equiv : OpenPartialHomeomorph ℂ ℂ)
    (pole : ℂ) (hpole : pole ∈ equiv.source) (green : ℂ → ℝ)
    (hgreen : IsClassicalGreen equiv.target (equiv pole) green)
    (point : ℂ) (hpoint : point ∈ frontier equiv.source) :
    Tendsto (green ∘ (equiv : ℂ → ℂ)) (𝓝[equiv.source] point) (𝓝 0) := by
  have hpoint_outside : point ∉ equiv.source := by
    simpa only [equiv.open_source.interior_eq] using hpoint.2
  have hpoint_ne : point ≠ pole := fun heq => hpoint_outside (heq.symm ▸ hpole)
  apply tendsto_order.mpr
  constructor
  · intro lower hlower
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hpoint_ne] with member hmember hmember_ne
    have himage := equiv.map_source hmember
    have himage_ne : equiv member ≠ equiv pole :=
      fun heq => hmember_ne (equiv.injOn hmember hpole heq)
    exact hlower.trans (hgreen.2.2.2.1 _ ⟨himage, by simpa using himage_ne⟩)
  · intro upper hupper
    let bad : Set ℂ := {member | member ∈ equiv.target ∧ upper ≤ green member}
    have hbad_subset : closure bad ⊆ equiv.target :=
      green_superlevel_closure_subset equiv.target equiv.open_target green hgreen.2.2.2.2.2.1 upper hupper
    have hbad_bounded : Bornology.IsBounded bad :=
      hgreen.1.subset (fun _ hmember => hmember.1)
    have hcompact : IsCompact (equiv.symm '' closure bad) :=
      hbad_bounded.isCompact_closure.image_of_continuousOn
        (equiv.symm.continuousOn.mono hbad_subset)
    have hout : point ∉ equiv.symm '' closure bad := by
      rintro ⟨member, hmember, heq⟩
      exact hpoint_outside (heq ▸ equiv.map_target (hbad_subset hmember))
    have hlocal : (equiv.symm '' closure bad)ᶜ ∈ 𝓝 point :=
      hcompact.isClosed.isOpen_compl.mem_nhds hout
    filter_upwards [nhdsWithin_le_nhds hlocal, self_mem_nhdsWithin] with member houtside hmember
    by_contra hnot
    exact houtside ⟨equiv member, subset_closure ⟨equiv.map_source hmember, le_of_not_gt hnot⟩,
      equiv.left_inv hmember⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.green_superlevel_closure_subset
#print axioms SmaleRate.Proofs.green_superlevel_closure_subset
#check SmaleRate.Proofs.finite_green_boundary_comp
#print axioms SmaleRate.Proofs.finite_green_boundary_comp
