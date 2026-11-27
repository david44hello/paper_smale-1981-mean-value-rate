/-
SmaleRate — inversion geometry of the exterior domain.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.InverseGeometry
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem inversion_involutive (critical : ℂ) (hcritical : critical ≠ 0) :
    Function.Involutive (inversion critical) := by
  intro point
  simp [inversion, hcritical]

theorem inversion_ne_zero (critical : ℂ) (hcritical : critical ≠ 0)
    (point : ℂ) (hpoint : point ≠ 0) : inversion critical point ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr hcritical) hpoint

def inversionPartialHomeomorph (critical : ℂ) (hcritical : critical ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ where
  toFun := inversion critical
  invFun := inversion critical
  source := {0}ᶜ
  target := {0}ᶜ
  map_source' := fun point hpoint => inversion_ne_zero critical hcritical point hpoint
  map_target' := fun point hpoint => inversion_ne_zero critical hcritical point hpoint
  left_inv' := fun point _ => inversion_involutive critical hcritical point
  right_inv' := fun point _ => inversion_involutive critical hcritical point
  continuousOn_toFun := by
    intro point hpoint
    exact (continuousAt_const.div continuousAt_id hpoint).continuousWithinAt
  continuousOn_invFun := by
    intro point hpoint
    exact (continuousAt_const.div continuousAt_id hpoint).continuousWithinAt
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl

def invertedExterior (domain : Set ℂ) (critical : ℂ) : Set ℂ :=
  {0} ∪ inversion critical '' (closure domain)ᶜ

theorem mem_invertedExterior_iff (domain : Set ℂ) (critical : ℂ) (hcritical : critical ≠ 0)
    (point : ℂ) (hpoint : point ≠ 0) :
    point ∈ invertedExterior domain critical ↔ inversion critical point ∉ closure domain := by
  constructor
  · rintro (hzero | ⟨other, hother, heq⟩)
    · exact (hpoint hzero).elim
    · rw [← heq, inversion_involutive critical hcritical]
      exact hother
  · intro hnot
    exact Or.inr ⟨inversion critical point, hnot, inversion_involutive critical hcritical point⟩

theorem invertedExterior_zero_nhds (domain : Set ℂ) (hbounded : Bornology.IsBounded domain)
    (critical : ℂ) (hcritical : critical ≠ 0) : invertedExterior domain critical ∈ 𝓝 0 := by
  obtain ⟨radius, hradius, hnorm⟩ := hbounded.closure.exists_pos_norm_le
  have hcritical_norm : 0 < ‖critical‖ := norm_pos_iff.mpr hcritical
  apply mem_of_superset (ball_mem_nhds (0 : ℂ) (div_pos hcritical_norm hradius))
  intro point hpoint
  by_cases hzero : point = 0
  · exact Or.inl hzero
  · apply (mem_invertedExterior_iff domain critical hcritical point hzero).mpr
    intro hclosure
    have hnorm_point := hnorm _ hclosure
    rw [inversion, norm_div, norm_neg] at hnorm_point
    have hpoint_norm : 0 < ‖point‖ := norm_pos_iff.mpr hzero
    have hsmall := mem_ball_zero_iff.mp hpoint
    have hprod := (lt_div_iff₀ hradius).mp hsmall
    have hprod' := (div_le_iff₀ hpoint_norm).mp hnorm_point
    nlinarith

theorem invertedExterior_open (domain : Set ℂ) (hbounded : Bornology.IsBounded domain)
    (critical : ℂ) (hcritical : critical ≠ 0) : IsOpen (invertedExterior domain critical) := by
  rw [isOpen_iff_mem_nhds]
  intro point hpoint
  by_cases hzero : point = 0
  · subst point
    exact invertedExterior_zero_nhds domain hbounded critical hcritical
  · have hout := (mem_invertedExterior_iff domain critical hcritical point hzero).mp hpoint
    have hcont : ContinuousAt (inversion critical) point :=
      continuousAt_const.div continuousAt_id hzero
    have hlocal := hcont.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hout)
    apply mem_of_superset hlocal
    intro nearby hnearby
    by_cases hnearby_zero : nearby = 0
    · exact Or.inl hnearby_zero
    · exact (mem_invertedExterior_iff domain critical hcritical nearby hnearby_zero).mpr hnearby

theorem invertedExterior_bounded (domain : Set ℂ) (hopen : IsOpen domain)
    (hzero : (0 : ℂ) ∈ domain) (critical : ℂ) (hcritical : critical ≠ 0) :
    Bornology.IsBounded (invertedExterior domain critical) := by
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖critical‖ / radius, ?_⟩
  intro point hpoint
  by_cases hpoint_zero : point = 0
  · simp [hpoint_zero, (div_pos (norm_pos_iff.mpr hcritical) hradius).le]
  · have hout := (mem_invertedExterior_iff domain critical hcritical point hpoint_zero).mp hpoint
    have hlarge : radius ≤ ‖inversion critical point‖ := by
      by_contra hnot
      exact hout (subset_closure (hball (mem_ball_zero_iff.mpr (lt_of_not_ge hnot))))
    rw [inversion, norm_div, norm_neg] at hlarge
    apply (le_div_iff₀ hradius).mpr
    have hprod := (le_div_iff₀ (norm_pos_iff.mpr hpoint_zero)).mp hlarge
    nlinarith

theorem invertedExterior_frontier_subset (domain : Set ℂ)
    (hbounded : Bornology.IsBounded domain) (critical : ℂ) (hcritical : critical ≠ 0) :
    ∀ point ∈ frontier (invertedExterior domain critical),
      inversion critical point ∈ frontier domain := by
  let equiv := inversionPartialHomeomorph critical hcritical
  have himage : equiv.IsImage (closure domain)ᶜ (invertedExterior domain critical) := by
    intro point hpoint
    change inversion critical point ∈ invertedExterior domain critical ↔ point ∉ closure domain
    rw [mem_invertedExterior_iff domain critical hcritical _
      (inversion_ne_zero critical hcritical point hpoint), inversion_involutive critical hcritical]
  intro point hpoint
  have hpoint_ne : point ≠ 0 := by
    intro heq
    subst point
    exact hpoint.2 (mem_interior_iff_mem_nhds.mpr
      (invertedExterior_zero_nhds domain hbounded critical hcritical))
  have hsource : point ∈ equiv.target := hpoint_ne
  have hfrontier := himage.frontier.symm_apply_mem_iff hsource
  have hmember : inversion critical point ∈ frontier (closure domain) := by
    have hmember' := hfrontier.mpr hpoint
    change inversion critical point ∈ frontier ((closure domain)ᶜ) at hmember'
    simpa only [frontier_compl] using hmember'
  exact frontier_closure_subset hmember

end SmaleRate.Proofs


