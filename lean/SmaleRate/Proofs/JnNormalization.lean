/-
SmaleRate — concrete Jatar-Ng normalization witness.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.JnRadius
public import SmaleRate.Proofs.InverseBranch

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem branch_conformal_on_lemniscate (poly : ℂ[X]) (inverse : ℂ → ℂ)
    (hinverse : IsInverseBranch poly inverse) :
    IsConformalOnto poly.eval (lemniscateComponent poly 1) (disk 1) := by
  have hunivalent := inverse_univalent poly inverse hinverse
  have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hhalf : (1/2 : ℂ) ∈ disk 1 := by norm_num [disk, mem_ball_zero_iff]
  have hanalytic : AnalyticOnNhd ℂ inverse (disk 1) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hinverse.1
  have hopen : IsOpen (inverse '' disk 1) := by
    rcases hanalytic.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with
      ⟨constant, hconstant⟩ | hopen
    · have heq := hunivalent.2 hbase hhalf
        ((hconstant 0 hbase).trans (hconstant (1/2) hhalf).symm)
      norm_num at heq
    · exact hopen (disk 1) subset_rfl isOpen_ball
  have himage := inverse_image_eq_lemniscate poly 1 (by norm_num) inverse hinverse.1.continuousOn
    hinverse.2.1 hinverse.2.2 hopen
  refine ⟨⟨poly.differentiable.differentiableOn, ?_⟩, ?_⟩
  · intro first hfirst second hsecond heq
    rw [← himage] at hfirst hsecond
    obtain ⟨left, hleft, rfl⟩ := hfirst
    obtain ⟨right, hright, rfl⟩ := hsecond
    have hsame : left = right := (hinverse.2.2 left hleft).symm.trans
      (heq.trans (hinverse.2.2 right hright))
    exact congrArg inverse hsame
  · apply subset_antisymm
    · rintro point ⟨source, hsource, rfl⟩
      exact connectedComponentIn_subset (poly.eval ⁻¹' disk 1) 0 hsource
    · intro point hpoint
      refine ⟨inverse point, ?_, hinverse.2.2 point hpoint⟩
      rw [← himage]
      exact mem_image_of_mem inverse hpoint

theorem jn_normalization_witness_proved :
    IsSchlichtNormalized 2 (X - C (1/4 : ℂ) * X^2) := by
  let poly : ℂ[X] := X - C (1/4 : ℂ) * X^2
  have hderivative : ∀ point : ℂ, poly.derivative.eval point = 1 - point/2 := by
    intro point
    dsimp [poly]
    simp <;> ring_nf <;> simp
  have hpoly : IsPd 2 poly := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [poly]
      compute_degree!
    · simp [poly]
    · rw [hderivative]
      norm_num
  have hcritical : ∀ point ∈ criticalPoints poly, point = 2 := by
    intro point hpoint
    change poly.derivative.eval point = 0 at hpoint
    rw [hderivative] at hpoint
    linear_combination -2 * hpoint
  have hnormal : NormalizedCriticalValues poly 2 := by
    refine ⟨?_, ?_, ?_⟩
    · change poly.derivative.eval 2 = 0
      rw [hderivative]
      norm_num
    · norm_num [poly]
    · intro point hpoint
      rw [hcritical point hpoint]
      norm_num [poly]
  obtain ⟨inverse, hinverse⟩ := inverse_branch_exists_proved 2 (by norm_num) poly hpoly 2 hnormal
  have hone : (1 : ℝ) ∈ univalentRadii poly :=
    ⟨by norm_num, branch_conformal_on_lemniscate poly inverse hinverse⟩
  have hupper : ∀ height ∈ univalentRadii poly, height ≤ 1 := by
    intro height hheight
    by_contra hnot
    have hlarge : (1 : ℝ) < height := lt_of_not_ge hnot
    let path : ℝ → ℂ := fun param => (4 : ℂ) * param
    have hpath_cont : Continuous path := by fun_prop
    have hpath_zero : (0 : ℂ) ∈ path '' Icc (0 : ℝ) 1 := ⟨0, by simp, by simp [path]⟩
    have hpath_four : (4 : ℂ) ∈ path '' Icc (0 : ℝ) 1 := ⟨1, by simp, by simp [path]⟩
    have hpath_subset : path '' Icc (0 : ℝ) 1 ⊆ poly.eval ⁻¹' disk height := by
      rintro point ⟨param, hparam, rfl⟩
      have hvalue : poly.eval (path param) = ((4*param - 4*param^2 : ℝ) : ℂ) := by
        simp [poly, path]
        <;> push_cast
        <;> ring
      have hnonneg : 0 ≤ 4*param - 4*param^2 := by
        nlinarith [mul_nonneg hparam.1 (sub_nonneg.mpr hparam.2)]
      have hle : 4*param - 4*param^2 ≤ 1 := by nlinarith [sq_nonneg (2*param-1)]
      change poly.eval (path param) ∈ ball 0 height
      rw [mem_ball_zero_iff, hvalue, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hle.trans_lt hlarge
    have hpreconnected : IsPreconnected (path '' Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image path hpath_cont.continuousOn
    have hcomponent := hpreconnected.subset_connectedComponentIn hpath_zero hpath_subset
    have heq := hheight.2.1.2 (hcomponent hpath_zero) (hcomponent hpath_four)
      (by norm_num [poly])
    norm_num at heq
  have hsup : maxUnivalentRadius poly = 1 := by
    exact le_antisymm (csSup_le ⟨1, hone⟩ hupper) (le_csSup ⟨1, hupper⟩ hone)
  exact ⟨hpoly, by rw [hderivative]; norm_num, hsup⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.jn_normalization_witness_proved
#print axioms SmaleRate.Proofs.branch_conformal_on_lemniscate
#print axioms SmaleRate.Proofs.jn_normalization_witness_proved
