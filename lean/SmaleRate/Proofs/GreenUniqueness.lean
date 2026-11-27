/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.HarmonicMaximum

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric InnerProductSpace
open scoped Topology

theorem finite_green_unique (domain : Set ℂ) (hopen : IsOpen domain)
    (hconnected : IsPreconnected domain) (pole : ℂ) (first second : ℂ → ℝ)
    (hfirst : IsClassicalGreen domain pole first)
    (hsecond : IsClassicalGreen domain pole second) :
    ∀ point : ℂ, point ≠ pole → first point = second point := by
  classical
  obtain ⟨hbounded, hpole, hhfirst, _, ⟨regFirst, hrfirst, hefirst⟩,
    hbfirst, hzfirst⟩ := hfirst
  obtain ⟨_, _, hhsecond, _, ⟨regSecond, hrsecond, hesecond⟩,
    hbsecond, hzsecond⟩ := hsecond
  let regular : ℂ → ℝ := fun point => regFirst point - regSecond point
  let difference : ℂ → ℝ := fun point => first point - second point
  let patched : ℂ → ℝ := fun point => if point = pole then regular pole else difference point
  have hpatch_ne (point : ℂ) (hpoint : point ≠ pole) : patched point = difference point := by
    simp only [patched, if_neg hpoint]
  have hpatch_regular : patched =ᶠ[𝓝 pole] regular := by
    have he := eventually_nhdsWithin_iff.mp (hefirst.and hesecond)
    filter_upwards [he] with point hpoint
    by_cases heq : point = pole
    · subst point
      simp only [patched, if_pos rfl]
    · have hvalues := hpoint (by simpa using heq)
      rw [hpatch_ne point heq]
      dsimp [difference, regular]
      linarith [hvalues.1, hvalues.2]
  have hhpatch : HarmonicOnNhd patched domain := by
    intro point hpoint
    by_cases heq : point = pole
    · subst point
      exact (harmonicAt_congr_nhds hpatch_regular).mpr (hrfirst.sub hrsecond)
    · have hsame : patched =ᶠ[𝓝 point] difference := by
        filter_upwards [eventually_ne_nhds heq] with member hmember
        exact hpatch_ne member hmember
      exact (harmonicAt_congr_nhds hsame).mpr
        ((hhfirst point ⟨hpoint, by simpa using heq⟩).sub
          (hhsecond point ⟨hpoint, by simpa using heq⟩))
  have hboundary_ne (point : ℂ) (hpoint : point ∈ frontier domain) : point ≠ pole := by
    intro heq
    have hnot : point ∉ domain := by
      simpa only [hopen.interior_eq] using hpoint.2
    exact hnot (heq.symm ▸ hpole)
  have hboundary_zero (point : ℂ) (hpoint : point ∈ frontier domain) : patched point = 0 := by
    rw [hpatch_ne point (hboundary_ne point hpoint)]
    have hnot : point ∉ domain := by
      simpa only [hopen.interior_eq] using hpoint.2
    simp only [difference, hzfirst point hnot, hzsecond point hnot, sub_self]
  have hcontinuous : ContinuousOn patched (closure domain) := by
    intro point hpoint
    by_cases hinterior : point ∈ domain
    · exact (hhpatch point hinterior).1.continuousAt.continuousWithinAt
    · have hfrontier : point ∈ frontier domain :=
        ⟨hpoint, by simpa only [hopen.interior_eq] using hinterior⟩
      have hne := hboundary_ne point hfrontier
      have hinside : Tendsto patched (𝓝[domain] point) (𝓝 (0 : ℝ)) := by
        have hlimit := (hbfirst point hfrontier).sub (hbsecond point hfrontier)
        simp only [sub_zero] at hlimit
        apply hlimit.congr'
        filter_upwards [eventually_ne_nhdsWithin hne] with member hmember
        exact (hpatch_ne member hmember).symm
      have houtside : Tendsto patched (𝓝[domainᶜ] point) (𝓝 (0 : ℝ)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with member hmember
        have hmemberne : member ≠ pole := by
          intro heq
          exact hmember (heq.symm ▸ hpole)
        rw [hpatch_ne member hmemberne]
        simp only [difference, hzfirst member hmember, hzsecond member hmember, sub_self]
      have hlimit : Tendsto patched (𝓝 point) (𝓝 (0 : ℝ)) := by
        have hboth := hinside.sup houtside
        simpa only [← nhdsWithin_union, union_compl_self, nhdsWithin_univ] using hboth
      rw [← hboundary_zero point hfrontier] at hlimit
      exact hlimit.mono_left nhdsWithin_le_nhds
  have hzero := harmonic_zero_of_boundary patched domain hopen hconnected ⟨pole, hpole⟩
    hbounded hhpatch hcontinuous hboundary_zero
  intro point hpoint
  by_cases hmem : point ∈ domain
  · have hvalue := hzero (subset_closure hmem)
    rw [hpatch_ne point hpoint] at hvalue
    exact sub_eq_zero.mp hvalue
  · rw [hzfirst point hmem, hzsecond point hmem]

end SmaleRate.Proofs

#check SmaleRate.Proofs.finite_green_unique
#print axioms SmaleRate.Proofs.finite_green_unique
