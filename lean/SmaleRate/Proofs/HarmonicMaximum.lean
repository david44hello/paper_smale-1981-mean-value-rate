/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.GreenFromDisk

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric InnerProductSpace
open scoped Topology

theorem harmonic_local_max_constant (func : ℂ → ℝ) (point : ℂ)
    (hharmonic : HarmonicAt func point) (hmax : IsLocalMax func point) :
    ∀ᶠ member : ℂ in 𝓝 point, func member = func point := by
  have hnear : ∀ᶠ member : ℂ in 𝓝 point,
      HarmonicAt func member ∧ func member ≤ func point := hharmonic.eventually.and hmax
  obtain ⟨radius, hradius, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  have hbase : point ∈ ball point radius := mem_ball_self hradius
  obtain ⟨analytic, hanalytic, hreal⟩ :=
    (show HarmonicOnNhd func (ball point radius) from fun member hmember => (hball member hmember).1).exists_analyticOnNhd_ball_re_eq
  have hrepr : ∀ member ∈ ball point radius, (analytic member).re = func member :=
    fun member hmember => hreal hmember
  have hdiff : ∀ᶠ member : ℂ in 𝓝 point,
      DifferentiableAt ℂ (fun member : ℂ => Complex.exp (analytic member)) member := by
    filter_upwards [isOpen_ball.mem_nhds hbase] with member hmember
    exact Complex.differentiable_exp.differentiableAt.comp member (hanalytic member hmember).differentiableAt
  have hnormmax : IsLocalMax (norm ∘ (fun member : ℂ => Complex.exp (analytic member))) point := by
    filter_upwards [isOpen_ball.mem_nhds hbase] with member hmember
    simp only [Function.comp_def, Complex.norm_exp, hrepr member hmember, hrepr point hbase]
    exact Real.exp_le_exp.mpr (hball member hmember).2
  have hconstant := Complex.norm_eventually_eq_of_isLocalMax hdiff hnormmax
  filter_upwards [hconstant, isOpen_ball.mem_nhds hbase] with member hmember hballmember
  rw [Complex.norm_exp, Complex.norm_exp, hrepr member hballmember, hrepr point hbase] at hmember
  exact Real.exp_injective hmember

theorem harmonic_constant_of_max (func : ℂ → ℝ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain)
    (hharmonic : HarmonicOnNhd func domain) (point : ℂ) (hpoint : point ∈ domain)
    (hmax : IsMaxOn func domain point) : EqOn func (fun _ : ℂ => func point) domain := by
  have hlocal : IsLocalMax func point := by
    filter_upwards [hopen.mem_nhds hpoint] with member hmember
    exact hmax hmember
  have hanalytic : AnalyticOnNhd ℝ func domain :=
    fun member hmember => HarmonicAt.analyticAt (hharmonic member hmember)
  exact hanalytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconnected hpoint
    (harmonic_local_max_constant func point (hharmonic point hpoint) hlocal)

theorem harmonic_le_zero_of_boundary (func : ℂ → ℝ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hbounded : Bornology.IsBounded domain) (hharmonic : HarmonicOnNhd func domain)
    (hcontinuous : ContinuousOn func (closure domain))
    (hboundary : ∀ point ∈ frontier domain, func point ≤ 0) :
    ∀ point ∈ closure domain, func point ≤ 0 := by
  have hproper : domain ≠ univ := by
    intro heq
    rw [heq] at hbounded
    exact NormedSpace.unbounded_univ ℂ ℂ hbounded
  obtain ⟨boundary, hboundary_mem⟩ := nonempty_frontier_iff.mpr ⟨hnonempty, hproper⟩
  obtain ⟨base, hbase, hmax⟩ := hbounded.isCompact_closure.exists_isMaxOn
    hnonempty.closure hcontinuous
  have hbase_bound : func base ≤ 0 := by
    by_cases hinterior : base ∈ domain
    · have hconstant := harmonic_constant_of_max func domain hopen hconnected hharmonic base hinterior
        (hmax.of_subset subset_closure)
      have hclosure : EqOn func (fun _ : ℂ => func base) (closure domain) :=
        hconstant.of_subset_closure hcontinuous continuousOn_const subset_closure Subset.rfl
      have hvalue : func boundary = func base := hclosure hboundary_mem.1
      linarith [hboundary boundary hboundary_mem]
    · exact hboundary base ⟨hbase, by simpa only [hopen.interior_eq] using hinterior⟩
  intro point hpoint
  exact (hmax hpoint).trans hbase_bound

theorem harmonic_zero_of_boundary (func : ℂ → ℝ) (domain : Set ℂ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain) (hnonempty : domain.Nonempty)
    (hbounded : Bornology.IsBounded domain) (hharmonic : HarmonicOnNhd func domain)
    (hcontinuous : ContinuousOn func (closure domain))
    (hboundary : ∀ point ∈ frontier domain, func point = 0) :
    EqOn func (fun _ : ℂ => (0 : ℝ)) (closure domain) := by
  have hupper := harmonic_le_zero_of_boundary func domain hopen hconnected hnonempty hbounded
    hharmonic hcontinuous (fun point hpoint => (hboundary point hpoint).le)
  have hlower := harmonic_le_zero_of_boundary (-func) domain hopen hconnected hnonempty hbounded
    hharmonic.neg hcontinuous.neg (fun point hpoint => by simp [hboundary point hpoint])
  intro point hpoint
  have hu := hupper point hpoint
  have hl := hlower point hpoint
  change -func point ≤ 0 at hl
  linarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.harmonic_local_max_constant
#print axioms SmaleRate.Proofs.harmonic_local_max_constant
#check SmaleRate.Proofs.harmonic_constant_of_max
#print axioms SmaleRate.Proofs.harmonic_constant_of_max
#check SmaleRate.Proofs.harmonic_zero_of_boundary
#print axioms SmaleRate.Proofs.harmonic_zero_of_boundary
