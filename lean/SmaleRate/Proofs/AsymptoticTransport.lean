/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.Elementary

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem weaker_asymptotic_difference_of_gap
    (hgap : Tendsto gap atTop (𝓝 (2*Real.pi^2))) :
    Tendsto (fun degree : ℕ => (target degree-bestBound degree)*ell degree) atTop (𝓝 (2*Real.pi^2-4)) := by
  have hconstant : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 (4 : ℝ)) := tendsto_const_nhds
  apply (hgap.sub hconstant).congr'
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with degree hdegree
  have hell : 0 < ell degree := lt_trans (by norm_num) (ell_gt_one degree hdegree)
  change gap degree - 4 = (target degree-bestBound degree)*ell degree
  unfold gap target
  field_simp [ne_of_gt hell]
  ring

theorem weaker_k_gap_liminf_of_best
    (hbest : ∀ degree : ℕ, 8 ≤ degree → Kd degree ≤ (bestBound degree : EReal))
    (hgap : Tendsto gap atTop (𝓝 (2*Real.pi^2))) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ degree : ℕ in atTop, Kd degree ≤ ((4 - (2*Real.pi^2-epsilon)/ell degree : ℝ) : EReal) := by
  have hnear : ∀ᶠ degree : ℕ in atTop, 2*Real.pi^2-epsilon < gap degree :=
    hgap.eventually (lt_mem_nhds (by linarith : 2*Real.pi^2-epsilon < 2*Real.pi^2))
  filter_upwards [eventually_ge_atTop (8 : ℕ), hnear] with degree hdegree hgap_bound
  have hell : 0 < ell degree := lt_trans (by norm_num) (ell_gt_one degree hdegree)
  have hdivide : (2*Real.pi^2-epsilon)/ell degree ≤ 4-bestBound degree := by
    apply (div_le_iff₀ hell).mpr
    exact hgap_bound.le
  have hreal : bestBound degree ≤ 4-(2*Real.pi^2-epsilon)/ell degree := by linarith
  exact (hbest degree hdegree).trans (EReal.coe_le_coe hreal)

end SmaleRate.Proofs
