/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.YBoundLimits

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem ybound_fixed_y_limit_from_mu_limit
    (hlimit : Tendsto mu (𝓝[<] (1 : ℝ)) (𝓝 0))
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    Tendsto (fun degree : ℕ => yBound degree height) atTop (𝓝 (4 / height)) := by
  have hcast : Tendsto (fun degree : ℕ => (degree : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun degree : ℕ => 1 / (degree : ℝ)) atTop (𝓝 0) := by
    convert hcast.inv_tendsto_atTop using 1
    ext degree
    simp [one_div]
  have hconstant : Tendsto (fun _ : ℕ => height) atTop (𝓝 height) := tendsto_const_nhds
  have hpower : Tendsto (fun degree : ℕ => height ^ (1 / (degree : ℝ))) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using hconstant.rpow hinv (Or.inl hheight.1.ne')
  have hwithin : Tendsto (fun degree : ℕ => height ^ (1 / (degree : ℝ))) atTop (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hpower, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with degree hdegree
    exact (ypower_mem degree hdegree height hheight).2
  have hmu := hlimit.comp hwithin
  have hexp : Tendsto (fun degree : ℕ => Real.exp (-mu (height ^ (1 / (degree : ℝ))))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hmu.neg
  have hcoefficient : Tendsto (fun _ : ℕ => 4 / height) atTop (𝓝 (4 / height)) := tendsto_const_nhds
  convert hcoefficient.mul hexp using 1
  · ext degree
    rfl
  · simp

end SmaleRate.Proofs
