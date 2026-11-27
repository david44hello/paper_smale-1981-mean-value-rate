/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.MuLimits

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem ypower_mem (degree : ℕ) (hdegree : 2 ≤ degree) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    height ^ (1 / (degree : ℝ)) ∈ Ioo 0 1 := by
  have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (show 0 < degree by omega)
  exact ⟨Real.rpow_pos_of_pos hheight.1 _, Real.rpow_lt_one hheight.1.le hheight.2 (one_div_pos.mpr hdpos)⟩

theorem ybound_gt_rpow_from_log_upper
    (hupper : ∀ modulus ∈ Ioo 0 1, mu modulus < Real.log (4 / modulus))
    (degree : ℕ) (hdegree : 2 ≤ degree) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    height ^ ((1 / (degree : ℝ)) - 1) < yBound degree height := by
  have hmem := ypower_mem degree hdegree height hheight
  have hexp : height ^ (1 / (degree : ℝ)) / 4 < Real.exp (-mu (height ^ (1 / (degree : ℝ)))) := by
    have hcompare := Real.exp_lt_exp.mpr (neg_lt_neg (hupper _ hmem))
    rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num : (0 : ℝ) < 4) hmem.1)] at hcompare
    simpa only [inv_div] using hcompare
  rw [Real.rpow_sub_one hheight.1.ne', yBound]
  calc
    height ^ (1 / (degree : ℝ)) / height =
        (4 / height) * (height ^ (1 / (degree : ℝ)) / 4) := by ring
    _ < _ := mul_lt_mul_of_pos_left hexp (div_pos (by norm_num) hheight.1)

theorem ybound_at_zero_from_log_upper
    (hupper : ∀ modulus ∈ Ioo 0 1, mu modulus < Real.log (4 / modulus))
    (degree : ℕ) (hdegree : 2 ≤ degree) : Tendsto (yBound degree) (𝓝[>] (0 : ℝ)) atTop := by
  have hdcast : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hnegative : 1 / (degree : ℝ) - 1 < 0 := by
    have hfrac : 1 / (degree : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _ (tendsto_rpow_neg_nhdsGT_zero hnegative)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with height hheight
  exact (ybound_gt_rpow_from_log_upper hupper degree hdegree height hheight).le

theorem ybound_at_one_from_mu_limit
    (hlimit : Tendsto mu (𝓝[<] (1 : ℝ)) (𝓝 0))
    (degree : ℕ) (hdegree : 2 ≤ degree) : Tendsto (yBound degree) (𝓝[<] (1 : ℝ)) (𝓝 4) := by
  have hheight : Tendsto (fun height : ℝ => height) (𝓝[<] (1 : ℝ)) (𝓝 1) := nhdsWithin_le_nhds
  have hpower : Tendsto (fun height : ℝ => height ^ (1 / (degree : ℝ))) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa only [Real.one_rpow] using hheight.rpow_const (Or.inl one_ne_zero)
  have hpower_within : Tendsto (fun height : ℝ => height ^ (1 / (degree : ℝ)))
      (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hpower, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with height hheight
    exact (ypower_mem degree hdegree height hheight).2
  have hmu := hlimit.comp hpower_within
  have hexp : Tendsto (fun height : ℝ => Real.exp (-mu (height ^ (1 / (degree : ℝ)))))
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hmu.neg
  have hconstant : Tendsto (fun _ : ℝ => (4 : ℝ)) (𝓝[<] (1 : ℝ)) (𝓝 (4 : ℝ)) := tendsto_const_nhds
  have hquot := hconstant.div hheight one_ne_zero
  convert hquot.mul hexp using 1
  · ext height
    rfl
  · norm_num

end SmaleRate.Proofs
