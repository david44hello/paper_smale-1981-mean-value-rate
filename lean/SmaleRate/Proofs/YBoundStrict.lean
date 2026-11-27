/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.YBoundLimits

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem scalar_strict_near_zero (degree : ℕ) :
    ∀ᶠ root : ℝ in 𝓝[>] 0,
      1 < (Real.sqrt (1-root^4))^(degree-1) * (1+root)^2 := by
  let func : ℝ → ℝ := fun root => (Real.sqrt (1-root^4))^(degree-1) * (1+root)^2
  have hsqrt : HasDerivAt (fun root : ℝ => Real.sqrt (1-root^4)) 0 0 := by
    convert (((hasDerivAt_const 0 (1 : ℝ)).sub ((hasDerivAt_id 0).pow 4)).sqrt (by norm_num)) using 1 <;>
      norm_num
  have hfunc : HasDerivAt func 2 0 := by
    convert (hsqrt.pow (degree-1)).mul (((hasDerivAt_const 0 (1 : ℝ)).add (hasDerivAt_id 0)).pow 2) using 1 <;>
      norm_num [func]
    ext root
    simp [func, Pi.mul_apply, Pi.pow_apply, Pi.add_apply, id_eq]
  have hnear := hfunc.tendsto_slope_zero_right.eventually
    (lt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hnear, self_mem_nhdsWithin] with root hroot hpositive
  have hzero : func 0 = 1 := by simp [func]
  simp only [zero_add, smul_eq_mul, hzero] at hroot
  have hdivide : 1 < (func root-1) / root := by simpa only [div_eq_mul_inv, mul_comm] using hroot
  have hvalue := (lt_div_iff₀ hpositive).mp hdivide
  have hrootpos : 0 < root := hpositive
  change 1 < func root
  linarith

theorem ybound_below_four_near_one_from_dlmf
    (hlower : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus)
    (degree : ℕ) (hdegree : 2 ≤ degree) :
    ∀ᶠ height : ℝ in 𝓝[<] 1, yBound degree height < 4 := by
  let radiusY : ℝ → ℝ := fun height => height ^ (1 / (degree : ℝ))
  let rootY : ℝ → ℝ := fun height => Real.sqrt (complement (radiusY height))
  have hradius : ContinuousAt radiusY 1 := by dsimp [radiusY]; fun_prop (disch := norm_num)
  have hroot : ContinuousAt rootY 1 := by dsimp [rootY, complement]; fun_prop
  have hroot_limit : Tendsto rootY (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa [rootY, radiusY, complement] using hroot.tendsto.mono_left nhdsWithin_le_nhds
  have hroot_within : Tendsto rootY (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hroot_limit, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with height hheight
    exact Real.sqrt_pos.mpr (complement_mem (radiusY height) (ypower_mem degree hdegree height hheight)).1
  have hscalar := hroot_within.eventually (scalar_strict_near_zero degree)
  filter_upwards [hscalar, Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with height hscalar hheight
  have hradius_mem := ypower_mem degree hdegree height hheight
  have hradiuspos : 0 < radiusY height := hradius_mem.1
  have hroot_nonneg : 0 ≤ rootY height := Real.sqrt_nonneg _
  have hcomp := complement_mem (radiusY height) hradius_mem
  have hroot_sq : (rootY height)^2 = complement (radiusY height) := Real.sq_sqrt hcomp.1.le
  have harg : 0 ≤ 1-(radiusY height)^2 := by nlinarith [hradius_mem.1, hradius_mem.2]
  have hcomp_sq : (complement (radiusY height))^2 = 1-(radiusY height)^2 := Real.sq_sqrt harg
  have hfourth : (rootY height)^4 = 1-(radiusY height)^2 := by nlinarith [sq_nonneg ((rootY height)^2)]
  have hrecover : Real.sqrt (1-(rootY height)^4) = radiusY height := by
    rw [hfourth]
    convert Real.sqrt_sq hradius_mem.1.le using 1 <;> congr 1 <;> ring
  rw [hrecover] at hscalar
  have hpower : (radiusY height)^degree = height := by
    dsimp [radiusY]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hheight.1.le]
    have hdegreepos : (degree : ℝ) ≠ 0 := by exact_mod_cast (show degree ≠ 0 by omega)
    rw [one_div_mul_cancel hdegreepos, Real.rpow_one]
  have hlower_bound := hlower (radiusY height) hradius_mem
  have hexp := Real.exp_lt_exp.mpr (neg_lt_neg hlower_bound)
  have hdenpos : 0 < (1+rootY height)^2 / radiusY height := by
    positivity
  change Real.exp (-Real.log ((1+rootY height)^2 / radiusY height)) >
    Real.exp (-mu (radiusY height)) at hexp
  have hlog_exp : Real.exp (-Real.log ((1+rootY height)^2 / radiusY height)) =
      radiusY height / (1+rootY height)^2 := by
    rw [Real.exp_neg, Real.exp_log hdenpos, inv_div]
  rw [hlog_exp] at hexp
  have hfactor : radiusY height < height * (1+rootY height)^2 := by
    have hpos := mul_lt_mul_of_pos_left hscalar hradius_mem.1
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ degree), hpower] at hpos
    simpa only [mul_one] using hpos
  have hratio : radiusY height / (1+rootY height)^2 < height :=
    (div_lt_iff₀ (sq_pos_of_pos (by linarith : 0 < 1+rootY height))).mpr hfactor
  unfold yBound
  change (4 / height) * Real.exp (-mu (radiusY height)) < 4
  have hcombined := mul_lt_mul_of_pos_left (hexp.trans hratio) (div_pos (by norm_num : (0 : ℝ) < 4) hheight.1)
  simpa only [div_mul_cancel₀ _ hheight.1.ne'] using hcombined

end SmaleRate.Proofs
