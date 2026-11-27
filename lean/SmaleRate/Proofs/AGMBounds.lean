/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.Basic

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem agm_step_order (upper lower : ℝ) (hzero : 0 ≤ lower) (horder : lower ≤ upper) :
    lower ≤ Real.sqrt (upper*lower) ∧
      Real.sqrt (upper*lower) ≤ (upper+lower)/2 ∧
      (upper+lower)/2 ≤ upper ∧
      (upper+lower)/2-Real.sqrt (upper*lower) ≤ (upper-lower)/2 := by
  have hu : 0 ≤ upper := hzero.trans horder
  have hproduct : 0 ≤ upper*lower := mul_nonneg hu hzero
  have hlower : lower ≤ Real.sqrt (upper*lower) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg hzero (sub_nonneg.mpr horder)]
  have hmean : Real.sqrt (upper*lower) ≤ (upper+lower)/2 := by
    apply (Real.sqrt_le_left (by linarith)).2
    nlinarith [sq_nonneg (upper-lower)]
  exact ⟨hlower, hmean, by linarith, by linarith⟩

theorem agm_pair_bounds (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (index : ℕ) :
    modulus ≤ (agmPair modulus index).2 ∧ 0 ≤ (agmPair modulus index).2 ∧
      (agmPair modulus index).2 ≤ (agmPair modulus index).1 ∧
      (agmPair modulus index).1 ≤ 1 := by
  induction index with
  | zero => simp only [agmPair]; exact ⟨le_rfl, hmodulus.1.le, hmodulus.2.le, le_rfl⟩
  | succ index ih =>
    have hstep := agm_step_order (agmPair modulus index).1 (agmPair modulus index).2 ih.2.1 ih.2.2.1
    simp only [agmPair]
    exact ⟨ih.1.trans hstep.1, Real.sqrt_nonneg _, hstep.2.1, hstep.2.2.1.trans ih.2.2.2⟩

theorem agm_pair_monotone (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    Monotone (fun index => (agmPair modulus index).2) ∧
      Antitone (fun index => (agmPair modulus index).1) := by
  have hstep (index : ℕ) := agm_step_order (agmPair modulus index).1 (agmPair modulus index).2
    (agm_pair_bounds modulus hmodulus index).2.1 (agm_pair_bounds modulus hmodulus index).2.2.1
  constructor
  · apply monotone_nat_of_le_succ
    intro index
    simpa only [agmPair] using (hstep index).1
  · apply antitone_nat_of_succ_le
    intro index
    simpa only [agmPair] using (hstep index).2.2.1

theorem agm_cross_order (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (first second : ℕ) :
    (agmPair modulus first).2 ≤ (agmPair modulus second).1 := by
  have hmono := agm_pair_monotone modulus hmodulus
  rcases le_total first second with h | h
  · exact (hmono.1 h).trans (agm_pair_bounds modulus hmodulus second).2.2.1
  · exact (agm_pair_bounds modulus hmodulus first).2.2.1.trans (hmono.2 h)

theorem agm_range_bdd (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    BddBelow (Set.range fun index => (agmPair modulus index).1) := by
  refine ⟨modulus, ?_⟩
  rintro value ⟨index, rfl⟩
  exact (agm_pair_bounds modulus hmodulus index).1.trans
    (agm_pair_bounds modulus hmodulus index).2.2.1

theorem agm_sandwich (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (index : ℕ) :
    (agmPair modulus index).2 ≤ agm modulus ∧ agm modulus ≤ (agmPair modulus index).1 := by
  constructor
  · apply le_csInf (Set.range_nonempty _)
    rintro value ⟨second, rfl⟩
    exact agm_cross_order modulus hmodulus index second
  · exact csInf_le (agm_range_bdd modulus hmodulus) (Set.mem_range_self index)

theorem agm_bracketing_proved (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (index : ℕ) :
    (agmPair modulus index).2 ≤ (agmPair modulus (index+1)).2 ∧
    (agmPair modulus (index+1)).2 ≤ (agmPair modulus (index+1)).1 ∧
    (agmPair modulus (index+1)).1 ≤ (agmPair modulus index).1 ∧
    (agmPair modulus (index+1)).1-(agmPair modulus (index+1)).2 ≤
      ((agmPair modulus index).1-(agmPair modulus index).2)/2 ∧
    (agmPair modulus index).2 ≤ agm modulus ∧ agm modulus ≤ (agmPair modulus index).1 := by
  have hstep := agm_step_order (agmPair modulus index).1 (agmPair modulus index).2
    (agm_pair_bounds modulus hmodulus index).2.1 (agm_pair_bounds modulus hmodulus index).2.2.1
  refine ⟨?_, ?_, ?_, ?_, (agm_sandwich modulus hmodulus index).1,
    (agm_sandwich modulus hmodulus index).2⟩
  · simpa only [agmPair] using hstep.1
  · simpa only [agmPair] using hstep.2.1
  · simpa only [agmPair] using hstep.2.2.1
  · simpa only [agmPair] using hstep.2.2.2

theorem agm_gap_bound (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (index : ℕ) :
    (agmPair modulus index).1-(agmPair modulus index).2 ≤ (1-modulus)*(1/2 : ℝ)^index := by
  induction index with
  | zero => simp [agmPair]
  | succ index ih =>
    have h := (agm_bracketing_proved modulus hmodulus index).2.2.2.1
    rw [pow_succ]
    exact h.trans (by linarith)

theorem agm_convergence_proved (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    Tendsto (fun index => (agmPair modulus index).1) atTop (𝓝 (agm modulus)) ∧
    Tendsto (fun index => (agmPair modulus index).2) atTop (𝓝 (agm modulus)) := by
  have hupper : Tendsto (fun index => (agmPair modulus index).1) atTop (𝓝 (agm modulus)) := by
    exact tendsto_atTop_ciInf (agm_pair_monotone modulus hmodulus).2 (agm_range_bdd modulus hmodulus)
  have hgeo : Tendsto (fun index : ℕ => (1-modulus)*(1/2 : ℝ)^index) atTop (𝓝 0) := by
    simpa using (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).const_mul (1-modulus)
  have hgap : Tendsto (fun index => (agmPair modulus index).1-(agmPair modulus index).2) atTop (𝓝 0) := by
    exact squeeze_zero (fun index => sub_nonneg.mpr (agm_pair_bounds modulus hmodulus index).2.2.1)
      (agm_gap_bound modulus hmodulus) hgeo
  have hid : (fun index => (agmPair modulus index).1-
      ((agmPair modulus index).1-(agmPair modulus index).2)) =
      (fun index => (agmPair modulus index).2) := by funext index; ring
  exact ⟨hupper, by simpa only [hid, sub_zero] using hupper.sub hgap⟩

theorem agm_initial_bounds (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    modulus ≤ agm modulus ∧ agm modulus ≤ 1 := by
  simpa only [agmPair] using agm_sandwich modulus hmodulus 0

end SmaleRate.Proofs


