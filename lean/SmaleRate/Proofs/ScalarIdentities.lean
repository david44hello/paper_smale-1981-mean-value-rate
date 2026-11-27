/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.Basic

noncomputable section
namespace SmaleRate.Proofs

theorem crane_gap_order_proved (degree : ℕ) : 4-crane degree = (2263/1000)/Real.sqrt degree := by
  unfold crane
  ring

theorem fujikawa_identity_proved (degree : ℕ) (hdegree : 2 ≤ degree) :
    fujikawa degree = 4-4*(((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2)/((degree : ℝ)+1) := by
  unfold fujikawa
  rw [Nat.cast_sub hdegree]
  push_cast
  field_simp
  ring

end SmaleRate.Proofs
