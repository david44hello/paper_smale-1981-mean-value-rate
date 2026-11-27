/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.Basic

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

theorem capacity_step_scalar (value height derivative critical cap : ℝ)
    (hvalue : 0 < value) (hheight : 0 < height)
    (hderivative : 0 < derivative) (hcritical : 0 < critical)
    (hbound : value ≤ derivative / critical)
    (hcap : cap = critical / (height * derivative)) : cap ≤ 1 / (height * value) := by
  rw [hcap]
  apply (div_le_div_iff₀ (mul_pos hheight hderivative) (mul_pos hheight hvalue)).2
  have hproduct := mul_le_mul_of_nonneg_left ((le_div_iff₀ hcritical).mp hbound) hheight.le
  nlinarith

theorem final_scalar_deduction (value height inner outer cap : ℝ)
    (hvalue : 0 < value) (hheight : 0 < height)
    (hinner : inner ∈ Ioo 0 1) (houter : outer ∈ Ioo 0 1) (horder : inner ≤ outer)
    (hmu : AntitoneOn mu (Ioo 0 1)) (hcap : cap ≤ 1 / (height * value))
    (hbets : 1 ≤ 4 * cap * Real.exp (-mu inner)) :
    value ≤ (4 / height) * Real.exp (-mu outer) := by
  have hexp : Real.exp (-mu inner) ≤ Real.exp (-mu outer) :=
    Real.exp_le_exp.mpr (neg_le_neg (hmu hinner houter horder))
  have hfirst : 1 ≤ 4 * (1 / (height * value)) * Real.exp (-mu inner) :=
    hbets.trans (by gcongr)
  have hsecond : 1 ≤ 4 * (1 / (height * value)) * Real.exp (-mu outer) :=
    hfirst.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hid : 4 * (1 / (height * value)) * Real.exp (-mu outer) =
      ((4 / height) * Real.exp (-mu outer)) / value := by ring
  rw [hid] at hsecond
  simpa only [one_mul] using (le_div_iff₀ hvalue).mp hsecond

end SmaleRate.Proofs
