/-
SmaleRate — Palomar registry solution entry point (three standard axioms only, zero custom axioms).
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.Basic
public import SmaleRate.Defs.BackgroundFacts
public import SmaleRate.Proofs.MainBound
public import SmaleRate.Proofs.Elementary
public import SmaleRate.Proofs.EllipticOrder

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section

namespace SmaleRate.Registry

open Polynomial Filter Set
open scoped Topology BigOperators

/-- Refereed input: NIST DLMF 19.9.5 (Lehto–Virtanen 1973, p. 62) two-sided bound on `μ(k)`. -/
def DLMF1995Fact : Prop :=
  ∀ (modulus : ℝ), modulus ∈ Ioo 0 1 →
    Real.log ((1 + Real.sqrt (complement modulus)) ^ 2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus)

/-- Refereed input: D. Betsakos, *J. Aust. Math. Soc.* 94 (2013), Theorem 1.1, p. 146
(transfinite-diameter growth inequality for bounded holomorphic maps on the unit disk). -/
def Betsakos2013Fact : Prop :=
  ∀ (func : ℂ → ℂ), DifferentiableOn ℂ func (disk 1) →
    Bornology.IsBounded (func '' disk 1) → func 0 = 0 →
    (∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second) →
    ∀ (point : ℂ), point ∈ disk 1 → point ≠ 0 →
      ‖func point‖ ≤ 4 * transfiniteDiameter (func '' disk 1) * Real.exp (-mu ‖point‖)

theorem thm_1_1_conditional
    (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact)
    (hbetsakos : Betsakos2013Fact)
    (hdlmf : DLMF1995Fact)
    (degree : ℕ) (hdegree : 2 ≤ degree)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    Kd degree ≤ (yBound degree height : EReal) := by
  have hmu : AntitoneOn mu (Ioo 0 1) :=
    (Proofs.mu_decreasing_of_positive fun modulus hmodulus =>
      Proofs.mu_positive_of_lower_dlmf modulus hmodulus (hdlmf modulus hmodulus).1).antitoneOn
  unfold Kd
  apply iSup_le
  intro poly
  exact_mod_cast Proofs.polynomial_bound_given_facts hjordan hcoefficient hmu hbetsakos
    degree hdegree poly.val poly.property height hheight

theorem cor_1_2_conditional
    (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact)
    (hbetsakos : Betsakos2013Fact)
    (hdlmf : DLMF1995Fact)
    (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree < (target degree : EReal) := by
  apply Proofs.cor_1_2_of_ybound hdlmf degree hdegree
  have hlength := (Proofs.chosen_length_bounds degree hdegree).1
  exact thm_1_1_conditional hjordan hcoefficient hbetsakos hdlmf degree (by omega)
    (Real.exp (-Lchoice degree)) ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlength)⟩

theorem prop_3_4_limit_conditional (hdlmf : DLMF1995Fact) :
    Tendsto gap atTop (𝓝 (2 * Real.pi ^ 2)) :=
  Proofs.prop_3_4_limit_from_dlmf hdlmf

theorem prop_3_4_upper_conditional (hdlmf : DLMF1995Fact)
    (degree : ℕ) (hdegree : 8 ≤ degree) :
    gap degree ≤ 2 * Real.pi ^ 2 / (1 - Real.pi ^ 2 / ((degree : ℝ) * (ell degree) ^ 2)) :=
  Proofs.prop_3_4_upper_from_dlmf hdlmf degree hdegree

theorem cor_1_2_table3_and_majorant :
    (∀ degree : ℕ, 8 ≤ degree → majorant degree ≤ target degree) ∧
    (∀ degree : ℕ, 8 ≤ degree → degree ≤ 20 → majorant degree < target degree) :=
  ⟨Proofs.majorant_le_target, Proofs.cor_step2⟩

end SmaleRate.Registry
