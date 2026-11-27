/-
SmaleRate — minimal isolated definitions retained from public earlier Smale reuse.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see upstream LICENSE.
Provenance: public tag smale-mean-value-constant-v2.90, tag object ec8636ff8d997446a7b3610be2cc8529a6fae019,
peeled commit afc571844c24d077b891bad410962765328fa931,
papers_supporting_materials/smale-mean-value-constant/lean/Smale/Defs/Basic.lean.
Original SHA256241d55ec792a8d922ffd75d2afd84a740ce8395598183ca7c939e9b9e36a3f89.
Only the six definitions needed by ArgPrinciple/Lemma53 are retained, under an isolated namespace.
The bridge to's nonzero-derivative class and actual quotient is a separate proof.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Mathlib

set_option backward.proofsInPublic true

@[expose] public section

namespace SmaleRate.Legacy009
open Polynomial Complex Metric

/-- Derivative-one derivative-one class, distinct from SmaleRate IsPd. -/
def IsPd (degree : ℕ) (poly : ℂ[X]) : Prop :=
  poly.natDegree = degree ∧ poly.eval 0 = 0 ∧ poly.derivative.eval 0 = 1

/-- Derivative-one critical ratios, with derivative normalization implicit only in its class. -/
def critRatios (poly : ℂ[X]) : Set ℝ :=
  {value | ∃ point : ℂ, poly.derivative.eval point = 0 ∧ value = ‖poly.eval point‖ / ‖point‖}

noncomputable def mval (poly : ℂ[X]) : ℝ := sInf (critRatios poly)

noncomputable def Kd (degree : ℕ) : EReal :=
  ⨆ poly : {poly : ℂ[X] // IsPd degree poly}, ((mval poly.val : ℝ) : EReal)

noncomputable def zerosInBall (poly : ℂ[X]) (center : ℂ) (radius : ℝ) : ℕ :=
  (poly.roots.filter fun point => ‖point - center‖ < radius).card

noncomputable def zerosInDisk (poly : ℂ[X]) : ℕ := zerosInBall poly 0 1

end SmaleRate.Legacy009
