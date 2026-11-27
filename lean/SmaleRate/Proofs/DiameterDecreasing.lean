/-
SmaleRate — cross-count n-diameter and limit bridge.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.DiameterMonotonicity

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology
open scoped BigOperators

theorem diameter_limit_of_antitone (domain : Set ℂ) (hbounded : Bornology.IsBounded domain)
    (hnonempty : domain.Nonempty) (hanti : AntitoneOn (nDiameter domain) (Ici 2)) :
    Tendsto (nDiameter domain) atTop (𝓝 (transfiniteDiameter domain)) := by
  let sequence : ℕ → ℝ := fun index => nDiameter domain (index + 2)
  have hnonneg : ∀ index, 0 ≤ nDiameter domain index := fun index =>
    nDiameter_nonneg_of_subset_compact domain (closure domain) hnonempty subset_closure
      hbounded.isCompact_closure index
  have hanti_sequence : Antitone sequence := by
    intro first second horder
    change nDiameter domain (second + 2) ≤ nDiameter domain (first + 2)
    exact hanti (show 2 ≤ first + 2 from by omega)
      (show 2 ≤ second + 2 from by omega) (by omega)
  have hlower : BddBelow (range sequence) := ⟨0, by
    rintro value ⟨index, rfl⟩
    exact hnonneg (index + 2)⟩
  have hlower_set : BddBelow {value : ℝ | ∃ count ≥ 2, value = nDiameter domain count} :=
    ⟨0, by rintro value ⟨count, _, rfl⟩; exact hnonneg count⟩
  have hinf : (⨅ index, sequence index) = transfiniteDiameter domain := by
    unfold transfiniteDiameter
    apply le_antisymm
    · apply le_csInf (s := {value : ℝ | ∃ count ≥ 2, value = nDiameter domain count})
        ⟨nDiameter domain 2, 2, le_rfl, rfl⟩
      rintro value ⟨count, hcount, rfl⟩
      have hindex := ciInf_le hlower (count - 2)
      simpa only [sequence, Nat.sub_add_cancel hcount] using hindex
    · apply le_ciInf
      intro index
      exact csInf_le hlower_set ⟨index + 2, by omega, rfl⟩
  have hlimit := tendsto_atTop_ciInf hanti_sequence hlower
  rw [hinf] at hlimit
  exact (tendsto_add_atTop_iff_nat 2).mp hlimit

def pairFactor {count : ℕ} (points : Fin count → ℂ) (first second : Fin count) : ℝ :=
  if first < second then ‖points first - points second‖ else 1

def pairProduct {count : ℕ} (points : Fin count → ℂ) : ℝ :=
  ∏ first, ∏ second, pairFactor points first second

theorem configurationDiameter_eq_pairProduct (count : ℕ) (points : Fin count → ℂ) :
    configurationDiameter count points =
      pairProduct points ^ (2 / ((count : ℝ) * (count - 1 : ℕ))) := by
  simp only [configurationDiameter, pairProduct, pairFactor, Finset.prod_filter]

theorem pairProduct_nonneg {count : ℕ} (points : Fin count → ℂ) : 0 ≤ pairProduct points := by
  unfold pairProduct pairFactor
  positivity

def deletedPairProduct {count : ℕ} (points : Fin count → ℂ) (hole : Fin count) : ℝ :=
  ∏ first, ∏ second, if first = hole ∨ second = hole then 1 else pairFactor points first second

theorem pairProduct_succAbove (count : ℕ) (points : Fin (count + 1) → ℂ)
    (hole : Fin (count + 1)) :
    pairProduct (points ∘ hole.succAbove) = deletedPairProduct points hole := by
  have hreindex : pairProduct (points ∘ hole.succAbove) =
      ∏ first : Fin count, ∏ second : Fin count,
        pairFactor points (hole.succAbove first) (hole.succAbove second) := by
    simp only [pairProduct, pairFactor, Function.comp_apply,
      (Fin.strictMono_succAbove hole).lt_iff_lt]
  rw [hreindex]
  symm
  unfold deletedPairProduct
  rw [Fin.prod_univ_succAbove _ hole]
  simp only [true_or, ite_true, Finset.prod_const_one, one_mul]
  apply Finset.prod_congr rfl
  intro first _
  rw [Fin.prod_univ_succAbove _ hole]
  simp [Fin.succAbove_ne, eq_comm]

theorem product_deletedPairProduct (count : ℕ) (points : Fin count → ℂ) :
    (∏ hole, deletedPairProduct points hole) = pairProduct points ^ (count - 2) := by
  classical
  unfold deletedPairProduct pairProduct
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun hole second => if _ = hole ∨ second = hole then (1 : ℝ) else _)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro first _
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro second _
  by_cases heq : first = second
  · subst second
    simp [pairFactor]
  · have hfilter : Finset.univ.filter (fun hole : Fin count => ¬(first = hole ∨ second = hole)) =
        (Finset.univ.erase first).erase second := by
      ext hole
      simp [not_or, eq_comm, and_comm, and_left_comm]
    have hrewrite : (∏ hole, if first = hole ∨ second = hole then (1 : ℝ)
        else pairFactor points first second) =
        ∏ hole ∈ Finset.univ.filter (fun hole : Fin count => ¬(first = hole ∨ second = hole)),
          pairFactor points first second := by
      simp only [Finset.prod_filter, ite_not]
    rw [hrewrite, hfilter, Finset.prod_const]
    congr 1
    rw [Finset.card_erase_of_mem (by simp [Ne.symm heq]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, Fintype.card_fin]
    omega

theorem configuration_le_of_deletions (count : ℕ) (hcount : 2 ≤ count)
    (points : Fin (count + 1) → ℂ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hdeletions : ∀ hole : Fin (count + 1),
      configurationDiameter count (points ∘ hole.succAbove) ≤ bound) :
    configurationDiameter (count + 1) points ≤ bound := by
  have hcount_pos : 0 < (count : ℝ) := by exact_mod_cast (show 0 < count by omega)
  have hcount_one : 0 < (count : ℝ) - 1 := by
    have : (2 : ℝ) ≤ count := by exact_mod_cast hcount
    linarith
  have hcast_sub : ((count - 1 : ℕ) : ℝ) = (count : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) (show 1 ≤ count by omega))
  let weight : ℝ := (count : ℝ) * ((count : ℝ) - 1) / 2
  have hweight : 0 < weight := div_pos (mul_pos hcount_pos hcount_one) (by norm_num)
  have hexponent : 2 / ((count : ℝ) * (count - 1 : ℕ)) = weight⁻¹ := by
    rw [hcast_sub]
    dsimp [weight]
    field_simp
  have hdeleted_bound : ∀ hole, deletedPairProduct points hole ≤ bound ^ weight := by
    intro hole
    have hroot := hdeletions hole
    rw [configurationDiameter_eq_pairProduct, pairProduct_succAbove, hexponent] at hroot
    have hnonneg : 0 ≤ deletedPairProduct points hole := by
      rw [← pairProduct_succAbove]
      exact pairProduct_nonneg _
    simpa only [inv_inv] using
      (Real.le_rpow_inv_iff_of_pos hnonneg hbound (inv_pos.mpr hweight)).mpr hroot
  have hproduct : pairProduct points ^ (count - 1) ≤ (bound ^ weight) ^ (count + 1) := by
    have hprod := Finset.prod_le_prod₀
      (fun hole (_ : hole ∈ (Finset.univ : Finset (Fin (count + 1)))) =>
        show 0 ≤ deletedPairProduct points hole from by
          rw [← pairProduct_succAbove]; exact pairProduct_nonneg _)
      (fun hole _ => hdeleted_bound hole)
    rw [product_deletedPairProduct, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
    simpa only [show count + 1 - 2 = count - 1 by omega] using hprod
  let exponent : ℝ := 2 / (((count : ℝ) + 1) * (count : ℝ) * ((count : ℝ) - 1))
  have hexponent_nonneg : 0 ≤ exponent := by dsimp [exponent]; positivity
  have hpair_nonneg := pairProduct_nonneg points
  have hleft_exponent : ((count - 1 : ℕ) : ℝ) * exponent =
      2 / (((count + 1 : ℕ) : ℝ) * ((count + 1 - 1 : ℕ) : ℝ)) := by
    rw [hcast_sub]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    dsimp [exponent]
    field_simp
  have hright_exponent : weight * (((count + 1 : ℕ) : ℝ) * exponent) = 1 := by
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [weight, exponent]
    field_simp
  rw [configurationDiameter_eq_pairProduct, ← hleft_exponent,
    Real.rpow_natCast_mul hpair_nonneg]
  calc
    (pairProduct points ^ (count - 1)) ^ exponent ≤ ((bound ^ weight) ^ (count + 1)) ^ exponent :=
      Real.rpow_le_rpow (pow_nonneg hpair_nonneg _) hproduct hexponent_nonneg
    _ = bound := by
      rw [← Real.rpow_natCast_mul (Real.rpow_nonneg hbound _) (count + 1) exponent,
        ← Real.rpow_mul hbound, hright_exponent, Real.rpow_one]

theorem nDiameter_succ_le (domain : Set ℂ) (hbounded : Bornology.IsBounded domain)
    (hnonempty : domain.Nonempty) (count : ℕ) (hcount : 2 ≤ count) :
    nDiameter domain (count + 1) ≤ nDiameter domain count := by
  rw [nDiameter_eq_sSup_image]
  apply csSup_le (configuration_values_nonempty domain hnonempty (count + 1))
  rintro value ⟨points, hpoints, rfl⟩
  apply configuration_le_of_deletions count hcount points (nDiameter domain count)
    (nDiameter_nonneg_of_subset_compact domain (closure domain) hnonempty subset_closure
      hbounded.isCompact_closure count)
  intro hole
  rw [nDiameter_eq_sSup_image]
  exact le_csSup (configuration_values_bddAbove domain (closure domain) subset_closure
    hbounded.isCompact_closure count) ⟨points ∘ hole.succAbove,
      (fun index => hpoints (hole.succAbove index)), rfl⟩

theorem diameter_decreasing_proved (domain : Set ℂ) (hbounded : Bornology.IsBounded domain)
    (hinfinite : domain.Infinite) :
    AntitoneOn (nDiameter domain) (Ici 2) ∧
      Tendsto (nDiameter domain) atTop (𝓝 (transfiniteDiameter domain)) := by
  have hanti : AntitoneOn (nDiameter domain) (Ici 2) :=
    antitoneOn_nat_Ici_of_succ_le (nDiameter_succ_le domain hbounded hinfinite.nonempty)
  exact ⟨hanti, diameter_limit_of_antitone domain hbounded hinfinite.nonempty hanti⟩

end SmaleRate.Proofs


