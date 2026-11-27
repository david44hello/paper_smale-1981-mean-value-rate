/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.Basic

noncomputable section
namespace SmaleRate.Proofs
open Set
open scoped BigOperators

def configurationDiameter (count : ℕ) (points : Fin count → ℂ) : ℝ :=
  (∏ first : Fin count, ∏ second ∈ Finset.univ.filter (first < ·),
    ‖points first - points second‖) ^ (2 / ((count : ℝ) * (count - 1 : ℕ)))

theorem configurationDiameter_continuous (count : ℕ) : Continuous (configurationDiameter count) := by
  unfold configurationDiameter
  fun_prop (disch := positivity)

theorem nDiameter_eq_sSup_image (domain : Set ℂ) (count : ℕ) :
    nDiameter domain count = sSup (configurationDiameter count ''
      {points : Fin count → ℂ | ∀ index, points index ∈ domain}) := by
  unfold nDiameter
  congr 1
  ext value
  constructor
  · rintro ⟨points, hpoints, hvalue⟩
    exact ⟨points, hpoints, hvalue.symm⟩
  · rintro ⟨points, hpoints, hvalue⟩
    exact ⟨points, hpoints, hvalue.symm⟩

theorem configuration_values_bddAbove (domain compactSet : Set ℂ)
    (hsubset : domain ⊆ compactSet) (hcompact : IsCompact compactSet) (count : ℕ) :
    BddAbove (configurationDiameter count ''
      {points : Fin count → ℂ | ∀ index, points index ∈ domain}) := by
  have hcompact_configs : IsCompact {points : Fin count → ℂ | ∀ index, points index ∈ compactSet} :=
    isCompact_pi_infinite (fun _ => hcompact)
  apply (hcompact_configs.image (configurationDiameter_continuous count)).bddAbove.mono
  rintro value ⟨points, hpoints, rfl⟩
  exact ⟨points, fun index => hsubset (hpoints index), rfl⟩

theorem configuration_values_nonempty (domain : Set ℂ) (hnonempty : domain.Nonempty) (count : ℕ) :
    (configurationDiameter count ''
      {points : Fin count → ℂ | ∀ index, points index ∈ domain}).Nonempty := by
  obtain ⟨point, hpoint⟩ := hnonempty
  exact ⟨configurationDiameter count (fun _ => point), ⟨(fun _ => point), (fun _ => hpoint), rfl⟩⟩

theorem nDiameter_nonneg_of_subset_compact (domain compactSet : Set ℂ)
    (hnonempty : domain.Nonempty) (hsubset : domain ⊆ compactSet)
    (hcompact : IsCompact compactSet) (count : ℕ) : 0 ≤ nDiameter domain count := by
  rw [nDiameter_eq_sSup_image]
  obtain ⟨value, points, hpoints, rfl⟩ := configuration_values_nonempty domain hnonempty count
  apply le_csSup_of_le (configuration_values_bddAbove domain compactSet hsubset hcompact count)
    (mem_image_of_mem _ hpoints)
  unfold configurationDiameter
  positivity

theorem nDiameter_mono_of_compact (domain compactSet : Set ℂ)
    (hnonempty : domain.Nonempty) (hsubset : domain ⊆ compactSet)
    (hcompact : IsCompact compactSet) (count : ℕ) : nDiameter domain count ≤ nDiameter compactSet count := by
  rw [nDiameter_eq_sSup_image, nDiameter_eq_sSup_image]
  apply csSup_le_csSup (configuration_values_bddAbove compactSet compactSet Subset.rfl hcompact count)
    (configuration_values_nonempty domain hnonempty count)
  rintro value ⟨points, hpoints, rfl⟩
  exact ⟨points, fun index => hsubset (hpoints index), rfl⟩

theorem transfiniteDiameter_mono_of_compact (domain compactSet : Set ℂ)
    (hnonempty : domain.Nonempty) (hsubset : domain ⊆ compactSet)
    (hcompact : IsCompact compactSet) : transfiniteDiameter domain ≤ transfiniteDiameter compactSet := by
  have hlower : BddBelow {value | ∃ count ≥ 2, value = nDiameter domain count} := by
    refine ⟨0, ?_⟩
    rintro value ⟨count, _, rfl⟩
    exact nDiameter_nonneg_of_subset_compact domain compactSet hnonempty hsubset hcompact count
  unfold transfiniteDiameter
  apply le_csInf (s := {value : ℝ | ∃ count ≥ (2 : ℕ), value = nDiameter compactSet count})
    (show {value : ℝ | ∃ count ≥ (2 : ℕ), value = nDiameter compactSet count}.Nonempty from
      ⟨nDiameter compactSet 2, 2, le_rfl, rfl⟩)
  rintro value ⟨count, hcount, rfl⟩
  exact (csInf_le hlower ⟨count, hcount, rfl⟩).trans
    (nDiameter_mono_of_compact domain compactSet hnonempty hsubset hcompact count)

theorem nDiameter_closure_of_bounded (domain : Set ℂ) (hbounded : Bornology.IsBounded domain)
    (hnonempty : domain.Nonempty) (count : ℕ) : nDiameter domain count = nDiameter (closure domain) count := by
  have hcompact : IsCompact (closure domain) := hbounded.isCompact_closure
  apply le_antisymm (nDiameter_mono_of_compact domain (closure domain) hnonempty subset_closure hcompact count)
  rw [nDiameter_eq_sSup_image (closure domain) count]
  apply csSup_le (configuration_values_nonempty (closure domain) (hnonempty.mono subset_closure) count)
  rintro value ⟨points, hpoints, rfl⟩
  have hclosed : IsClosed {configuration : Fin count → ℂ |
      configurationDiameter count configuration ≤ nDiameter domain count} :=
    isClosed_Iic.preimage (configurationDiameter_continuous count)
  have hsubset : {configuration : Fin count → ℂ | ∀ index, configuration index ∈ domain} ⊆
      {configuration : Fin count → ℂ | configurationDiameter count configuration ≤ nDiameter domain count} := by
    intro configuration hconfiguration
    rw [mem_setOf_eq, nDiameter_eq_sSup_image]
    exact le_csSup (configuration_values_bddAbove domain (closure domain) subset_closure hcompact count)
      (mem_image_of_mem _ hconfiguration)
  apply closure_minimal hsubset hclosed
  have hclosure : points ∈ closure (Set.pi Set.univ (fun _ : Fin count => domain)) :=
    mem_closure_pi.mpr (fun index _ => hpoints index)
  have hconfigs : Set.pi Set.univ (fun _ : Fin count => domain) =
      {configuration : Fin count → ℂ | ∀ index, configuration index ∈ domain} := by
    ext configuration
    simp
  rw [hconfigs] at hclosure
  exact hclosure

theorem transfiniteDiameter_closure_of_bounded (domain : Set ℂ)
    (hbounded : Bornology.IsBounded domain) (hnonempty : domain.Nonempty) :
    transfiniteDiameter domain = transfiniteDiameter (closure domain) := by
  unfold transfiniteDiameter
  simp_rw [← nDiameter_closure_of_bounded domain hbounded hnonempty]

end SmaleRate.Proofs
