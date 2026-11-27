/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.Generated.D7Cover
import SmaleRate.Proofs.Generated.D8Cover
import SmaleRate.Proofs.SevenAndRange
import SmaleRate.Proofs.TableTargets

noncomputable section
namespace SmaleRate.Proofs
open Set

section
variable (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1,
  ellipticK modulus = Real.pi/(2*agm (complement modulus)))
variable (hdlmf : ∀ modulus ∈ Ioo (0 : ℝ) 1,
  Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
  mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
include hidentity hdlmf

theorem certified_seven_enclosure :
    (20190/10000 : ℝ) < bestBound 7 ∧ bestBound 7 < (20191/10000 : ℝ) := by
  constructor
  · convert cover7_best_bound_lower hidentity hdlmf using 1 <;> norm_num
  · apply best_bound_upper_of_beta_strict 7 (13621/100000) (20191/10000) (by norm_num)
    convert point7_certificate hidentity using 1 <;> norm_num

theorem certified_eight_enclosure :
    (20549/10000 : ℝ) < bestBound 8 ∧ bestBound 8 < (20550/10000 : ℝ) := by
  constructor
  · exact cover8_best_bound_lower hidentity hdlmf
  · apply best_bound_upper_of_beta_strict 8 (12766/100000) (20550/10000) (by norm_num)
    convert point8_certificate hidentity using 1 <;> norm_num

theorem certified_seven_target_improvement : target 7 < bestBound 7 := by
  have hbound := (certified_seven_enclosure hidentity hdlmf).1
  linarith [degree_seven_target_upper]

theorem certified_eight_gap_enclosure : (4 : ℝ) < gap 8 ∧ gap 8 < (4045/1000 : ℝ) := by
  have hbound := certified_eight_enclosure hidentity hdlmf
  exact ⟨range_eight_gap_lower_of_upper hbound.2, range_eight_gap_upper_of_lower hbound.1⟩

end
end SmaleRate.Proofs

#check SmaleRate.Proofs.certified_seven_enclosure
#print axioms SmaleRate.Proofs.certified_seven_enclosure
#check SmaleRate.Proofs.certified_eight_enclosure
#print axioms SmaleRate.Proofs.certified_eight_enclosure
#check SmaleRate.Proofs.certified_seven_target_improvement
#print axioms SmaleRate.Proofs.certified_seven_target_improvement
#check SmaleRate.Proofs.certified_eight_gap_enclosure
#print axioms SmaleRate.Proofs.certified_eight_gap_enclosure
