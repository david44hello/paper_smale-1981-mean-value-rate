/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0000

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0000 : BoxTree := (.split (.leaf (206997795373/100000000000 : ℚ)) (.split (.leaf (2056676994689/1000000000000 : ℚ)) (.leaf (405678441683/200000000000 : ℚ))))

theorem cover7_tree0000_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0000 (0/1 : ℚ) (1/16 : ℚ) := by
  unfold cover7_tree0000
  refine tree_all_split_at (1/32 : ℚ) (by norm_num) ?_ ?_
  · convert cover7_leaf0000_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (3/64 : ℚ) (by norm_num) ?_ ?_
    · convert cover7_leaf0001_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · convert cover7_leaf0002_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0000_checked
#print axioms SmaleRate.Proofs.cover7_tree0000_checked
