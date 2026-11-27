/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0025

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0041 : BoxTree := (.split (.split (.split (.leaf (505519726457/250000000000 : ℚ)) (.leaf (20471500453/10000000000 : ℚ))) (.leaf (1020116743231/500000000000 : ℚ))) (.leaf (2045160682289/1000000000000 : ℚ)))

theorem cover7_tree0041_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0041 (1/4 : ℚ) (1/2 : ℚ) := by
  unfold cover7_tree0041
  refine tree_all_split_at (3/8 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (5/16 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (9/32 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0638_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0639_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · convert cover7_leaf0640_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
  · convert cover7_leaf0641_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0041_checked
#print axioms SmaleRate.Proofs.cover7_tree0041_checked
