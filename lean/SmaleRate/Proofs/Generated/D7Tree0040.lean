/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0025

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0040 : BoxTree := (.split (.split (.split (.split (.leaf (505858466277/250000000000 : ℚ)) (.leaf (63283151729/31250000000 : ℚ))) (.leaf (505162507783/250000000000 : ℚ))) (.split (.leaf (2024441816561/1000000000000 : ℚ)) (.leaf (405704742503/200000000000 : ℚ)))) (.split (.leaf (2021640761009/1000000000000 : ℚ)) (.leaf (2031528004067/1000000000000 : ℚ))))

theorem cover7_tree0040_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0040 (3/16 : ℚ) (1/4 : ℚ) := by
  unfold cover7_tree0040
  refine tree_all_split_at (7/32 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (13/64 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (25/128 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (49/256 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0631_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0632_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0633_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (27/128 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0634_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0635_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (15/64 : ℚ) (by norm_num) ?_ ?_
    · convert cover7_leaf0636_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · convert cover7_leaf0637_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0040_checked
#print axioms SmaleRate.Proofs.cover7_tree0040_checked
