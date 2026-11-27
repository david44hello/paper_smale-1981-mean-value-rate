/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0023
import SmaleRate.Proofs.Generated.D7Chunk0024

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0038 : BoxTree := (.split (.split (.split (.split (.split (.leaf (3230843969/1600000000 : ℚ)) (.leaf (1009652814501/500000000000 : ℚ))) (.split (.leaf (2019334282563/1000000000000 : ℚ)) (.leaf (1009681719931/500000000000 : ℚ)))) (.split (.split (.leaf (403878619903/200000000000 : ℚ)) (.leaf (403884652017/200000000000 : ℚ))) (.split (.leaf (2019453920177/1000000000000 : ℚ)) (.leaf (1009742539201/500000000000 : ℚ))))) (.split (.split (.leaf (1009527944983/500000000000 : ℚ)) (.leaf (1009560827581/500000000000 : ℚ))) (.split (.leaf (1009594692457/500000000000 : ℚ)) (.leaf (201925906837/100000000000 : ℚ))))) (.split (.split (.split (.leaf (2019330694851/1000000000000 : ℚ)) (.leaf (1009702126851/500000000000 : ℚ))) (.split (.leaf (1009739867219/500000000000 : ℚ)) (.leaf (2019557126607/1000000000000 : ℚ)))) (.split (.split (.leaf (31556819061/15625000000 : ℚ)) (.leaf (1009858802053/500000000000 : ℚ))) (.split (.leaf (2019800669049/1000000000000 : ℚ)) (.leaf (25248570059/12500000000 : ℚ))))))

theorem cover7_tree0038_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0038 (19/128 : ℚ) (5/32 : ℚ) := by
  unfold cover7_tree0038
  refine tree_all_split_at (39/256 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (77/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (153/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (305/2048 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (609/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0594_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0595_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (611/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0596_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0597_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (307/2048 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (613/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0598_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0599_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (615/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0600_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0601_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (155/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (309/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0602_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0603_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (311/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0604_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0605_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (79/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (157/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (313/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0606_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0607_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (315/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0608_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0609_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (159/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (317/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0610_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0611_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (319/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0612_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0613_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0038_checked
#print axioms SmaleRate.Proofs.cover7_tree0038_checked
