/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0041

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0065 : BoxTree := (.split (.split (.split (.split (.leaf (2054902117529/1000000000000 : ℚ)) (.leaf (513725531089/250000000000 : ℚ))) (.split (.leaf (1027451065621/500000000000 : ℚ)) (.leaf (1027451069081/500000000000 : ℚ)))) (.split (.split (.leaf (2054902145121/1000000000000 : ℚ)) (.leaf (2054902152109/1000000000000 : ℚ))) (.split (.leaf (1027451079571/500000000000 : ℚ)) (.leaf (1027451083109/500000000000 : ℚ))))) (.split (.split (.split (.leaf (1027451086667/500000000000 : ℚ)) (.leaf (256862772561/125000000000 : ℚ))) (.split (.leaf (513725546921/250000000000 : ℚ)) (.leaf (64215693591/31250000000 : ℚ)))) (.split (.split (.leaf (102745110109/50000000000 : ℚ)) (.leaf (410980441901/200000000000 : ℚ))) (.split (.leaf (41098044337/20000000000 : ℚ)) (.leaf (2054902224239/1000000000000 : ℚ))))))

theorem cover8_tree0065_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0065 (2097/16384 : ℚ) (4195/32768 : ℚ) := by
  unfold cover8_tree0065
  refine tree_all_split_at (8389/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16777/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33553/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67105/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1032_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1033_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67107/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1034_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1035_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33555/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67109/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1036_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1037_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67111/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1038_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1039_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16779/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33557/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67113/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1040_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1041_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67115/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1042_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1043_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33559/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67117/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1044_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1045_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67119/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1046_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1047_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0065_checked
#print axioms SmaleRate.Proofs.cover8_tree0065_checked
