/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0001
import SmaleRate.Proofs.Generated.D7Chunk0002

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0005 : BoxTree := (.split (.split (.split (.split (.leaf (1009586488763/500000000000 : ℚ)) (.leaf (2019144780493/1000000000000 : ℚ))) (.split (.leaf (403823452993/200000000000 : ℚ)) (.leaf (2019090428603/1000000000000 : ℚ)))) (.split (.split (.leaf (1009532134531/500000000000 : ℚ)) (.leaf (1009519392019/500000000000 : ℚ))) (.split (.leaf (2019013971229/1000000000000 : ℚ)) (.split (.leaf (2019248291417/1000000000000 : ℚ)) (.leaf (1009618151047/500000000000 : ℚ)))))) (.split (.split (.split (.split (.leaf (2019224479703/1000000000000 : ℚ)) (.leaf (80768512959/40000000000 : ℚ))) (.split (.leaf (2019201334597/1000000000000 : ℚ)) (.leaf (252398751413/125000000000 : ℚ)))) (.split (.split (.leaf (252397356727/125000000000 : ℚ)) (.leaf (2019167861841/1000000000000 : ℚ))) (.split (.leaf (504789258779/250000000000 : ℚ)) (.leaf (2019146373339/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (504783969063/250000000000 : ℚ)) (.leaf (1009562771789/500000000000 : ℚ))) (.split (.leaf (2019115375023/1000000000000 : ℚ)) (.leaf (252388171291/125000000000 : ℚ)))) (.split (.split (.leaf (504773882301/250000000000 : ℚ)) (.leaf (201908585139/100000000000 : ℚ))) (.split (.leaf (2019076336613/1000000000000 : ℚ)) (.leaf (2019066984589/1000000000000 : ℚ)))))))

theorem cover7_tree0005_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0005 (1/8 : ℚ) (33/256 : ℚ) := by
  unfold cover7_tree0005
  refine tree_all_split_at (65/512 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (129/1024 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (257/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (513/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0044_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0045_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (515/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0046_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0047_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (259/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (517/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0048_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0049_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (519/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0050_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1039/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0051_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0052_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (131/1024 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (261/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (521/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1041/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0053_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0054_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1043/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0055_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0056_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (523/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1045/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0057_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0058_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1047/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0059_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0060_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (263/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (525/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1049/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0061_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0062_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1051/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0063_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0064_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (527/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1053/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0065_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0066_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1055/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0067_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0068_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0005_checked
#print axioms SmaleRate.Proofs.cover7_tree0005_checked
