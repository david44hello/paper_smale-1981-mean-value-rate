/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0047
import SmaleRate.Proofs.Generated.D8Chunk0048

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0075 : BoxTree := (.split (.split (.split (.split (.split (.leaf (1027451856923/500000000000 : ℚ)) (.leaf (2054903727009/1000000000000 : ℚ))) (.split (.leaf (205490374019/100000000000 : ℚ)) (.leaf (2054903753421/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903766699/1000000000000 : ℚ)) (.leaf (1027451890007/500000000000 : ℚ))) (.split (.leaf (410980758669/200000000000 : ℚ)) (.leaf (1027451903367/500000000000 : ℚ))))) (.split (.split (.split (.leaf (1027451910081/500000000000 : ℚ)) (.leaf (2054903833631/1000000000000 : ℚ))) (.split (.leaf (64215745223/31250000000 : ℚ)) (.leaf (2054903860681/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903874261/1000000000000 : ℚ)) (.leaf (2054903887901/1000000000000 : ℚ))) (.split (.leaf (2054903901557/1000000000000 : ℚ)) (.leaf (1027451957629/500000000000 : ℚ)))))) (.split (.split (.split (.leaf (2054900023367/1000000000000 : ℚ)) (.leaf (513725012763/250000000000 : ℚ))) (.split (.leaf (513725019721/250000000000 : ℚ)) (.leaf (2054900106891/1000000000000 : ℚ)))) (.split (.split (.leaf (2054900135031/1000000000000 : ℚ)) (.leaf (128431260209/62500000000 : ℚ))) (.split (.leaf (2054900191807/1000000000000 : ℚ)) (.leaf (513725055111/250000000000 : ℚ))))))

theorem cover8_tree0075_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0075 (1051/8192 : ℚ) (2103/16384 : ℚ) := by
  unfold cover8_tree0075
  refine tree_all_split_at (4205/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8409/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16817/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33633/262144 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (67265/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1192_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1193_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (67267/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1194_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1195_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33635/262144 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (67269/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1196_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1197_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (67271/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1198_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1199_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16819/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33637/262144 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (67273/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1200_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1201_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (67275/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1202_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1203_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33639/262144 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (67277/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1204_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1205_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (67279/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1206_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1207_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8411/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16821/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33641/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1208_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1209_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33643/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1210_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1211_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16823/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33645/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1212_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1213_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33647/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1214_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1215_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0075_checked
#print axioms SmaleRate.Proofs.cover8_tree0075_checked
