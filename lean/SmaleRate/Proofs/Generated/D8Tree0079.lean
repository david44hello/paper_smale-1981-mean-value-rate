/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0050
public import SmaleRate.Proofs.Generated.D8Chunk0051

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0079 : BoxTree := (.split (.split (.split (.split (.leaf (2054901815707/1000000000000 : ℚ)) (.leaf (1027450926091/500000000000 : ℚ))) (.split (.leaf (205490188883/100000000000 : ℚ)) (.leaf (513725481407/250000000000 : ℚ)))) (.split (.split (.leaf (1027450981291/500000000000 : ℚ)) (.leaf (1027450999849/500000000000 : ℚ))) (.split (.leaf (1027451018487/500000000000 : ℚ)) (.leaf (513725518597/250000000000 : ℚ))))) (.split (.split (.split (.leaf (2054902111971/1000000000000 : ℚ)) (.leaf (1027451074859/500000000000 : ℚ))) (.split (.leaf (2054902187607/1000000000000 : ℚ)) (.leaf (8026961819/3906250000 : ℚ)))) (.split (.split (.leaf (513725565969/250000000000 : ℚ)) (.leaf (2054902302243/1000000000000 : ℚ))) (.split (.leaf (2054902340771/1000000000000 : ℚ)) (.leaf (410980475889/200000000000 : ℚ))))))

theorem cover8_tree0079_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0079 (1053/8192 : ℚ) (2107/16384 : ℚ) := by
  unfold cover8_tree0079
  refine tree_all_split_at (4213/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8425/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16849/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33697/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1264_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1265_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33699/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1266_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1267_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16851/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33701/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1268_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1269_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33703/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1270_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1271_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8427/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16853/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33705/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1272_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1273_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33707/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1274_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1275_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16855/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33709/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1276_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1277_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33711/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1278_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1279_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0079_checked
#print axioms SmaleRate.Proofs.cover8_tree0079_checked
