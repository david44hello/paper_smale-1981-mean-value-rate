/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0051
import SmaleRate.Proofs.Generated.D8Chunk0052

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0081 : BoxTree := (.split (.split (.split (.split (.leaf (1027451530513/500000000000 : ℚ)) (.leaf (1027451551267/500000000000 : ℚ))) (.split (.leaf (10274515721/5000000000 : ℚ)) (.leaf (2054903186007/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903227977/1000000000000 : ℚ)) (.leaf (513725817529/250000000000 : ℚ))) (.split (.leaf (256862914051/125000000000 : ℚ)) (.leaf (2054903354849/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054903397443/1000000000000 : ℚ)) (.leaf (1027451720097/500000000000 : ℚ))) (.split (.leaf (2054903483111/1000000000000 : ℚ)) (.leaf (1027451763091/500000000000 : ℚ)))) (.split (.split (.leaf (2006741767/976562500 : ℚ)) (.leaf (1027451806401/500000000000 : ℚ))) (.split (.leaf (2054903656333/1000000000000 : ℚ)) (.leaf (1027451850017/500000000000 : ℚ))))))

theorem cover8_tree0081_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0081 (527/4096 : ℚ) (2109/16384 : ℚ) := by
  unfold cover8_tree0081
  refine tree_all_split_at (4217/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8433/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16865/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33729/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1296_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1297_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33731/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1298_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1299_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16867/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33733/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1300_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1301_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33735/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1302_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1303_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8435/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16869/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33737/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1304_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1305_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33739/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1306_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1307_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16871/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33741/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1308_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1309_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33743/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1310_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1311_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0081_checked
#print axioms SmaleRate.Proofs.cover8_tree0081_checked
