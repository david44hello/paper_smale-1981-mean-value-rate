/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0051

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0080 : BoxTree := (.split (.split (.split (.split (.leaf (2054902418283/1000000000000 : ℚ)) (.leaf (1027451228639/500000000000 : ℚ))) (.split (.leaf (1027451248219/500000000000 : ℚ)) (.leaf (2054902535741/1000000000000 : ℚ)))) (.split (.split (.leaf (256862821901/125000000000 : ℚ)) (.leaf (2054902614827/1000000000000 : ℚ))) (.split (.leaf (1027451327301/500000000000 : ℚ)) (.leaf (513725673637/250000000000 : ℚ))))) (.split (.split (.split (.leaf (256862841831/125000000000 : ℚ)) (.leaf (1027451387441/500000000000 : ℚ))) (.split (.leaf (256862851913/125000000000 : ℚ)) (.leaf (1027451427929/500000000000 : ℚ)))) (.split (.split (.leaf (2054902896587/1000000000000 : ℚ)) (.leaf (2054902937453/1000000000000 : ℚ))) (.split (.leaf (513725744621/250000000000 : ℚ)) (.leaf (2054903019687/1000000000000 : ℚ))))))

theorem cover8_tree0080_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0080 (2107/16384 : ℚ) (527/4096 : ℚ) := by
  unfold cover8_tree0080
  refine tree_all_split_at (4215/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8429/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16857/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33713/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1280_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1281_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33715/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1282_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1283_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16859/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33717/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1284_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1285_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33719/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1286_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1287_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8431/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16861/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33721/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1288_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1289_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33723/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1290_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1291_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16863/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33725/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1292_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1293_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33727/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1294_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1295_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0080_checked
#print axioms SmaleRate.Proofs.cover8_tree0080_checked
