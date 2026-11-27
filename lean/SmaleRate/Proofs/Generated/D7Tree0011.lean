/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0006

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0011 : BoxTree := (.split (.split (.split (.split (.leaf (2019020412621/1000000000000 : ℚ)) (.leaf (2019019528983/1000000000000 : ℚ))) (.split (.leaf (201901865491/100000000000 : ℚ)) (.leaf (2019017790407/1000000000000 : ℚ)))) (.split (.split (.leaf (63094279233/31250000000 : ℚ)) (.leaf (100950804503/50000000000 : ℚ))) (.split (.leaf (31547113347/15625000000 : ℚ)) (.leaf (252376803489/125000000000 : ℚ))))) (.split (.split (.split (.leaf (1009506805579/500000000000 : ℚ)) (.leaf (2019012803939/1000000000000 : ℚ))) (.split (.leaf (1009506003127/500000000000 : ℚ)) (.leaf (2019011218113/1000000000000 : ℚ)))) (.split (.split (.leaf (2019010439489/1000000000000 : ℚ)) (.leaf (252376208799/125000000000 : ℚ))) (.split (.leaf (2019008910823/1000000000000 : ℚ)) (.leaf (50475204019/25000000000 : ℚ))))))

theorem cover7_tree0011_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0011 (273/2048 : ℚ) (137/1024 : ℚ) := by
  unfold cover7_tree0011
  refine tree_all_split_at (547/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1093/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2185/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4369/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0153_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0154_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4371/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0155_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0156_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2187/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4373/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0157_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0158_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4375/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0159_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0160_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1095/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2189/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4377/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0161_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0162_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4379/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0163_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0164_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2191/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4381/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0165_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0166_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4383/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0167_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0168_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0011_checked
#print axioms SmaleRate.Proofs.cover7_tree0011_checked
