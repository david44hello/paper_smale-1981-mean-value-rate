/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0003
import SmaleRate.Proofs.Generated.D7Chunk0004

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0007 : BoxTree := (.split (.split (.split (.split (.leaf (252382395563/125000000000 : ℚ)) (.leaf (252381983873/125000000000 : ℚ))) (.split (.leaf (2019052616959/1000000000000 : ℚ)) (.leaf (201904940239/100000000000 : ℚ)))) (.split (.split (.leaf (1009523113631/500000000000 : ℚ)) (.leaf (403808618307/200000000000 : ℚ))) (.split (.leaf (201903999517/100000000000 : ℚ)) (.leaf (100951846907/50000000000 : ℚ))))) (.split (.split (.split (.leaf (100951696021/50000000000 : ℚ)) (.leaf (50475773549/25000000000 : ℚ))) (.split (.leaf (1009514001371/500000000000 : ℚ)) (.leaf (1009512551361/500000000000 : ℚ)))) (.split (.split (.leaf (403804448377/200000000000 : ℚ)) (.leaf (1009509710089/500000000000 : ℚ))) (.split (.leaf (2019016637601/1000000000000 : ℚ)) (.leaf (1009506947039/500000000000 : ℚ))))))

theorem cover7_tree0007_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0007 (67/512 : ℚ) (135/1024 : ℚ) := by
  unfold cover7_tree0007
  refine tree_all_split_at (269/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (537/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1073/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2145/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0094_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0095_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2147/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0096_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0097_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1075/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2149/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0098_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0099_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2151/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0100_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0101_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (539/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1077/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2153/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0102_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0103_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2155/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0104_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0105_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1079/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2157/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0106_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0107_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2159/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0108_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0109_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0007_checked
#print axioms SmaleRate.Proofs.cover7_tree0007_checked
