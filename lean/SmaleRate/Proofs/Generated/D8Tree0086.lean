/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0055

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0086 : BoxTree := (.split (.split (.split (.split (.leaf (1027453437937/500000000000 : ℚ)) (.leaf (256863366237/125000000000 : ℚ))) (.split (.leaf (410981396811/200000000000 : ℚ)) (.leaf (1027453519191/500000000000 : ℚ)))) (.split (.split (.leaf (1027453546439/500000000000 : ℚ)) (.leaf (1027453573753/500000000000 : ℚ))) (.split (.leaf (2054907202309/1000000000000 : ℚ)) (.leaf (1027453628629/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054907312367/1000000000000 : ℚ)) (.leaf (1027453683811/500000000000 : ℚ))) (.split (.leaf (513726855763/250000000000 : ℚ)) (.leaf (2054907478627/1000000000000 : ℚ)))) (.split (.split (.leaf (2054907534359/1000000000000 : ℚ)) (.leaf (2054907590241/1000000000000 : ℚ))) (.split (.leaf (2054907646291/1000000000000 : ℚ)) (.leaf (2054907702479/1000000000000 : ℚ))))))

theorem cover8_tree0086_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0086 (2113/16384 : ℚ) (1057/8192 : ℚ) := by
  unfold cover8_tree0086
  refine tree_all_split_at (4227/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8453/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16905/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33809/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1376_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1377_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33811/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1378_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1379_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16907/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33813/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1380_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1381_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33815/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1382_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1383_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8455/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16909/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33817/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1384_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1385_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33819/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1386_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1387_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16911/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33821/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1388_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1389_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33823/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1390_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1391_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0086_checked
#print axioms SmaleRate.Proofs.cover8_tree0086_checked
