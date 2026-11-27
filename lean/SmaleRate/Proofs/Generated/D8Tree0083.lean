/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0053

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0083 : BoxTree := (.split (.split (.split (.split (.leaf (128431529177/62500000000 : ℚ)) (.leaf (32107883021/15625000000 : ℚ))) (.split (.leaf (2054904560013/1000000000000 : ℚ)) (.leaf (2054904606853/1000000000000 : ℚ)))) (.split (.split (.leaf (2054904653831/1000000000000 : ℚ)) (.leaf (2054904700977/1000000000000 : ℚ))) (.split (.leaf (2054904748271/1000000000000 : ℚ)) (.leaf (1027452397861/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054904843343/1000000000000 : ℚ)) (.leaf (410980978219/200000000000 : ℚ))) (.split (.leaf (102745246951/50000000000 : ℚ)) (.leaf (410980997419/200000000000 : ℚ)))) (.split (.split (.leaf (32107891177/15625000000 : ℚ)) (.leaf (1027452541863/500000000000 : ℚ))) (.split (.leaf (513726283069/250000000000 : ℚ)) (.leaf (82196207239/40000000000 : ℚ))))))

theorem cover8_tree0083_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0083 (1055/8192 : ℚ) (2111/16384 : ℚ) := by
  unfold cover8_tree0083
  refine tree_all_split_at (4221/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8441/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16881/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33761/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1328_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1329_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33763/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1330_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1331_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16883/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33765/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1332_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1333_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33767/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1334_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1335_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8443/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16885/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33769/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1336_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1337_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33771/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1338_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1339_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16887/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33773/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1340_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1341_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33775/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1342_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1343_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0083_checked
#print axioms SmaleRate.Proofs.cover8_tree0083_checked
