/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0049

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0077 : BoxTree := (.split (.split (.split (.split (.leaf (256862591393/125000000000 : ℚ)) (.leaf (64215648831/31250000000 : ℚ))) (.split (.leaf (513725198553/250000000000 : ℚ)) (.leaf (2054900825989/1000000000000 : ℚ)))) (.split (.split (.leaf (2054900857917/1000000000000 : ℚ)) (.leaf (2054900889999/1000000000000 : ℚ))) (.split (.leaf (205490092223/100000000000 : ℚ)) (.leaf (1027450477317/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054900987193/1000000000000 : ℚ)) (.leaf (410980203981/200000000000 : ℚ))) (.split (.leaf (1027450526393/500000000000 : ℚ)) (.leaf (410980217161/200000000000 : ℚ)))) (.split (.split (.leaf (1027450559497/500000000000 : ℚ)) (.leaf (1027450576169/500000000000 : ℚ))) (.split (.leaf (2054901185843/1000000000000 : ℚ)) (.leaf (410980243899/200000000000 : ℚ))))))

theorem cover8_tree0077_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0077 (263/2048 : ℚ) (2105/16384 : ℚ) := by
  unfold cover8_tree0077
  refine tree_all_split_at (4209/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8417/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16833/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33665/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1232_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1233_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33667/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1234_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1235_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16835/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33669/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1236_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1237_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33671/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1238_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1239_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8419/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16837/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33673/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1240_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1241_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33675/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1242_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1243_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16839/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33677/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1244_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1245_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33679/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1246_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1247_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0077_checked
#print axioms SmaleRate.Proofs.cover8_tree0077_checked
