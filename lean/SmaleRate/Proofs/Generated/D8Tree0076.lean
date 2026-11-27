/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0048
import SmaleRate.Proofs.Generated.D8Chunk0049

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0076 : BoxTree := (.split (.split (.split (.split (.leaf (16053908197/7812500000 : ℚ)) (.leaf (2054900278157/1000000000000 : ℚ))) (.split (.leaf (2054900307259/1000000000000 : ℚ)) (.leaf (2054900336509/1000000000000 : ℚ)))) (.split (.split (.leaf (513725091481/250000000000 : ℚ)) (.leaf (64215637359/31250000000 : ℚ))) (.split (.leaf (2054900425213/1000000000000 : ℚ)) (.leaf (1027450227557/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054900485147/1000000000000 : ℚ)) (.leaf (256862564417/125000000000 : ℚ))) (.split (.leaf (64215642053/31250000000 : ℚ)) (.leaf (1027450288103/500000000000 : ℚ)))) (.split (.split (.leaf (256862575861/125000000000 : ℚ)) (.leaf (205490063771/100000000000 : ℚ))) (.split (.leaf (1027450334349/500000000000 : ℚ)) (.leaf (2054900699843/1000000000000 : ℚ))))))

theorem cover8_tree0076_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0076 (2103/16384 : ℚ) (263/2048 : ℚ) := by
  unfold cover8_tree0076
  refine tree_all_split_at (4207/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8413/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16825/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33649/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1216_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1217_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33651/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1218_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1219_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16827/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33653/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1220_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1221_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33655/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1222_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1223_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8415/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16829/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33657/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1224_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1225_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33659/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1226_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1227_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16831/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33661/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1228_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1229_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33663/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1230_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1231_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0076_checked
#print axioms SmaleRate.Proofs.cover8_tree0076_checked
