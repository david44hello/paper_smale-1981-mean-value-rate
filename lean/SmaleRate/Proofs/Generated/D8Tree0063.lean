/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0040

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0063 : BoxTree := (.split (.split (.split (.split (.leaf (5137254799/2500000000 : ℚ)) (.leaf (256862740647/125000000000 : ℚ))) (.split (.leaf (256862741349/125000000000 : ℚ)) (.leaf (1027450968223/500000000000 : ℚ)))) (.split (.split (.leaf (410980388427/200000000000 : ℚ)) (.leaf (513725486967/250000000000 : ℚ))) (.split (.leaf (2054901953633/1000000000000 : ℚ)) (.leaf (2054901959441/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901965287/1000000000000 : ℚ)) (.leaf (2054901971173/1000000000000 : ℚ))) (.split (.leaf (2054901977093/1000000000000 : ℚ)) (.leaf (1027450991537/500000000000 : ℚ)))) (.split (.split (.leaf (2054901989073/1000000000000 : ℚ)) (.leaf (205490199513/100000000000 : ℚ))) (.split (.leaf (256862750151/125000000000 : ℚ)) (.leaf (2054902007341/1000000000000 : ℚ))))))

theorem cover8_tree0063_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0063 (131/1024 : ℚ) (4193/32768 : ℚ) := by
  unfold cover8_tree0063
  refine tree_all_split_at (8385/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16769/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33537/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67073/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1000_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1001_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67075/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1002_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1003_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33539/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67077/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1004_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1005_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67079/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1006_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1007_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16771/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33541/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67081/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1008_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1009_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67083/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1010_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1011_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33543/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67085/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1012_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1013_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67087/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1014_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1015_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0063_checked
#print axioms SmaleRate.Proofs.cover8_tree0063_checked
