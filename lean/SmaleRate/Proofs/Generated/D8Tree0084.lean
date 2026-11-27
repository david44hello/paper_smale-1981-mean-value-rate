/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0053
import SmaleRate.Proofs.Generated.D8Chunk0054

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0084 : BoxTree := (.split (.split (.split (.split (.leaf (1027452614919/500000000000 : ℚ)) (.leaf (41098105577/20000000000 : ℚ))) (.split (.leaf (205490532803/100000000000 : ℚ)) (.leaf (2054905377357/1000000000000 : ℚ)))) (.split (.split (.leaf (2054905426841/1000000000000 : ℚ)) (.leaf (1027452738239/500000000000 : ℚ))) (.split (.leaf (513726381571/250000000000 : ℚ)) (.leaf (2054905576239/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (128431601647/62500000000 : ℚ)) (.leaf (1027452838307/500000000000 : ℚ))) (.split (.leaf (2054905727031/1000000000000 : ℚ)) (.leaf (1027452888807/500000000000 : ℚ)))) (.split (.split (.leaf (1027452914177/500000000000 : ℚ)) (.leaf (1027452939623/500000000000 : ℚ))) (.split (.leaf (1027452965143/500000000000 : ℚ)) (.leaf (2054905981501/1000000000000 : ℚ))))))

theorem cover8_tree0084_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0084 (2111/16384 : ℚ) (33/256 : ℚ) := by
  unfold cover8_tree0084
  refine tree_all_split_at (4223/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8445/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16889/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33777/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1344_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1345_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33779/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1346_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1347_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16891/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33781/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1348_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1349_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33783/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1350_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1351_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8447/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16893/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33785/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1352_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1353_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33787/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1354_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1355_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16895/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33789/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1356_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1357_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33791/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1358_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1359_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0084_checked
#print axioms SmaleRate.Proofs.cover8_tree0084_checked
