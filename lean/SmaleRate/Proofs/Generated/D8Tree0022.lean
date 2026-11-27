/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0013
import SmaleRate.Proofs.Generated.D8Chunk0014

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0022 : BoxTree := (.split (.split (.split (.split (.leaf (2054907151201/1000000000000 : ℚ)) (.leaf (1027453547947/500000000000 : ℚ))) (.split (.leaf (410981408149/200000000000 : ℚ)) (.leaf (256863373219/125000000000 : ℚ)))) (.split (.split (.leaf (2054906930921/1000000000000 : ℚ)) (.leaf (2054906876259/1000000000000 : ℚ))) (.split (.leaf (3210791909/1562500000 : ℚ)) (.leaf (10274533837/5000000000 : ℚ))))) (.split (.split (.split (.leaf (2054906713231/1000000000000 : ℚ)) (.leaf (513726664801/250000000000 : ℚ))) (.split (.leaf (2054906605351/1000000000000 : ℚ)) (.leaf (2054906551657/1000000000000 : ℚ)))) (.split (.split (.leaf (2054906498117/1000000000000 : ℚ)) (.leaf (2054906444739/1000000000000 : ℚ))) (.split (.leaf (1027453195769/500000000000 : ℚ)) (.leaf (2054906338477/1000000000000 : ℚ))))))

theorem cover8_tree0022_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0022 (1035/8192 : ℚ) (2071/16384 : ℚ) := by
  unfold cover8_tree0022
  refine tree_all_split_at (4141/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8281/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16561/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33121/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0340_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0341_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33123/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0342_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0343_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16563/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33125/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0344_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0345_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33127/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0346_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0347_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8283/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16565/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33129/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0348_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0349_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33131/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0350_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0351_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16567/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33133/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0352_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0353_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33135/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0354_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0355_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0022_checked
#print axioms SmaleRate.Proofs.cover8_tree0022_checked
