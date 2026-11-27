/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0002
public import SmaleRate.Proofs.Generated.D7Chunk0003

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0006 : BoxTree := (.split (.split (.split (.split (.leaf (2019057795051/1000000000000 : ℚ)) (.leaf (1009524383863/500000000000 : ℚ))) (.split (.leaf (2019039902333/1000000000000 : ℚ)) (.leaf (504757799659/250000000000 : ℚ)))) (.split (.split (.leaf (2019022656323/1000000000000 : ℚ)) (.leaf (2019014275163/1000000000000 : ℚ))) (.split (.leaf (2019006054871/1000000000000 : ℚ)) (.split (.leaf (2019125238821/1000000000000 : ℚ)) (.leaf (201912122879/100000000000 : ℚ)))))) (.split (.split (.split (.split (.leaf (2019117258847/1000000000000 : ℚ)) (.leaf (40382266579/20000000000 : ℚ))) (.split (.leaf (504777359769/250000000000 : ℚ)) (.leaf (31548524831/15625000000 : ℚ)))) (.split (.split (.leaf (2019101779247/1000000000000 : ℚ)) (.leaf (50477450231/25000000000 : ℚ))) (.split (.leaf (1009547139563/500000000000 : ℚ)) (.leaf (252386323607/125000000000 : ℚ))))) (.split (.split (.split (.leaf (1009543469201/500000000000 : ℚ)) (.leaf (1009541663869/500000000000 : ℚ))) (.split (.leaf (2019079756839/1000000000000 : ℚ)) (.leaf (252384528209/125000000000 : ℚ)))) (.split (.split (.leaf (1009536367091/500000000000 : ℚ)) (.leaf (504767320591/250000000000 : ℚ))) (.split (.leaf (2019065870153/1000000000000 : ℚ)) (.leaf (403812499509/200000000000 : ℚ)))))))

theorem cover7_tree0006_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0006 (33/256 : ℚ) (67/512 : ℚ) := by
  unfold cover7_tree0006
  refine tree_all_split_at (133/1024 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (265/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (529/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1057/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0069_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0070_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1059/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0071_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0072_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (531/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1061/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0073_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0074_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1063/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0075_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (2127/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0076_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0077_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (267/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (533/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1065/8192 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (2129/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0078_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0079_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (2131/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0080_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0081_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1067/8192 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (2133/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0082_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0083_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (2135/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0084_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0085_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (535/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1069/8192 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (2137/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0086_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0087_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (2139/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0088_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0089_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1071/8192 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (2141/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0090_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0091_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (2143/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0092_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0093_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0006_checked
#print axioms SmaleRate.Proofs.cover7_tree0006_checked
