/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0015
public import SmaleRate.Proofs.Generated.D8Chunk0016

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0025 : BoxTree := (.split (.split (.split (.split (.leaf (410980935701/200000000000 : ℚ)) (.leaf (2054904630939/1000000000000 : ℚ))) (.split (.leaf (410980916707/200000000000 : ℚ)) (.leaf (128431533519/62500000000 : ℚ)))) (.split (.split (.leaf (513726122307/250000000000 : ℚ)) (.leaf (205490444233/100000000000 : ℚ))) (.split (.leaf (2054904395571/1000000000000 : ℚ)) (.leaf (2054904348989/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054904302557/1000000000000 : ℚ)) (.leaf (2054904256291/1000000000000 : ℚ))) (.split (.leaf (1027452105089/500000000000 : ℚ)) (.leaf (2054904164237/1000000000000 : ℚ)))) (.split (.split (.leaf (32107876851/15625000000 : ℚ)) (.leaf (1027452036419/500000000000 : ℚ))) (.split (.leaf (1027452013687/500000000000 : ℚ)) (.leaf (1027451991041/500000000000 : ℚ))))))

theorem cover8_tree0025_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0025 (2073/16384 : ℚ) (1037/8192 : ℚ) := by
  unfold cover8_tree0025
  refine tree_all_split_at (4147/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8293/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16585/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33169/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0388_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0389_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33171/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0390_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0391_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16587/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33173/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0392_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0393_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33175/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0394_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0395_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8295/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16589/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33177/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0396_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0397_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33179/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0398_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0399_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16591/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33181/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0400_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0401_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33183/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0402_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0403_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0025_checked
#print axioms SmaleRate.Proofs.cover8_tree0025_checked
