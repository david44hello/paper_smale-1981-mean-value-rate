/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0003
public import SmaleRate.Proofs.Generated.D8Chunk0004

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0007 : BoxTree := (.split (.split (.split (.split (.leaf (2054951538677/1000000000000 : ℚ)) (.leaf (410989545423/200000000000 : ℚ))) (.split (.leaf (51373598987/25000000000 : ℚ)) (.leaf (8219760943/4000000000 : ℚ)))) (.split (.split (.leaf (64216767371/31250000000 : ℚ)) (.leaf (410986583961/200000000000 : ℚ))) (.split (.leaf (2054929327529/1000000000000 : ℚ)) (.leaf (513731444747/250000000000 : ℚ))))) (.split (.split (.split (.leaf (41098445483/20000000000 : ℚ)) (.leaf (1027459406489/500000000000 : ℚ))) (.split (.leaf (2054915395431/1000000000000 : ℚ)) (.leaf (2054912021461/1000000000000 : ℚ)))) (.split (.split (.leaf (2054908691053/1000000000000 : ℚ)) (.leaf (1027452702077/500000000000 : ℚ))) (.split (.leaf (2054902160721/1000000000000 : ℚ)) (.split (.leaf (1027481633423/500000000000 : ℚ)) (.leaf (513740418057/250000000000 : ℚ)))))))

theorem cover8_tree0007_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0007 (125/1024 : ℚ) (63/512 : ℚ) := by
  unfold cover8_tree0007
  refine tree_all_split_at (251/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (501/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1001/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2001/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0090_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0091_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2003/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0092_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0093_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1003/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2005/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0094_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0095_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2007/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0096_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0097_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (503/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1005/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2009/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0098_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0099_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2011/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0100_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0101_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1007/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2013/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0102_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0103_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2015/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0104_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (4031/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0105_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0106_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0007_checked
#print axioms SmaleRate.Proofs.cover8_tree0007_checked
