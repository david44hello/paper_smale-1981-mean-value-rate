/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0006

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0011 : BoxTree := (.split (.split (.split (.split (.leaf (256866077829/125000000000 : ℚ)) (.leaf (2054928089697/1000000000000 : ℚ))) (.split (.leaf (1027463779703/500000000000 : ℚ)) (.leaf (2054927031779/1000000000000 : ℚ)))) (.split (.split (.leaf (2054926506811/1000000000000 : ℚ)) (.leaf (256865748061/125000000000 : ℚ))) (.split (.leaf (205492546481/100000000000 : ℚ)) (.leaf (2054924947803/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (513731108361/250000000000 : ℚ)) (.leaf (513730980431/250000000000 : ℚ))) (.split (.leaf (1027461706329/500000000000 : ℚ)) (.leaf (2054922906253/1000000000000 : ℚ)))) (.split (.split (.leaf (2054922402493/1000000000000 : ℚ)) (.leaf (102746095069/50000000000 : ℚ))) (.split (.leaf (513730350727/250000000000 : ℚ)) (.leaf (256865113387/125000000000 : ℚ))))))

theorem cover8_tree0011_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0011 (255/2048 : ℚ) (511/4096 : ℚ) := by
  unfold cover8_tree0011
  refine tree_all_split_at (1021/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2041/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4081/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8161/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0158_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0159_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8163/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0160_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0161_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4083/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8165/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0162_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0163_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8167/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0164_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0165_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2043/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4085/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8169/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0166_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0167_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8171/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0168_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0169_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4087/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8173/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0170_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0171_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8175/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0172_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0173_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0011_checked
#print axioms SmaleRate.Proofs.cover8_tree0011_checked
