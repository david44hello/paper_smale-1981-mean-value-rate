/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0018
public import SmaleRate.Proofs.Generated.D8Chunk0019

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0030 : BoxTree := (.split (.split (.split (.split (.leaf (256862672899/125000000000 : ℚ)) (.leaf (1027450674263/500000000000 : ℚ))) (.split (.leaf (205490131401/100000000000 : ℚ)) (.leaf (2054901279661/1000000000000 : ℚ)))) (.split (.split (.leaf (205490124547/100000000000 : ℚ)) (.leaf (2054901211437/1000000000000 : ℚ))) (.split (.leaf (2054901177559/1000000000000 : ℚ)) (.leaf (2054901143859/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901110311/1000000000000 : ℚ)) (.leaf (1027450538461/500000000000 : ℚ))) (.split (.leaf (205490104369/100000000000 : ℚ)) (.leaf (256862626329/125000000000 : ℚ)))) (.split (.split (.leaf (2054900977733/1000000000000 : ℚ)) (.leaf (2054900944989/1000000000000 : ℚ))) (.split (.leaf (2054900912397/1000000000000 : ℚ)) (.leaf (2054900879967/1000000000000 : ℚ))))))

theorem cover8_tree0030_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0030 (1039/8192 : ℚ) (2079/16384 : ℚ) := by
  unfold cover8_tree0030
  refine tree_all_split_at (4157/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8313/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16625/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33249/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0468_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0469_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33251/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0470_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0471_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16627/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33253/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0472_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0473_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33255/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0474_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0475_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8315/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16629/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33257/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0476_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0477_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33259/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0478_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0479_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16631/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33261/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0480_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0481_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33263/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0482_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0483_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0030_checked
#print axioms SmaleRate.Proofs.cover8_tree0030_checked
