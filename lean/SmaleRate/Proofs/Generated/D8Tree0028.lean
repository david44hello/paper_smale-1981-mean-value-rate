/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0017
public import SmaleRate.Proofs.Generated.D8Chunk0018

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0028 : BoxTree := (.split (.split (.split (.split (.leaf (2054902577637/1000000000000 : ℚ)) (.leaf (256862817227/125000000000 : ℚ))) (.split (.leaf (410980499633/200000000000 : ℚ)) (.leaf (64215701833/31250000000 : ℚ)))) (.split (.split (.leaf (1027451209663/500000000000 : ℚ)) (.leaf (2054902380149/1000000000000 : ℚ))) (.split (.leaf (2054902341127/1000000000000 : ℚ)) (.leaf (513725575571/250000000000 : ℚ))))) (.split (.split (.split (.leaf (410980452719/200000000000 : ℚ)) (.leaf (1027451112531/500000000000 : ℚ))) (.split (.leaf (2054902186689/1000000000000 : ℚ)) (.leaf (2054902148469/1000000000000 : ℚ)))) (.split (.split (.leaf (2054902110429/1000000000000 : ℚ)) (.leaf (2054902072529/1000000000000 : ℚ))) (.split (.leaf (2054902034797/1000000000000 : ℚ)) (.leaf (513725499311/250000000000 : ℚ))))))

theorem cover8_tree0028_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0028 (519/4096 : ℚ) (2077/16384 : ℚ) := by
  unfold cover8_tree0028
  refine tree_all_split_at (4153/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8305/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16609/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33217/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0436_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0437_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33219/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0438_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0439_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16611/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33221/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0440_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0441_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33223/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0442_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0443_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8307/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16613/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33225/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0444_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0445_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33227/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0446_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0447_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16615/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33229/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0448_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0449_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33231/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0450_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0451_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0028_checked
#print axioms SmaleRate.Proofs.cover8_tree0028_checked
