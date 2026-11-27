/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0000
public import SmaleRate.Proofs.Generated.D8Chunk0001

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0003 : BoxTree := (.split (.split (.split (.split (.leaf (1027894266209/500000000000 : ℚ)) (.leaf (513920486453/250000000000 : ℚ))) (.split (.leaf (2055578728317/1000000000000 : ℚ)) (.leaf (1027739426699/500000000000 : ℚ)))) (.split (.split (.leaf (2055382294903/1000000000000 : ℚ)) (.leaf (513822256749/250000000000 : ℚ))) (.split (.leaf (2055199024161/1000000000000 : ℚ)) (.leaf (411022452243/200000000000 : ℚ))))) (.split (.split (.split (.leaf (411005742651/200000000000 : ℚ)) (.leaf (513737088933/250000000000 : ℚ))) (.split (.split (.leaf (1027705556943/500000000000 : ℚ)) (.leaf (2055372903141/1000000000000 : ℚ))) (.split (.leaf (1027667739067/500000000000 : ℚ)) (.leaf (2055298835913/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2055262973489/1000000000000 : ℚ)) (.leaf (2055227887961/1000000000000 : ℚ))) (.split (.leaf (411038715283/200000000000 : ℚ)) (.leaf (2055160035929/1000000000000 : ℚ)))) (.split (.split (.leaf (2055127263647/1000000000000 : ℚ)) (.leaf (2055095256699/1000000000000 : ℚ))) (.split (.leaf (513766003057/250000000000 : ℚ)) (.leaf (2055033527443/1000000000000 : ℚ)))))))

theorem cover8_tree0003_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0003 (7/64 : ℚ) (15/128 : ℚ) := by
  unfold cover8_tree0003
  refine tree_all_split_at (29/256 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (57/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (113/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (225/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0023_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0024_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (227/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0025_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0026_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (115/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (229/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0027_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0028_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (231/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0029_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0030_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (59/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (117/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (233/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0031_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0032_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (235/2048 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (469/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0033_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0034_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (471/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0035_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0036_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (119/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (237/2048 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (473/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0037_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0038_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (475/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0039_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0040_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (239/2048 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (477/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0041_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0042_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (479/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0043_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0044_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0003_checked
#print axioms SmaleRate.Proofs.cover8_tree0003_checked
