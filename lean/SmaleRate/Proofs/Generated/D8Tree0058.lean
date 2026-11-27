/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0036
import SmaleRate.Proofs.Generated.D8Chunk0037

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0058 : BoxTree := (.split (.split (.split (.split (.leaf (1027450801089/500000000000 : ℚ)) (.leaf (82196064183/40000000000 : ℚ))) (.split (.leaf (1027450803503/500000000000 : ℚ)) (.leaf (2054901609499/1000000000000 : ℚ)))) (.split (.split (.leaf (1027450806007/500000000000 : ℚ)) (.leaf (1027450807291/500000000000 : ℚ))) (.split (.leaf (513725404293/250000000000 : ℚ)) (.leaf (102745080991/50000000000 : ℚ))))) (.split (.split (.split (.leaf (410980324501/200000000000 : ℚ)) (.leaf (2054901625213/1000000000000 : ℚ))) (.split (.leaf (1027450813987/500000000000 : ℚ)) (.leaf (256862703847/125000000000 : ℚ)))) (.split (.split (.leaf (410980326723/200000000000 : ℚ)) (.leaf (410980327299/200000000000 : ℚ))) (.split (.leaf (2054901639413/1000000000000 : ℚ)) (.leaf (2054901642367/1000000000000 : ℚ))))))

theorem cover8_tree0058_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0058 (4187/32768 : ℚ) (1047/8192 : ℚ) := by
  unfold cover8_tree0058
  refine tree_all_split_at (8375/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16749/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33497/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66993/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0920_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0921_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66995/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0922_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0923_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33499/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66997/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0924_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0925_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66999/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0926_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0927_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16751/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33501/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67001/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0928_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0929_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67003/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0930_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0931_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33503/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67005/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0932_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0933_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67007/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0934_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0935_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0058_checked
#print axioms SmaleRate.Proofs.cover8_tree0058_checked
