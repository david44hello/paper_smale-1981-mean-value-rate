/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0025
public import SmaleRate.Proofs.Generated.D8Chunk0026

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0041 : BoxTree := (.split (.split (.split (.split (.leaf (2054902424661/1000000000000 : ℚ)) (.leaf (2054902416237/1000000000000 : ℚ))) (.split (.leaf (41098048157/20000000000 : ℚ)) (.leaf (128431399969/62500000000 : ℚ)))) (.split (.split (.leaf (513725597799/250000000000 : ℚ)) (.leaf (64215699467/31250000000 : ℚ))) (.split (.leaf (1027451187357/500000000000 : ℚ)) (.leaf (51372559163/25000000000 : ℚ))))) (.split (.split (.split (.leaf (513725589597/250000000000 : ℚ)) (.leaf (82196094011/40000000000 : ℚ))) (.split (.leaf (2054902342221/1000000000000 : ℚ)) (.leaf (513725583551/250000000000 : ℚ)))) (.split (.split (.leaf (2054902326207/1000000000000 : ℚ)) (.leaf (1027451159131/500000000000 : ℚ))) (.split (.leaf (1027451155181/500000000000 : ℚ)) (.leaf (1027451151251/500000000000 : ℚ))))))

theorem cover8_tree0041_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0041 (2085/16384 : ℚ) (4171/32768 : ℚ) := by
  unfold cover8_tree0041
  refine tree_all_split_at (8341/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16681/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33361/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66721/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0648_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0649_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66723/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0650_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0651_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33363/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66725/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0652_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0653_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66727/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0654_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0655_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16683/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33365/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66729/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0656_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0657_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66731/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0658_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0659_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33367/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66733/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0660_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0661_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66735/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0662_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0663_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0041_checked
#print axioms SmaleRate.Proofs.cover8_tree0041_checked
