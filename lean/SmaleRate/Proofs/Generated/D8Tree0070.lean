/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0044
public import SmaleRate.Proofs.Generated.D8Chunk0045

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0070 : BoxTree := (.split (.split (.split (.split (.leaf (128431424339/62500000000 : ℚ)) (.leaf (256862849927/125000000000 : ℚ))) (.split (.leaf (2054902809453/1000000000000 : ℚ)) (.leaf (256862852441/125000000000 : ℚ)))) (.split (.split (.leaf (2054902829643/1000000000000 : ℚ)) (.leaf (205490283979/100000000000 : ℚ))) (.split (.leaf (1027451424999/500000000000 : ℚ)) (.leaf (32107857191/15625000000 : ℚ))))) (.split (.split (.split (.leaf (1027451435253/500000000000 : ℚ)) (.leaf (2054902880817/1000000000000 : ℚ))) (.split (.leaf (82196115647/40000000000 : ℚ)) (.leaf (2054902901557/1000000000000 : ℚ)))) (.split (.split (.leaf (1027451455997/500000000000 : ℚ)) (.leaf (2054902922471/1000000000000 : ℚ))) (.split (.leaf (256862866621/125000000000 : ℚ)) (.leaf (1027451471761/500000000000 : ℚ))))))

theorem cover8_tree0070_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0070 (4199/32768 : ℚ) (525/4096 : ℚ) := by
  unfold cover8_tree0070
  refine tree_all_split_at (8399/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16797/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33593/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67185/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1112_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1113_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67187/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1114_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1115_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33595/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67189/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1116_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1117_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67191/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1118_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1119_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16799/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33597/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67193/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1120_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1121_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67195/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1122_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1123_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33599/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67197/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1124_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1125_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67199/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1126_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1127_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0070_checked
#print axioms SmaleRate.Proofs.cover8_tree0070_checked
