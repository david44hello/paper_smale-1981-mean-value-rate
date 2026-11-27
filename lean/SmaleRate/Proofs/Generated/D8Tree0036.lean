/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0022
public import SmaleRate.Proofs.Generated.D8Chunk0023

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0036 : BoxTree := (.split (.split (.split (.split (.leaf (410980645603/200000000000 : ℚ)) (.leaf (1027451608199/500000000000 : ℚ))) (.split (.leaf (102745160241/50000000000 : ℚ)) (.leaf (2054903193267/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903181767/1000000000000 : ℚ)) (.leaf (513725792577/250000000000 : ℚ))) (.split (.leaf (256862894861/125000000000 : ℚ)) (.leaf (2054903147507/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054903136163/1000000000000 : ℚ)) (.leaf (2054903124863/1000000000000 : ℚ))) (.split (.leaf (2054903113599/1000000000000 : ℚ)) (.leaf (1027451551187/500000000000 : ℚ)))) (.split (.split (.leaf (410980618241/200000000000 : ℚ)) (.leaf (2054903080059/1000000000000 : ℚ))) (.split (.leaf (2054903068951/1000000000000 : ℚ)) (.leaf (2054903057901/1000000000000 : ℚ))))))

theorem cover8_tree0036_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0036 (4165/32768 : ℚ) (2083/16384 : ℚ) := by
  unfold cover8_tree0036
  refine tree_all_split_at (8331/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16661/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33321/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66641/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0568_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0569_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66643/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0570_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0571_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33323/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66645/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0572_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0573_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66647/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0574_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0575_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16663/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33325/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66649/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0576_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0577_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66651/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0578_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0579_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33327/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66653/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0580_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0581_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66655/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0582_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0583_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0036_checked
#print axioms SmaleRate.Proofs.cover8_tree0036_checked
