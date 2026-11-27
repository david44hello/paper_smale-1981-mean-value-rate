/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0026
import SmaleRate.Proofs.Generated.D8Chunk0027

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0042 : BoxTree := (.split (.split (.split (.split (.leaf (1027451147339/500000000000 : ℚ)) (.leaf (410980457379/200000000000 : ℚ))) (.split (.leaf (41098045583/20000000000 : ℚ)) (.leaf (2054902271447/1000000000000 : ℚ)))) (.split (.split (.leaf (2054902263773/1000000000000 : ℚ)) (.leaf (2054902256153/1000000000000 : ℚ))) (.split (.leaf (1027451124289/500000000000 : ℚ)) (.leaf (2054902241027/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (256862779189/125000000000 : ℚ)) (.leaf (1027451113029/500000000000 : ℚ))) (.split (.leaf (2054902218629/1000000000000 : ℚ)) (.leaf (2054902211249/1000000000000 : ℚ)))) (.split (.split (.leaf (513725550973/250000000000 : ℚ)) (.leaf (513725549149/250000000000 : ℚ))) (.split (.leaf (410980437867/200000000000 : ℚ)) (.leaf (410980436419/200000000000 : ℚ))))))

theorem cover8_tree0042_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0042 (4171/32768 : ℚ) (1043/8192 : ℚ) := by
  unfold cover8_tree0042
  refine tree_all_split_at (8343/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16685/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33369/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66737/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0664_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0665_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66739/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0666_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0667_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33371/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66741/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0668_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0669_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66743/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0670_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0671_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16687/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33373/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66745/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0672_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0673_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66747/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0674_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0675_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33375/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66749/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0676_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0677_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66751/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0678_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0679_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0042_checked
#print axioms SmaleRate.Proofs.cover8_tree0042_checked
