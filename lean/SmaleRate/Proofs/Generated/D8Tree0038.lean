/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0024

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0038 : BoxTree := (.split (.split (.split (.split (.leaf (51372571899/25000000000 : ℚ)) (.leaf (1027451432807/500000000000 : ℚ))) (.split (.leaf (2054902855323/1000000000000 : ℚ)) (.leaf (513725711263/250000000000 : ℚ)))) (.split (.split (.leaf (513725708709/250000000000 : ℚ)) (.leaf (2054902824661/1000000000000 : ℚ))) (.split (.leaf (2054902814507/1000000000000 : ℚ)) (.leaf (2054902804411/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054902794353/1000000000000 : ℚ)) (.leaf (410980556867/200000000000 : ℚ))) (.split (.leaf (1027451387177/500000000000 : ℚ)) (.leaf (2054902764411/1000000000000 : ℚ)))) (.split (.split (.leaf (205490275451/100000000000 : ℚ)) (.leaf (513725686161/250000000000 : ℚ))) (.split (.leaf (1027451367411/500000000000 : ℚ)) (.leaf (513725681259/250000000000 : ℚ))))))

theorem cover8_tree0038_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0038 (4167/32768 : ℚ) (521/4096 : ℚ) := by
  unfold cover8_tree0038
  refine tree_all_split_at (8335/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16669/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33337/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66673/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0600_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0601_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66675/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0602_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0603_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33339/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66677/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0604_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0605_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66679/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0606_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0607_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16671/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33341/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66681/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0608_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0609_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66683/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0610_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0611_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33343/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66685/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0612_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0613_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66687/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0614_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0615_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0038_checked
#print axioms SmaleRate.Proofs.cover8_tree0038_checked
