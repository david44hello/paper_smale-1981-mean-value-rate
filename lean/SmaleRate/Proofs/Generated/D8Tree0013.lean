/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0007
import SmaleRate.Proofs.Generated.D8Chunk0008

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0013 : BoxTree := (.split (.split (.split (.split (.leaf (1027456441393/500000000000 : ℚ)) (.leaf (82196497381/40000000000 : ℚ))) (.split (.leaf (2054911988909/1000000000000 : ℚ)) (.leaf (1027455772967/500000000000 : ℚ)))) (.split (.split (.leaf (205491110559/100000000000 : ℚ)) (.leaf (2054910667887/1000000000000 : ℚ))) (.split (.leaf (1027455116403/500000000000 : ℚ)) (.leaf (128431862523/62500000000 : ℚ))))) (.split (.split (.split (.leaf (513727342643/250000000000 : ℚ)) (.leaf (2054908943397/1000000000000 : ℚ))) (.split (.leaf (2054908518847/1000000000000 : ℚ)) (.leaf (1027454048477/500000000000 : ℚ)))) (.split (.split (.leaf (2054907677659/1000000000000 : ℚ)) (.leaf (102745363051/50000000000 : ℚ))) (.split (.leaf (1027453423503/500000000000 : ℚ)) (.leaf (2054906435609/1000000000000 : ℚ))))))

theorem cover8_tree0013_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0013 (1/8 : ℚ) (513/4096 : ℚ) := by
  unfold cover8_tree0013
  refine tree_all_split_at (1025/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2049/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4097/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8193/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0190_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0191_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8195/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0192_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0193_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4099/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8197/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0194_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0195_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8199/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0196_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0197_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2051/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4101/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8201/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0198_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0199_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8203/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0200_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0201_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4103/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8205/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0202_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0203_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8207/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0204_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0205_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0013_checked
#print axioms SmaleRate.Proofs.cover8_tree0013_checked
