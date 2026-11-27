/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0006
import SmaleRate.Proofs.Generated.D8Chunk0007

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0012 : BoxTree := (.split (.split (.split (.split (.leaf (205492041393/100000000000 : ℚ)) (.leaf (205491992341/100000000000 : ℚ))) (.split (.leaf (128432464721/62500000000 : ℚ)) (.leaf (2054918950299/1000000000000 : ℚ)))) (.split (.split (.leaf (51372961693/25000000000 : ℚ)) (.leaf (513729496941/250000000000 : ℚ))) (.split (.leaf (513729377617/250000000000 : ℚ)) (.leaf (2054917035819/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054916563803/1000000000000 : ℚ)) (.leaf (51372902361/25000000000 : ℚ))) (.split (.leaf (410983125541/200000000000 : ℚ)) (.leaf (64216098863/31250000000 : ℚ)))) (.split (.split (.leaf (2054914702183/1000000000000 : ℚ)) (.leaf (205491424337/100000000000 : ℚ))) (.split (.leaf (205491378721/100000000000 : ℚ)) (.leaf (2054913333677/1000000000000 : ℚ))))))

theorem cover8_tree0012_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0012 (511/4096 : ℚ) (1/8 : ℚ) := by
  unfold cover8_tree0012
  refine tree_all_split_at (1023/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2045/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4089/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8177/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0174_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0175_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8179/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0176_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0177_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4091/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8181/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0178_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0179_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8183/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0180_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0181_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2047/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4093/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8185/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0182_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0183_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8187/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0184_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0185_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4095/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8189/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0186_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0187_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8191/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0188_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0189_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0012_checked
#print axioms SmaleRate.Proofs.cover8_tree0012_checked
