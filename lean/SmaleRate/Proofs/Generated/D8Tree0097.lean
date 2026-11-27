/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0062

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0097 : BoxTree := (.split (.split (.split (.split (.leaf (1027460739243/500000000000 : ℚ)) (.leaf (513730491/250000000 : ℚ))) (.split (.leaf (51373061299/25000000000 : ℚ)) (.leaf (2054922942357/1000000000000 : ℚ)))) (.split (.split (.leaf (2054923435179/1000000000000 : ℚ)) (.leaf (1027461965233/500000000000 : ℚ))) (.split (.leaf (410984885637/200000000000 : ℚ)) (.leaf (2054924928329/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027462715459/500000000000 : ℚ)) (.leaf (1027462967977/500000000000 : ℚ))) (.split (.leaf (1027463221709/500000000000 : ℚ)) (.leaf (82197078133/40000000000 : ℚ)))) (.split (.split (.leaf (1027463732831/500000000000 : ℚ)) (.leaf (1027463990221/500000000000 : ℚ))) (.split (.leaf (2054928497659/1000000000000 : ℚ)) (.leaf (513732254327/250000000000 : ℚ))))))

theorem cover8_tree0097_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0097 (535/4096 : ℚ) (67/512 : ℚ) := by
  unfold cover8_tree0097
  refine tree_all_split_at (1071/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2141/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4281/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8561/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1551_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1552_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8563/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1553_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1554_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4283/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8565/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1555_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1556_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8567/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1557_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1558_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2143/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4285/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8569/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1559_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1560_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8571/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1561_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1562_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4287/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8573/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1563_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1564_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8575/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1565_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1566_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0097_checked
#print axioms SmaleRate.Proofs.cover8_tree0097_checked
