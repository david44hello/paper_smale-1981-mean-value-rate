/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0001
import SmaleRate.Proofs.Generated.D8Chunk0002

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0004 : BoxTree := (.split (.split (.split (.leaf (128437737469/62500000000 : ℚ)) (.leaf (513743706407/250000000000 : ℚ))) (.split (.leaf (1027473301521/500000000000 : ℚ)) (.leaf (410983825799/200000000000 : ℚ)))) (.split (.split (.split (.leaf (205515653009/100000000000 : ℚ)) (.leaf (2055143257383/1000000000000 : ℚ))) (.split (.leaf (64222817827/31250000000 : ℚ)) (.leaf (2055117269001/1000000000000 : ℚ)))) (.split (.split (.leaf (2055104552637/1000000000000 : ℚ)) (.leaf (411018404209/200000000000 : ℚ))) (.split (.leaf (2055079673897/1000000000000 : ℚ)) (.leaf (2055067510841/1000000000000 : ℚ))))))

theorem cover8_tree0004_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0004 (15/128 : ℚ) (61/512 : ℚ) := by
  unfold cover8_tree0004
  refine tree_all_split_at (121/1024 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (241/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (481/4096 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf0045_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf0046_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (483/4096 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf0047_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf0048_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (243/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (485/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (969/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0049_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0050_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (971/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0051_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0052_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (487/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (973/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0053_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0054_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (975/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0055_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0056_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0004_checked
#print axioms SmaleRate.Proofs.cover8_tree0004_checked
