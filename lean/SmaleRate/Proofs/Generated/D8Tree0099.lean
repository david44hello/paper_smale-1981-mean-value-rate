/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0063
public import SmaleRate.Proofs.Generated.D8Chunk0064

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0099 : BoxTree := (.split (.split (.split (.split (.leaf (2054916774799/1000000000000 : ℚ)) (.leaf (2054917986331/1000000000000 : ℚ))) (.split (.leaf (513729801877/250000000000 : ℚ)) (.leaf (1027460219179/500000000000 : ℚ)))) (.split (.split (.leaf (2054921678877/1000000000000 : ℚ)) (.leaf (205492292903/100000000000 : ℚ))) (.split (.leaf (513731047211/250000000000 : ℚ)) (.leaf (2054925458301/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054926737417/1000000000000 : ℚ)) (.leaf (1027464013071/500000000000 : ℚ))) (.split (.leaf (2054929324541/1000000000000 : ℚ)) (.leaf (2054930632541/1000000000000 : ℚ)))) (.split (.split (.leaf (1027465975091/500000000000 : ℚ)) (.leaf (2054933277447/1000000000000 : ℚ))) (.split (.leaf (2054934614319/1000000000000 : ℚ)) (.leaf (1027467980411/500000000000 : ℚ))))))

theorem cover8_tree0099_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0099 (269/2048 : ℚ) (135/1024 : ℚ) := by
  unfold cover8_tree0099
  refine tree_all_split_at (539/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1077/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2153/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4305/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1585_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1586_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4307/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1587_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1588_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2155/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4309/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1589_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1590_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4311/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1591_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1592_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1079/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2157/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4313/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1593_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1594_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4315/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1595_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1596_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2159/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4317/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1597_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1598_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4319/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1599_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1600_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0099_checked
#print axioms SmaleRate.Proofs.cover8_tree0099_checked
