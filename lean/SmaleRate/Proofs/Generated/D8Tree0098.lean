/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0062
public import SmaleRate.Proofs.Generated.D8Chunk0063

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0098 : BoxTree := (.split (.split (.split (.split (.split (.leaf (2054929539377/1000000000000 : ℚ)) (.leaf (1027465031953/500000000000 : ℚ))) (.split (.leaf (51373264771/25000000000 : ℚ)) (.leaf (2054931120233/1000000000000 : ℚ)))) (.split (.leaf (2054900830749/1000000000000 : ℚ)) (.leaf (2054901906523/1000000000000 : ℚ)))) (.split (.split (.leaf (2054902992011/1000000000000 : ℚ)) (.leaf (205490408723/100000000000 : ℚ))) (.split (.leaf (2054905192159/1000000000000 : ℚ)) (.leaf (2054906306789/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (513726857781/250000000000 : ℚ)) (.leaf (513727141293/250000000000 : ℚ))) (.split (.leaf (128431856807/62500000000 : ℚ)) (.leaf (1027455431179/500000000000 : ℚ)))) (.split (.split (.leaf (2054912025473/1000000000000 : ℚ)) (.leaf (513728299571/250000000000 : ℚ))) (.split (.leaf (2054914380787/1000000000000 : ℚ)) (.leaf (256864446619/125000000000 : ℚ))))))

theorem cover8_tree0098_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0098 (67/512 : ℚ) (269/2048 : ℚ) := by
  unfold cover8_tree0098
  refine tree_all_split_at (537/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1073/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2145/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4289/32768 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (8577/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1567_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1568_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (8579/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1569_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1570_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4291/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1571_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1572_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2147/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4293/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1573_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1574_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4295/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1575_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1576_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1075/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2149/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4297/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1577_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1578_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4299/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1579_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1580_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2151/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4301/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1581_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1582_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4303/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1583_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1584_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0098_checked
#print axioms SmaleRate.Proofs.cover8_tree0098_checked
