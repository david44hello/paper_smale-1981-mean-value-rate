/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0057
public import SmaleRate.Proofs.Generated.D8Chunk0058

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0090 : BoxTree := (.split (.split (.split (.split (.leaf (2054906126439/1000000000000 : ℚ)) (.leaf (64215820931/31250000000 : ℚ))) (.split (.leaf (205490641377/100000000000 : ℚ)) (.leaf (2054906558369/1000000000000 : ℚ)))) (.split (.split (.leaf (205490670359/100000000000 : ℚ)) (.leaf (102745342471/50000000000 : ℚ))) (.split (.leaf (513726748971/250000000000 : ℚ)) (.leaf (410981428591/200000000000 : ℚ))))) (.split (.split (.split (.leaf (2054907290647/1000000000000 : ℚ)) (.leaf (2054907438963/1000000000000 : ℚ))) (.split (.leaf (2054907587901/1000000000000 : ℚ)) (.leaf (2054907737459/1000000000000 : ℚ)))) (.split (.split (.leaf (513726971909/250000000000 : ℚ)) (.leaf (2054908038441/1000000000000 : ℚ))) (.split (.leaf (1027454094923/500000000000 : ℚ)) (.leaf (513727085473/250000000000 : ℚ))))))

theorem cover8_tree0090_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0090 (265/2048 : ℚ) (1061/8192 : ℚ) := by
  unfold cover8_tree0090
  refine tree_all_split_at (2121/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4241/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8481/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16961/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1441_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1442_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16963/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1443_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1444_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8483/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16965/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1445_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1446_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16967/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1447_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1448_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4243/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8485/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16969/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1449_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1450_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16971/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1451_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1452_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8487/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16973/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1453_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1454_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16975/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1455_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1456_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0090_checked
#print axioms SmaleRate.Proofs.cover8_tree0090_checked
