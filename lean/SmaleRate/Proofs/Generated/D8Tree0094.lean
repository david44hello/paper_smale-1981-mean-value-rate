/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0060

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0094 : BoxTree := (.split (.split (.split (.split (.leaf (2054901054807/1000000000000 : ℚ)) (.leaf (1027450711279/500000000000 : ℚ))) (.split (.leaf (410980358549/200000000000 : ℚ)) (.leaf (102745108271/50000000000 : ℚ)))) (.split (.split (.leaf (2054902540549/1000000000000 : ℚ)) (.leaf (2054902918137/1000000000000 : ℚ))) (.split (.leaf (128431456137/62500000000 : ℚ)) (.leaf (1027451840359/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054904065697/1000000000000 : ℚ)) (.leaf (2054904453143/1000000000000 : ℚ))) (.split (.leaf (1027452421521/500000000000 : ℚ)) (.leaf (128431577213/62500000000 : ℚ)))) (.split (.split (.leaf (513726407561/250000000000 : ℚ)) (.leaf (2054906027529/1000000000000 : ℚ))) (.split (.leaf (2054906427281/1000000000000 : ℚ)) (.leaf (1027453414741/500000000000 : ℚ))))))

theorem cover8_tree0094_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0094 (133/1024 : ℚ) (533/4096 : ℚ) := by
  unfold cover8_tree0094
  refine tree_all_split_at (1065/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2129/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4257/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8513/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1503_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1504_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8515/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1505_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1506_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4259/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8517/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1507_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1508_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8519/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1509_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1510_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2131/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4261/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8521/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1511_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1512_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8523/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1513_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1514_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4263/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8525/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1515_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1516_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8527/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1517_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1518_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0094_checked
#print axioms SmaleRate.Proofs.cover8_tree0094_checked
