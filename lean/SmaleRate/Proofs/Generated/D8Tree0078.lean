/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0049
public import SmaleRate.Proofs.Generated.D8Chunk0050

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0078 : BoxTree := (.split (.split (.split (.split (.leaf (410980250663/200000000000 : ℚ)) (.leaf (2054901287287/1000000000000 : ℚ))) (.split (.leaf (256862665177/125000000000 : ℚ)) (.leaf (1027450677847/500000000000 : ℚ)))) (.split (.split (.leaf (2054901390141/1000000000000 : ℚ)) (.leaf (513725356187/250000000000 : ℚ))) (.split (.leaf (2054901459503/1000000000000 : ℚ)) (.leaf (205490149441/100000000000 : ℚ))))) (.split (.split (.split (.leaf (128431345593/62500000000 : ℚ)) (.leaf (2054901564707/1000000000000 : ℚ))) (.split (.leaf (2054901600093/1000000000000 : ℚ)) (.leaf (513725408911/250000000000 : ℚ)))) (.split (.split (.leaf (1027450835669/500000000000 : ℚ)) (.leaf (2054901707201/1000000000000 : ℚ))) (.split (.leaf (410980348643/200000000000 : ℚ)) (.leaf (513725444847/250000000000 : ℚ))))))

theorem cover8_tree0078_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0078 (2105/16384 : ℚ) (1053/8192 : ℚ) := by
  unfold cover8_tree0078
  refine tree_all_split_at (4211/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8421/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16841/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33681/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1248_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1249_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33683/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1250_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1251_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16843/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33685/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1252_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1253_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33687/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1254_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1255_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8423/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16845/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33689/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1256_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1257_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33691/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1258_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1259_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16847/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33693/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1260_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1261_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33695/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1262_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1263_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0078_checked
#print axioms SmaleRate.Proofs.cover8_tree0078_checked
