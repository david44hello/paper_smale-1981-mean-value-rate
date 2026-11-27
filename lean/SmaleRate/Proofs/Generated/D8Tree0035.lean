/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0022

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0035 : BoxTree := (.split (.split (.split (.split (.leaf (2054903419417/1000000000000 : ℚ)) (.leaf (410980681431/200000000000 : ℚ))) (.split (.leaf (2054903394937/1000000000000 : ℚ)) (.leaf (2054903382761/1000000000000 : ℚ)))) (.split (.split (.leaf (10274516853/5000000000 : ℚ)) (.leaf (1027451679251/500000000000 : ℚ))) (.split (.leaf (2054903346439/1000000000000 : ℚ)) (.leaf (2054903334419/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (128431457653/62500000000 : ℚ)) (.leaf (4109806621/2000000000 : ℚ))) (.split (.leaf (2054903298591/1000000000000 : ℚ)) (.leaf (205490328673/100000000000 : ℚ)))) (.split (.split (.leaf (2054903274919/1000000000000 : ℚ)) (.leaf (513725815783/250000000000 : ℚ))) (.split (.leaf (2054903251377/1000000000000 : ℚ)) (.leaf (1027451619843/500000000000 : ℚ))))))

theorem cover8_tree0035_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0035 (1041/8192 : ℚ) (4165/32768 : ℚ) := by
  unfold cover8_tree0035
  refine tree_all_split_at (8329/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16657/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33313/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66625/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0552_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0553_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66627/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0554_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0555_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33315/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66629/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0556_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0557_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66631/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0558_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0559_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16659/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33317/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66633/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0560_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0561_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66635/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0562_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0563_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33319/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66637/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0564_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0565_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66639/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0566_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0567_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0035_checked
#print axioms SmaleRate.Proofs.cover8_tree0035_checked
