/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0012
public import SmaleRate.Proofs.Generated.D7Chunk0013

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0021 : BoxTree := (.split (.split (.split (.split (.leaf (504752366791/250000000000 : ℚ)) (.leaf (252376184061/125000000000 : ℚ))) (.split (.leaf (126188092507/62500000000 : ℚ)) (.leaf (2019009490049/1000000000000 : ℚ)))) (.split (.split (.leaf (2019009502289/1000000000000 : ℚ)) (.leaf (252376189603/125000000000 : ℚ))) (.split (.leaf (1009504766831/500000000000 : ℚ)) (.leaf (2019009552799/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2019009574233/1000000000000 : ℚ)) (.leaf (252376199747/125000000000 : ℚ))) (.split (.leaf (1009504812011/500000000000 : ℚ)) (.leaf (2019009652361/1000000000000 : ℚ)))) (.split (.split (.leaf (2019009682999/1000000000000 : ℚ)) (.leaf (2019009715927/1000000000000 : ℚ))) (.split (.leaf (403801950231/200000000000 : ℚ)) (.leaf (2019009788687/1000000000000 : ℚ))))))

theorem cover7_tree0021_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0021 (279/2048 : ℚ) (559/4096 : ℚ) := by
  unfold cover7_tree0021
  refine tree_all_split_at (1117/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2233/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4465/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8929/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0318_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0319_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8931/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0320_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0321_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4467/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8933/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0322_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0323_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8935/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0324_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0325_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2235/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4469/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8937/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0326_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0327_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8939/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0328_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0329_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4471/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8941/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0330_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0331_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8943/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0332_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0333_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0021_checked
#print axioms SmaleRate.Proofs.cover7_tree0021_checked
