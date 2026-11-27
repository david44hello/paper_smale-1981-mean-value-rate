/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0004

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0008 : BoxTree := (.split (.split (.split (.leaf (1009505594811/500000000000 : ℚ)) (.leaf (1009504262087/500000000000 : ℚ))) (.split (.leaf (63093934303/31250000000 : ℚ)) (.leaf (2019003310191/1000000000000 : ℚ)))) (.split (.split (.leaf (403800152317/200000000000 : ℚ)) (.split (.leaf (1009530558893/500000000000 : ℚ)) (.leaf (2019059867757/1000000000000 : ℚ)))) (.split (.split (.leaf (2019058627437/1000000000000 : ℚ)) (.leaf (63095543651/31250000000 : ℚ))) (.split (.leaf (2019056175921/1000000000000 : ℚ)) (.leaf (1009527482367/500000000000 : ℚ))))))

theorem cover7_tree0008_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0008 (135/1024 : ℚ) (271/2048 : ℚ) := by
  unfold cover7_tree0008
  refine tree_all_split_at (541/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1081/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2161/16384 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0110_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0111_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2163/16384 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0112_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0113_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1083/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2165/16384 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0114_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4331/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0115_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0116_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2167/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4333/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0117_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0118_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4335/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0119_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0120_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0008_checked
#print axioms SmaleRate.Proofs.cover7_tree0008_checked
