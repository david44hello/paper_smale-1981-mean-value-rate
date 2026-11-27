/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0004

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0008 : BoxTree := (.split (.split (.split (.split (.leaf (1027480044227/500000000000 : ℚ)) (.leaf (2054958515533/1000000000000 : ℚ))) (.split (.leaf (2054956953451/1000000000000 : ℚ)) (.leaf (410991080439/200000000000 : ℚ)))) (.split (.split (.leaf (2054953861781/1000000000000 : ℚ)) (.leaf (2054952332187/1000000000000 : ℚ))) (.split (.leaf (513737703353/250000000000 : ℚ)) (.leaf (2054949305463/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027473904159/500000000000 : ℚ)) (.leaf (82197852879/40000000000 : ℚ))) (.split (.leaf (513736211607/250000000000 : ℚ)) (.leaf (2054943381691/1000000000000 : ℚ)))) (.split (.split (.leaf (25686774097/12500000000 : ℚ)) (.leaf (2054940484593/1000000000000 : ℚ))) (.split (.leaf (102746952611/50000000000 : ℚ)) (.leaf (1027468815311/500000000000 : ℚ))))))

theorem cover8_tree0008_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0008 (63/512 : ℚ) (253/2048 : ℚ) := by
  unfold cover8_tree0008
  refine tree_all_split_at (505/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1009/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2017/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4033/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0107_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0108_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4035/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0109_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0110_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2019/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4037/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0111_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0112_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4039/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0113_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0114_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1011/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2021/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4041/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0115_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0116_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4043/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0117_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0118_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2023/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4045/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0119_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0120_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4047/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0121_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0122_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0008_checked
#print axioms SmaleRate.Proofs.cover8_tree0008_checked
