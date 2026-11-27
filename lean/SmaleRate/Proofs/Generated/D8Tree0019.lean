/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0011
public import SmaleRate.Proofs.Generated.D8Chunk0012

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0019 : BoxTree := (.split (.split (.split (.split (.leaf (128431581641/62500000000 : ℚ)) (.leaf (513726291243/250000000000 : ℚ))) (.split (.leaf (2054905024339/1000000000000 : ℚ)) (.leaf (513726221089/250000000000 : ℚ)))) (.split (.split (.leaf (513726186253/250000000000 : ℚ)) (.leaf (1027452303169/500000000000 : ℚ))) (.split (.leaf (410980893659/200000000000 : ℚ)) (.leaf (2054904330923/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (410980838837/200000000000 : ℚ)) (.leaf (1027452029049/500000000000 : ℚ))) (.split (.leaf (102745196133/50000000000 : ℚ)) (.leaf (1027451893941/500000000000 : ℚ)))) (.split (.split (.leaf (1643922923/800000000 : ℚ)) (.leaf (1027451760133/500000000000 : ℚ))) (.split (.leaf (64215730857/31250000000 : ℚ)) (.leaf (1027451627623/500000000000 : ℚ))))))

theorem cover8_tree0019_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0019 (129/1024 : ℚ) (1033/8192 : ℚ) := by
  unfold cover8_tree0019
  refine tree_all_split_at (2065/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4129/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8257/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16513/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0286_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0287_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16515/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0288_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0289_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8259/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16517/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0290_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0291_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16519/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0292_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0293_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4131/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8261/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16521/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0294_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0295_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16523/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0296_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0297_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8263/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16525/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0298_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0299_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16527/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0300_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0301_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0019_checked
#print axioms SmaleRate.Proofs.cover8_tree0019_checked
