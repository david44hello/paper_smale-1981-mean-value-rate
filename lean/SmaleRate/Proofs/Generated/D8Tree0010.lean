/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0005
public import SmaleRate.Proofs.Generated.D8Chunk0006

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0010 : BoxTree := (.split (.split (.split (.split (.leaf (2054915108093/1000000000000 : ℚ)) (.leaf (2054913879711/1000000000000 : ℚ))) (.split (.leaf (2054912662013/1000000000000 : ℚ)) (.leaf (2054911455013/1000000000000 : ℚ)))) (.split (.split (.leaf (2054910258683/1000000000000 : ℚ)) (.leaf (256863634131/125000000000 : ℚ))) (.split (.leaf (513726974517/250000000000 : ℚ)) (.leaf (1027453366879/500000000000 : ℚ))))) (.split (.split (.split (.leaf (410981116021/200000000000 : ℚ)) (.leaf (1027452218559/500000000000 : ℚ))) (.split (.leaf (82196132191/40000000000 : ℚ)) (.leaf (410980436619/200000000000 : ℚ)))) (.split (.split (.leaf (51372526801/25000000000 : ℚ)) (.split (.leaf (513732969011/250000000000 : ℚ)) (.leaf (1027465663581/500000000000 : ℚ)))) (.split (.split (.leaf (2054930780937/1000000000000 : ℚ)) (.leaf (2054930237381/1000000000000 : ℚ))) (.split (.leaf (205492969647/100000000000 : ℚ)) (.leaf (2054929158231/1000000000000 : ℚ)))))))

theorem cover8_tree0010_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0010 (127/1024 : ℚ) (255/2048 : ℚ) := by
  unfold cover8_tree0010
  refine tree_all_split_at (509/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1017/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2033/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4065/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0139_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0140_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4067/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0141_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0142_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2035/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4069/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0143_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0144_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4071/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0145_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0146_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1019/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2037/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4073/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0147_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0148_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4075/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0149_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0150_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2039/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4077/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0151_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (8155/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0152_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0153_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4079/32768 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (8157/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0154_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0155_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (8159/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0156_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0157_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0010_checked
#print axioms SmaleRate.Proofs.cover8_tree0010_checked
