/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0045

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0071 : BoxTree := (.split (.split (.split (.split (.leaf (16053929329/7812500000 : ℚ)) (.leaf (2054902964739/1000000000000 : ℚ))) (.split (.leaf (2054902975409/1000000000000 : ℚ)) (.leaf (2054902986117/1000000000000 : ℚ)))) (.split (.split (.leaf (410980599373/200000000000 : ℚ)) (.leaf (2054903007649/1000000000000 : ℚ))) (.split (.leaf (2054903018487/1000000000000 : ℚ)) (.leaf (2054903029347/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054903040249/1000000000000 : ℚ)) (.leaf (2054903051203/1000000000000 : ℚ))) (.split (.leaf (102745153109/50000000000 : ℚ)) (.leaf (205490307321/100000000000 : ℚ)))) (.split (.split (.leaf (410980616853/200000000000 : ℚ)) (.leaf (16439224763/8000000000 : ℚ))) (.split (.leaf (410980621301/200000000000 : ℚ)) (.leaf (2054903117687/1000000000000 : ℚ))))))

theorem cover8_tree0071_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0071 (525/4096 : ℚ) (4201/32768 : ℚ) := by
  unfold cover8_tree0071
  refine tree_all_split_at (8401/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16801/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33601/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67201/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1128_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1129_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67203/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1130_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1131_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33603/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67205/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1132_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1133_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67207/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1134_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1135_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16803/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33605/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67209/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1136_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1137_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67211/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1138_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1139_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33607/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67213/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1140_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1141_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67215/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1142_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1143_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0071_checked
#print axioms SmaleRate.Proofs.cover8_tree0071_checked
