/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0004
import SmaleRate.Proofs.Generated.D8Chunk0005

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0009 : BoxTree := (.split (.split (.split (.split (.leaf (64216756869/31250000000 : ℚ)) (.leaf (513733704939/250000000000 : ℚ))) (.split (.leaf (1027466715231/500000000000 : ℚ)) (.leaf (102746602597/50000000000 : ℚ)))) (.split (.split (.leaf (2054930684169/1000000000000 : ℚ)) (.leaf (2054929327147/1000000000000 : ℚ))) (.split (.leaf (2054927980863/1000000000000 : ℚ)) (.leaf (82197065813/40000000000 : ℚ))))) (.split (.split (.split (.leaf (2054925320523/1000000000000 : ℚ)) (.leaf (1027462003231/500000000000 : ℚ))) (.split (.leaf (256865337891/125000000000 : ℚ)) (.leaf (256865176313/125000000000 : ℚ)))) (.split (.split (.leaf (410984025719/200000000000 : ℚ)) (.leaf (513729714353/250000000000 : ℚ))) (.split (.leaf (2054917596927/1000000000000 : ℚ)) (.leaf (1027458173583/500000000000 : ℚ))))))

theorem cover8_tree0009_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0009 (253/2048 : ℚ) (127/1024 : ℚ) := by
  unfold cover8_tree0009
  refine tree_all_split_at (507/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1013/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2025/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4049/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0123_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0124_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4051/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0125_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0126_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2027/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4053/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0127_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0128_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4055/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0129_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0130_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1015/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2029/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4057/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0131_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0132_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4059/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0133_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0134_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2031/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4061/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0135_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0136_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4063/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0137_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0138_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0009_checked
#print axioms SmaleRate.Proofs.cover8_tree0009_checked
