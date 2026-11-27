/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0005
public import SmaleRate.Proofs.Generated.D7Chunk0006

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0010 : BoxTree := (.split (.split (.split (.split (.leaf (252379481877/125000000000 : ℚ)) (.leaf (126189676111/62500000000 : ℚ))) (.split (.leaf (1009516895093/500000000000 : ℚ)) (.leaf (252379096527/125000000000 : ℚ)))) (.split (.split (.leaf (2019031763863/1000000000000 : ℚ)) (.leaf (1009515382561/500000000000 : ℚ))) (.split (.leaf (2019029775999/1000000000000 : ℚ)) (.leaf (2019028796491/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (80761113063/40000000000 : ℚ)) (.leaf (2019026866279/1000000000000 : ℚ))) (.split (.leaf (504756478889/250000000000 : ℚ)) (.leaf (40380499489/20000000000 : ℚ)))) (.split (.split (.leaf (2019024042923/1000000000000 : ℚ)) (.leaf (504755780243/250000000000 : ℚ))) (.split (.leaf (2019022208609/1000000000000 : ℚ)) (.leaf (63094415807/31250000000 : ℚ))))))

theorem cover7_tree0010_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0010 (17/128 : ℚ) (273/2048 : ℚ) := by
  unfold cover7_tree0010
  refine tree_all_split_at (545/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1089/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2177/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4353/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0137_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0138_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4355/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0139_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0140_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2179/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4357/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0141_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0142_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4359/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0143_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0144_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1091/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2181/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4361/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0145_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0146_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4363/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0147_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0148_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2183/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4365/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0149_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0150_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4367/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0151_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0152_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0010_checked
#print axioms SmaleRate.Proofs.cover7_tree0010_checked
