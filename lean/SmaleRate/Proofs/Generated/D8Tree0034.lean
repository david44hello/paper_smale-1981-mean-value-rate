/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0021
public import SmaleRate.Proofs.Generated.D8Chunk0022

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0034 : BoxTree := (.split (.split (.split (.split (.leaf (102745181053/50000000000 : ℚ)) (.leaf (410980721633/200000000000 : ℚ))) (.split (.leaf (2054903595301/1000000000000 : ℚ)) (.leaf (2054903582479/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903569693/1000000000000 : ℚ)) (.leaf (41098071139/20000000000 : ℚ))) (.split (.leaf (256862943031/125000000000 : ℚ)) (.leaf (102745176579/50000000000 : ℚ))))) (.split (.split (.split (.leaf (256862939869/125000000000 : ℚ)) (.leaf (1027451753191/500000000000 : ℚ))) (.split (.leaf (1027451746917/500000000000 : ℚ)) (.leaf (2054903481327/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903468871/1000000000000 : ℚ)) (.leaf (51372586411/25000000000 : ℚ))) (.split (.leaf (410980688813/200000000000 : ℚ)) (.leaf (2054903431729/1000000000000 : ℚ))))))

theorem cover8_tree0034_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0034 (4163/32768 : ℚ) (1041/8192 : ℚ) := by
  unfold cover8_tree0034
  refine tree_all_split_at (8327/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16653/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33305/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66609/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0536_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0537_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66611/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0538_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0539_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33307/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66613/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0540_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0541_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66615/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0542_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0543_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16655/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33309/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66617/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0544_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0545_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66619/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0546_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0547_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33311/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66621/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0548_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0549_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66623/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0550_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0551_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0034_checked
#print axioms SmaleRate.Proofs.cover8_tree0034_checked
