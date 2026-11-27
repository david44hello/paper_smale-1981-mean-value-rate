/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0052
public import SmaleRate.Proofs.Generated.D8Chunk0053

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0082 : BoxTree := (.split (.split (.split (.split (.leaf (128431483993/62500000000 : ℚ)) (.leaf (128431486743/62500000000 : ℚ))) (.split (.leaf (2054903832069/1000000000000 : ℚ)) (.leaf (513725969099/250000000000 : ℚ)))) (.split (.split (.leaf (16439231367/8000000000 : ℚ)) (.leaf (1027451982753/500000000000 : ℚ))) (.split (.leaf (410980802059/200000000000 : ℚ)) (.leaf (2054904055251/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054904100363/1000000000000 : ℚ)) (.leaf (102745207281/50000000000 : ℚ))) (.split (.leaf (513726047759/250000000000 : ℚ)) (.leaf (1027452118301/500000000000 : ℚ)))) (.split (.split (.leaf (2054904282341/1000000000000 : ℚ)) (.leaf (2054904328227/1000000000000 : ℚ))) (.split (.leaf (513726093567/250000000000 : ℚ)) (.leaf (2054904420479/1000000000000 : ℚ))))))

theorem cover8_tree0082_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0082 (2109/16384 : ℚ) (1055/8192 : ℚ) := by
  unfold cover8_tree0082
  refine tree_all_split_at (4219/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8437/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16873/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33745/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1312_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1313_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33747/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1314_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1315_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16875/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33749/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1316_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1317_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33751/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1318_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1319_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8439/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16877/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33753/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1320_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1321_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33755/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1322_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1323_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16879/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33757/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1324_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1325_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33759/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1326_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1327_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0082_checked
#print axioms SmaleRate.Proofs.cover8_tree0082_checked
