/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0021
import SmaleRate.Proofs.Generated.D7Chunk0022

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0035 : BoxTree := (.split (.split (.split (.split (.leaf (2019060403789/1000000000000 : ℚ)) (.leaf (1009531799529/500000000000 : ℚ))) (.split (.leaf (403813365749/200000000000 : ℚ)) (.leaf (504767523197/250000000000 : ℚ)))) (.split (.split (.leaf (201907339121/100000000000 : ℚ)) (.leaf (2019076723939/1000000000000 : ℚ))) (.split (.leaf (2019080090993/1000000000000 : ℚ)) (.leaf (20190834923/10000000000 : ℚ))))) (.split (.split (.split (.leaf (403817385577/200000000000 : ℚ)) (.leaf (2019090397693/1000000000000 : ℚ))) (.split (.leaf (2019093901691/1000000000000 : ℚ)) (.leaf (15774198749/7812500000 : ℚ)))) (.split (.split (.leaf (1009550506099/500000000000 : ℚ)) (.leaf (1009552309329/500000000000 : ℚ))) (.split (.leaf (252388532401/125000000000 : ℚ)) (.leaf (2019111933841/1000000000000 : ℚ))))))

theorem cover7_tree0035_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0035 (145/1024 : ℚ) (73/512 : ℚ) := by
  unfold cover7_tree0035
  refine tree_all_split_at (291/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (581/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1161/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2321/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0540_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0541_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2323/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0542_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0543_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1163/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2325/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0544_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0545_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2327/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0546_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0547_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (583/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1165/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2329/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0548_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0549_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2331/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0550_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0551_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1167/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2333/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0552_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0553_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2335/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0554_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0555_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0035_checked
#print axioms SmaleRate.Proofs.cover7_tree0035_checked
