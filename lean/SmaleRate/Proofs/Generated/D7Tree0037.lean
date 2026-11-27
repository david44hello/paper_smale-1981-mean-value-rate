/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0022
import SmaleRate.Proofs.Generated.D7Chunk0023

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0037 : BoxTree := (.split (.split (.split (.split (.split (.leaf (1009566862337/500000000000 : ℚ)) (.leaf (80765738411/40000000000 : ℚ))) (.split (.leaf (1009576664251/500000000000 : ℚ)) (.leaf (1009581664573/500000000000 : ℚ)))) (.split (.split (.leaf (2019173462047/1000000000000 : ℚ)) (.leaf (252397965873/125000000000 : ℚ))) (.split (.leaf (80767764951/40000000000 : ℚ)) (.leaf (403840930447/200000000000 : ℚ))))) (.split (.split (.split (.leaf (504803828041/250000000000 : ℚ)) (.leaf (2019226103361/1000000000000 : ℚ))) (.leaf (1009500801831/500000000000 : ℚ))) (.split (.leaf (2019024099283/1000000000000 : ℚ)) (.leaf (1009523558083/500000000000 : ℚ))))) (.split (.split (.split (.leaf (504767663209/250000000000 : ℚ)) (.leaf (2019094707789/1000000000000 : ℚ))) (.split (.leaf (1009559639773/500000000000 : ℚ)) (.leaf (16153154933/8000000000 : ℚ)))) (.split (.split (.leaf (403833993511/200000000000 : ℚ)) (.leaf (252399510109/125000000000 : ℚ))) (.split (.leaf (2019222705121/1000000000000 : ℚ)) (.leaf (504812459713/250000000000 : ℚ))))))

theorem cover7_tree0037_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0037 (37/256 : ℚ) (19/128 : ℚ) := by
  unfold cover7_tree0037
  refine tree_all_split_at (75/512 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (149/1024 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (297/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (593/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1185/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0573_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0574_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1187/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0575_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0576_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (595/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1189/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0577_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0578_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1191/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0579_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0580_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (299/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (597/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1193/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0581_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0582_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0583_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (599/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0584_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0585_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (151/1024 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (301/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (601/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0586_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0587_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (603/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0588_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0589_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (303/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (605/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0590_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0591_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (607/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0592_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0593_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0037_checked
#print axioms SmaleRate.Proofs.cover7_tree0037_checked
