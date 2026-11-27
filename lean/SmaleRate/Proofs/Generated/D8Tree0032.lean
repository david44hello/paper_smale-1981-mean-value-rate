/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0020

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0032 : BoxTree := (.split (.split (.split (.split (.leaf (128431272083/62500000000 : ℚ)) (.leaf (2054900323787/1000000000000 : ℚ))) (.split (.leaf (2054900294417/1000000000000 : ℚ)) (.leaf (2054900265209/1000000000000 : ℚ)))) (.split (.split (.leaf (2054900236151/1000000000000 : ℚ)) (.leaf (513725051813/250000000000 : ℚ))) (.split (.leaf (2054900178527/1000000000000 : ℚ)) (.leaf (102745007497/50000000000 : ℚ))))) (.split (.split (.split (.leaf (2054900121527/1000000000000 : ℚ)) (.leaf (2054900093289/1000000000000 : ℚ))) (.split (.leaf (2054900065191/1000000000000 : ℚ)) (.leaf (2054900037263/1000000000000 : ℚ)))) (.split (.split (.split (.leaf (410980788553/200000000000 : ℚ)) (.leaf (513725982227/250000000000 : ℚ))) (.split (.leaf (1027451957539/500000000000 : ℚ)) (.leaf (2054903901299/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903887559/1000000000000 : ℚ)) (.leaf (1027451936921/500000000000 : ℚ))) (.split (.leaf (1027451930091/500000000000 : ℚ)) (.leaf (1027451923279/500000000000 : ℚ)))))))

theorem cover8_tree0032_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0032 (65/512 : ℚ) (2081/16384 : ℚ) := by
  unfold cover8_tree0032
  refine tree_all_split_at (4161/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8321/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16641/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33281/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0500_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0501_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33283/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0502_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0503_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16643/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33285/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0504_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0505_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33287/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0506_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0507_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8323/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16645/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33289/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0508_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0509_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33291/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0510_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0511_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16647/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33293/262144 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (66585/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0512_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0513_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (66587/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0514_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0515_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33295/262144 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (66589/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0516_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0517_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (66591/524288 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0518_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0519_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0032_checked
#print axioms SmaleRate.Proofs.cover8_tree0032_checked
