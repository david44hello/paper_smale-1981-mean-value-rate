/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0012
import SmaleRate.Proofs.Generated.D8Chunk0013

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0021 : BoxTree := (.split (.split (.split (.split (.leaf (1027450553697/500000000000 : ℚ)) (.leaf (1027450493447/500000000000 : ℚ))) (.split (.leaf (410980173409/200000000000 : ℚ)) (.leaf (2054900747829/1000000000000 : ℚ)))) (.split (.split (.leaf (1027450314631/500000000000 : ℚ)) (.leaf (2054900511363/1000000000000 : ℚ))) (.split (.leaf (2054900394097/1000000000000 : ℚ)) (.leaf (2054900277477/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054900161509/1000000000000 : ℚ)) (.leaf (2054900046173/1000000000000 : ℚ))) (.split (.split (.leaf (1027453913799/500000000000 : ℚ)) (.leaf (410981554069/200000000000 : ℚ))) (.split (.leaf (1027453856623/500000000000 : ℚ)) (.leaf (2054907656323/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054907599543/1000000000000 : ℚ)) (.leaf (1027453771467/500000000000 : ℚ))) (.split (.leaf (2054907486489/1000000000000 : ℚ)) (.leaf (2054907430199/1000000000000 : ℚ)))) (.split (.split (.leaf (1027453687041/500000000000 : ℚ)) (.leaf (1027453659063/500000000000 : ℚ))) (.split (.leaf (2054907262327/1000000000000 : ℚ)) (.leaf (410981441337/200000000000 : ℚ)))))))

theorem cover8_tree0021_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0021 (517/4096 : ℚ) (1035/8192 : ℚ) := by
  unfold cover8_tree0021
  refine tree_all_split_at (2069/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4137/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8273/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16545/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0318_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0319_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16547/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0320_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0321_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8275/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16549/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0322_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0323_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16551/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0324_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0325_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4139/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8277/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16553/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0326_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0327_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16555/131072 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (33109/262144 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0328_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0329_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (33111/262144 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0330_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0331_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8279/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16557/131072 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (33113/262144 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0332_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0333_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (33115/262144 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0334_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0335_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16559/131072 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (33117/262144 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0336_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0337_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (33119/262144 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0338_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0339_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0021_checked
#print axioms SmaleRate.Proofs.cover8_tree0021_checked
