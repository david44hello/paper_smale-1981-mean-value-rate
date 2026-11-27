/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0017
import SmaleRate.Proofs.Generated.D7Chunk0018

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0029 : BoxTree := (.split (.split (.split (.split (.split (.leaf (7886830923/3906250000 : ℚ)) (.leaf (1009514506399/500000000000 : ℚ))) (.split (.leaf (50475732789/25000000000 : ℚ)) (.leaf (2019029612553/1000000000000 : ℚ)))) (.split (.split (.leaf (504757478951/250000000000 : ℚ)) (.leaf (2019030221299/1000000000000 : ℚ))) (.leaf (2019000031289/1000000000000 : ℚ)))) (.split (.split (.leaf (80760026319/40000000000 : ℚ)) (.leaf (2019001293619/1000000000000 : ℚ))) (.split (.leaf (252375242281/125000000000 : ℚ)) (.leaf (12618766199/6250000000 : ℚ))))) (.split (.split (.split (.leaf (504750813597/250000000000 : ℚ)) (.leaf (2019003925897/1000000000000 : ℚ))) (.split (.leaf (504751151589/250000000000 : ℚ)) (.leaf (252375661973/125000000000 : ℚ)))) (.split (.split (.leaf (252375749269/125000000000 : ℚ)) (.leaf (2019006701449/1000000000000 : ℚ))) (.split (.leaf (63093981803/31250000000 : ℚ)) (.leaf (2019008142887/1000000000000 : ℚ))))))

theorem cover7_tree0029_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0029 (283/2048 : ℚ) (71/512 : ℚ) := by
  unfold cover7_tree0029
  refine tree_all_split_at (567/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1133/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2265/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4529/32768 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (9057/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0446_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0447_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (9059/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0448_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0449_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4531/32768 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (9061/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0450_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0451_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0452_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2267/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4533/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0453_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0454_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4535/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0455_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0456_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1135/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2269/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4537/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0457_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0458_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4539/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0459_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0460_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2271/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4541/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0461_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0462_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4543/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0463_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0464_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0029_checked
#print axioms SmaleRate.Proofs.cover7_tree0029_checked
