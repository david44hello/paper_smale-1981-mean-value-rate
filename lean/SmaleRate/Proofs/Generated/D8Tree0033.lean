/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0020
import SmaleRate.Proofs.Generated.D8Chunk0021

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0033 : BoxTree := (.split (.split (.split (.split (.leaf (128431489561/62500000000 : ℚ)) (.leaf (1027451909717/500000000000 : ℚ))) (.split (.leaf (205490380593/100000000000 : ℚ)) (.leaf (1027451896233/500000000000 : ℚ)))) (.split (.split (.leaf (1027451889519/500000000000 : ℚ)) (.leaf (41098075313/20000000000 : ℚ))) (.split (.leaf (128431484519/62500000000 : ℚ)) (.leaf (1027451869497/500000000000 : ℚ))))) (.split (.split (.split (.leaf (410980745149/200000000000 : ℚ)) (.leaf (2054903712509/1000000000000 : ℚ))) (.split (.leaf (1027451849667/500000000000 : ℚ)) (.leaf (513725921547/250000000000 : ℚ)))) (.split (.split (.leaf (2054903673091/1000000000000 : ℚ)) (.leaf (2054903660017/1000000000000 : ℚ))) (.split (.leaf (2054903646999/1000000000000 : ℚ)) (.leaf (2054903634019/1000000000000 : ℚ))))))

theorem cover8_tree0033_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0033 (2081/16384 : ℚ) (4163/32768 : ℚ) := by
  unfold cover8_tree0033
  refine tree_all_split_at (8325/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16649/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33297/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66593/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0520_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0521_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66595/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0522_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0523_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33299/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66597/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0524_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0525_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66599/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0526_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0527_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16651/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33301/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66601/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0528_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0529_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66603/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0530_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0531_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33303/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66605/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0532_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0533_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66607/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0534_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0535_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0033_checked
#print axioms SmaleRate.Proofs.cover8_tree0033_checked
