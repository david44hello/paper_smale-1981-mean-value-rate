/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0054
import SmaleRate.Proofs.Generated.D8Chunk0055

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0085 : BoxTree := (.split (.split (.split (.split (.leaf (64215813527/31250000000 : ℚ)) (.leaf (2054906084383/1000000000000 : ℚ))) (.split (.leaf (41098122721/20000000000 : ℚ)) (.leaf (128431636743/62500000000 : ℚ)))) (.split (.split (.leaf (2054906239861/1000000000000 : ℚ)) (.leaf (2054906292003/1000000000000 : ℚ))) (.split (.leaf (2054906344303/1000000000000 : ℚ)) (.leaf (410981279353/200000000000 : ℚ))))) (.split (.split (.split (.leaf (2054906449369/1000000000000 : ℚ)) (.leaf (1027453251069/500000000000 : ℚ))) (.split (.leaf (128431659691/62500000000 : ℚ)) (.leaf (410981321627/200000000000 : ℚ)))) (.split (.split (.leaf (1027453330687/500000000000 : ℚ)) (.leaf (1027453357387/500000000000 : ℚ))) (.split (.leaf (128431673019/62500000000 : ℚ)) (.leaf (256863352753/125000000000 : ℚ))))))

theorem cover8_tree0085_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0085 (33/256 : ℚ) (2113/16384 : ℚ) := by
  unfold cover8_tree0085
  refine tree_all_split_at (4225/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8449/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16897/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33793/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1360_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1361_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33795/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1362_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1363_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16899/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33797/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1364_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1365_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33799/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1366_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1367_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8451/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16901/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33801/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1368_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1369_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33803/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1370_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1371_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16903/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33805/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1372_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1373_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33807/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1374_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1375_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0085_checked
#print axioms SmaleRate.Proofs.cover8_tree0085_checked
