/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0014
import SmaleRate.Proofs.Generated.D8Chunk0015

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0024 : BoxTree := (.split (.split (.split (.split (.leaf (513726365343/250000000000 : ℚ)) (.leaf (2054905411233/1000000000000 : ℚ))) (.split (.leaf (1027452680627/500000000000 : ℚ)) (.leaf (1027452655717/500000000000 : ℚ)))) (.split (.split (.leaf (2054905261769/1000000000000 : ℚ)) (.leaf (51372630307/25000000000 : ℚ))) (.split (.leaf (1027452581473/500000000000 : ℚ)) (.leaf (82196204551/40000000000 : ℚ))))) (.split (.split (.split (.leaf (2054905064757/1000000000000 : ℚ)) (.leaf (410981003183/200000000000 : ℚ))) (.split (.leaf (2054904967233/1000000000000 : ℚ)) (.leaf (2054904918703/1000000000000 : ℚ)))) (.split (.split (.leaf (2054904870337/1000000000000 : ℚ)) (.leaf (1027452411071/500000000000 : ℚ))) (.split (.leaf (256863096761/125000000000 : ℚ)) (.leaf (205490472621/100000000000 : ℚ))))))

theorem cover8_tree0024_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0024 (259/2048 : ℚ) (2073/16384 : ℚ) := by
  unfold cover8_tree0024
  refine tree_all_split_at (4145/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8289/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16577/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33153/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0372_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0373_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33155/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0374_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0375_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16579/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33157/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0376_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0377_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33159/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0378_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0379_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8291/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16581/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33161/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0380_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0381_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33163/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0382_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0383_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16583/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33165/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0384_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0385_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33167/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0386_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0387_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0024_checked
#print axioms SmaleRate.Proofs.cover8_tree0024_checked
