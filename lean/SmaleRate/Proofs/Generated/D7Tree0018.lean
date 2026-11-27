/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0010
public import SmaleRate.Proofs.Generated.D7Chunk0011

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0018 : BoxTree := (.split (.split (.split (.split (.leaf (2523764911/1250000000 : ℚ)) (.leaf (504752955761/250000000000 : ℚ))) (.split (.leaf (16152093757/8000000000 : ℚ)) (.leaf (403802323703/200000000000 : ℚ)))) (.split (.split (.leaf (403802303947/200000000000 : ℚ)) (.leaf (504752855817/250000000000 : ℚ))) (.split (.leaf (201901132913/100000000000 : ℚ)) (.leaf (1009505618661/500000000000 : ℚ))))) (.split (.split (.split (.leaf (403802229567/200000000000 : ℚ)) (.leaf (2019011060667/1000000000000 : ℚ))) (.split (.leaf (31547046497/15625000000 : ℚ)) (.leaf (2019010893287/1000000000000 : ℚ)))) (.split (.split (.leaf (1009505406539/500000000000 : ℚ)) (.leaf (201901073519/100000000000 : ℚ))) (.split (.leaf (2019010659619/1000000000000 : ℚ)) (.leaf (2019010586369/1000000000000 : ℚ))))))

theorem cover7_tree0018_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0018 (555/4096 : ℚ) (139/1024 : ℚ) := by
  unfold cover7_tree0018
  refine tree_all_split_at (1111/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2221/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4441/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8881/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0270_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0271_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8883/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0272_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0273_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4443/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8885/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0274_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0275_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8887/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0276_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0277_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2223/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4445/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8889/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0278_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0279_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8891/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0280_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0281_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4447/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8893/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0282_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0283_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8895/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0284_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0285_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0018_checked
#print axioms SmaleRate.Proofs.cover7_tree0018_checked
