/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0008
public import SmaleRate.Proofs.Generated.D8Chunk0009

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0015 : BoxTree := (.split (.split (.split (.split (.leaf (2054915704609/1000000000000 : ℚ)) (.leaf (2054915521547/1000000000000 : ℚ))) (.split (.leaf (513728834787/250000000000 : ℚ)) (.leaf (205491515739/100000000000 : ℚ)))) (.split (.split (.leaf (256864372039/125000000000 : ℚ)) (.leaf (410982959173/200000000000 : ℚ))) (.split (.leaf (2054914616077/1000000000000 : ℚ)) (.leaf (410982887389/200000000000 : ℚ))))) (.split (.split (.split (.leaf (82196570339/40000000000 : ℚ)) (.leaf (128432130041/62500000000 : ℚ))) (.split (.leaf (410982780699/200000000000 : ℚ)) (.leaf (2054913726971/1000000000000 : ℚ)))) (.split (.split (.leaf (1027456775561/500000000000 : ℚ)) (.leaf (2054913375907/1000000000000 : ℚ))) (.split (.leaf (513728300343/250000000000 : ℚ)) (.leaf (1027456513737/500000000000 : ℚ))))))

theorem cover8_tree0015_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0015 (257/2048 : ℚ) (1029/8192 : ℚ) := by
  unfold cover8_tree0015
  refine tree_all_split_at (2057/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4113/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8225/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16449/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0222_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0223_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16451/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0224_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0225_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8227/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16453/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0226_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0227_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16455/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0228_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0229_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4115/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8229/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16457/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0230_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0231_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16459/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0232_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0233_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8231/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16461/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0234_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0235_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16463/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0236_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0237_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0015_checked
#print axioms SmaleRate.Proofs.cover8_tree0015_checked
