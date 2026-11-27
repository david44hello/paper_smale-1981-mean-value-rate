/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0009
import SmaleRate.Proofs.Generated.D8Chunk0010

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0016 : BoxTree := (.split (.split (.split (.split (.leaf (1027456427113/500000000000 : ℚ)) (.leaf (2054912681641/1000000000000 : ℚ))) (.split (.leaf (2054912509709/1000000000000 : ℚ)) (.leaf (2054912338429/1000000000000 : ℚ)))) (.split (.split (.leaf (2054912167791/1000000000000 : ℚ)) (.leaf (16053999983/7812500000 : ℚ))) (.split (.leaf (4109823657/2000000000 : ℚ)) (.leaf (1027455829921/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054911491823/1000000000000 : ℚ)) (.leaf (1027455662231/500000000000 : ℚ))) (.split (.leaf (410982231551/200000000000 : ℚ)) (.leaf (1027455495851/500000000000 : ℚ)))) (.split (.split (.leaf (513727706577/250000000000 : ℚ)) (.leaf (2054910661561/1000000000000 : ℚ))) (.split (.leaf (1027455248727/500000000000 : ℚ)) (.leaf (256863791753/125000000000 : ℚ))))))

theorem cover8_tree0016_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0016 (1029/8192 : ℚ) (515/4096 : ℚ) := by
  unfold cover8_tree0016
  refine tree_all_split_at (2059/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4117/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8233/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16465/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0238_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0239_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16467/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0240_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0241_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8235/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16469/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0242_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0243_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16471/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0244_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0245_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4119/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8237/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16473/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0246_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0247_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16475/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0248_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0249_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8239/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16477/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0250_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0251_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16479/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0252_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0253_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0016_checked
#print axioms SmaleRate.Proofs.cover8_tree0016_checked
