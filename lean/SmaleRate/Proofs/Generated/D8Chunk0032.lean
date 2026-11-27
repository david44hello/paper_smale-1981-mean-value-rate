/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0800; no trusted numerical premise.
theorem cover8_leaf0800_exp_radius : (199601802788483239/200000000000000000 : ℝ) ≤ Real.exp ((-66873/4194304 : ℝ)/8) ∧ Real.exp ((-66873/4194304 : ℝ)/8) ≤ (249502253485604049/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66873/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0800_exp_lower : (920113451620122743/1000000000000000000 : ℝ) ≤ Real.exp ((-10657062344137/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062344137/16000000000000 : ℝ)/8) ≤ (115014181452515343/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062344137/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0800_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450801049/500000000000 : ℝ) ≤ 4*Real.exp (8359/65536 : ℝ)*Real.exp (-mu (radius 8 (66873/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450801049/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66873/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0800_exp_radius
  have hrNumeric : (984182663381/1000000000000 : ℝ) ≤ Real.exp (-66873/4194304 : ℝ) ∧ Real.exp (-66873/4194304 : ℝ) ≤ (492091331691/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984182663381/1000000000000 : ℝ) ≤ (radius 8 (66873/524288 : ℝ)) ∧ (radius 8 (66873/524288 : ℝ)) ≤ (492091331691/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66873/524288 : ℝ)) (984182663381/1000000000000 : ℝ) (492091331691/500000000000 : ℝ) (177156668229/1000000000000 : ℝ) (44289167059/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66873/524288 : ℝ)) (984182663381/1000000000000 : ℝ) (492091331691/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984182663381/1000000000000 : ℝ) (492091331691/500000000000 : ℝ) (99209133169/100000000000 : ℝ) (992091331691/1000000000000 : ℝ) (62003738023/62500000000 : ℝ) (99205980837/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 1 (99209133169/100000000000 : ℝ) (992091331691/1000000000000 : ℝ) (62003738023/62500000000 : ℝ) (99205980837/100000000000 : ℝ) (992075570029/1000000000000 : ℝ) (992075570031/1000000000000 : ℝ) (992075569903/1000000000000 : ℝ) (496037784953/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 2 (992075570029/1000000000000 : ℝ) (992075570031/1000000000000 : ℝ) (992075569903/1000000000000 : ℝ) (496037784953/500000000000 : ℝ) (496037784983/500000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 3 (496037784983/500000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 4 (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 5 (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 6 (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66873/524288 : ℝ)) 7 (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66873/524288 : ℝ))) (177156668229/1000000000000 : ℝ) (44289167059/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177156668229/1000000000000 : ℝ) (44289167059/250000000000 : ℝ) (294289167057/500000000000 : ℝ) (294289167059/500000000000 : ℝ) (84179966317/200000000000 : ℝ) (84179966319/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 1 (294289167057/500000000000 : ℝ) (294289167059/500000000000 : ℝ) (84179966317/200000000000 : ℝ) (84179966319/200000000000 : ℝ) (504739082849/1000000000000 : ℝ) (504739082857/1000000000000 : ℝ) (124431839199/250000000000 : ℝ) (124431839201/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 2 (504739082849/1000000000000 : ℝ) (504739082857/1000000000000 : ℝ) (124431839199/250000000000 : ℝ) (124431839201/250000000000 : ℝ) (250616609911/500000000000 : ℝ) (501233219831/1000000000000 : ℝ) (501220958837/1000000000000 : ℝ) (250610479423/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 3 (250616609911/500000000000 : ℝ) (501233219831/1000000000000 : ℝ) (501220958837/1000000000000 : ℝ) (250610479423/500000000000 : ℝ) (501227089329/1000000000000 : ℝ) (501227089339/1000000000000 : ℝ) (125306772323/250000000000 : ℝ) (250613544651/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 4 (501227089329/1000000000000 : ℝ) (501227089339/1000000000000 : ℝ) (125306772323/250000000000 : ℝ) (250613544651/500000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 5 (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 6 (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66873/524288 : ℝ))) 7 (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66873/524288 : ℝ)) hmem 8 (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66873/524288 : ℝ))) hcmem 8 (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66873/524288 : ℝ)) (198415113993/200000000000 : ℝ) (992075569969/1000000000000 : ℝ) (50122708931/100000000000 : ℝ) (501227089321/1000000000000 : ℝ) (39680730713/50000000000 : ℝ) (396807307141/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0800_exp_lower
  have heNumeric : (1027450801049/500000000000 : ℝ)/4 ≤ Real.exp (-10657062344137/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450801049/500000000000 : ℝ)/4 ≤ Real.exp ((8359/65536 : ℝ)-(396807307141/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8359/65536 : ℝ) (66873/524288 : ℝ) (396807307141/500000000000 : ℝ) (1027450801049/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0801; no trusted numerical premise.
theorem cover8_leaf0801_exp_radius : (499004492099715129/500000000000000000 : ℝ) ≤ Real.exp ((-33437/2097152 : ℝ)/8) ∧ Real.exp ((-33437/2097152 : ℝ)/8) ≤ (998008984199430259/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33437/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0801_exp_lower : (460056725743677073/500000000000000000 : ℝ) ≤ Real.exp ((-17051299780171/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051299780171/25600000000000 : ℝ)/8) ≤ (920113451487354147/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051299780171/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0801_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450799863/500000000000 : ℝ) ≤ 4*Real.exp (66873/524288 : ℝ)*Real.exp (-mu (radius 8 (33437/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450799863/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33437/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0801_exp_radius
  have hrNumeric : (984182428733/1000000000000 : ℝ) ≤ Real.exp (-33437/2097152 : ℝ) ∧ Real.exp (-33437/2097152 : ℝ) ≤ (492091214367/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984182428733/1000000000000 : ℝ) ≤ (radius 8 (33437/262144 : ℝ)) ∧ (radius 8 (33437/262144 : ℝ)) ≤ (492091214367/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33437/262144 : ℝ)) (984182428733/1000000000000 : ℝ) (492091214367/500000000000 : ℝ) (177157971797/1000000000000 : ℝ) (177157971803/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33437/262144 : ℝ)) (984182428733/1000000000000 : ℝ) (492091214367/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984182428733/1000000000000 : ℝ) (492091214367/500000000000 : ℝ) (496045607183/500000000000 : ℝ) (992091214367/1000000000000 : ℝ) (198411938021/200000000000 : ℝ) (992059690107/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 1 (496045607183/500000000000 : ℝ) (992091214367/1000000000000 : ℝ) (198411938021/200000000000 : ℝ) (992059690107/1000000000000 : ℝ) (198415090447/200000000000 : ℝ) (992075452237/1000000000000 : ℝ) (99207545211/100000000000 : ℝ) (62004715757/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 2 (198415090447/200000000000 : ℝ) (992075452237/1000000000000 : ℝ) (99207545211/100000000000 : ℝ) (62004715757/62500000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 3 (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 4 (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 5 (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 6 (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33437/262144 : ℝ)) 7 (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33437/262144 : ℝ))) (177157971797/1000000000000 : ℝ) (177157971803/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177157971797/1000000000000 : ℝ) (177157971803/1000000000000 : ℝ) (294289492949/500000000000 : ℝ) (294289492951/500000000000 : ℝ) (420901380131/1000000000000 : ℝ) (21045069007/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 1 (294289492949/500000000000 : ℝ) (294289492951/500000000000 : ℝ) (420901380131/1000000000000 : ℝ) (21045069007/50000000000 : ℝ) (252370091507/500000000000 : ℝ) (504740183021/1000000000000 : ℝ) (248864273993/500000000000 : ℝ) (248864273997/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 2 (252370091507/500000000000 : ℝ) (504740183021/1000000000000 : ℝ) (248864273993/500000000000 : ℝ) (248864273997/500000000000 : ℝ) (1002468731/2000000000 : ℝ) (125308591377/250000000000 : ℝ) (501222104861/1000000000000 : ℝ) (501222104869/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 3 (1002468731/2000000000 : ℝ) (125308591377/250000000000 : ℝ) (501222104861/1000000000000 : ℝ) (501222104869/1000000000000 : ℝ) (25061411759/50000000000 : ℝ) (501228235189/1000000000000 : ℝ) (501228235143/1000000000000 : ℝ) (31326764697/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 4 (25061411759/50000000000 : ℝ) (501228235189/1000000000000 : ℝ) (501228235143/1000000000000 : ℝ) (31326764697/62500000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 5 (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 6 (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33437/262144 : ℝ))) 7 (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33437/262144 : ℝ)) hmem 8 (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33437/262144 : ℝ))) hcmem 8 (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33437/262144 : ℝ)) (248018863043/250000000000 : ℝ) (39683018087/40000000000 : ℝ) (501228235161/1000000000000 : ℝ) (501228235171/1000000000000 : ℝ) (396808261383/500000000000 : ℝ) (158723304557/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0801_exp_lower
  have heNumeric : (1027450799863/500000000000 : ℝ)/4 ≤ Real.exp (-17051299780171/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450799863/500000000000 : ℝ)/4 ≤ Real.exp ((66873/524288 : ℝ)-(158723304557/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66873/524288 : ℝ) (33437/262144 : ℝ) (158723304557/200000000000 : ℝ) (1027450799863/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0802; no trusted numerical premise.
theorem cover8_leaf0802_exp_radius : (998008954456445209/1000000000000000000 : ℝ) ≤ Real.exp ((-66875/4194304 : ℝ)/8) ∧ Real.exp ((-66875/4194304 : ℝ)/8) ≤ (99800895445644521/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66875/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0802_exp_lower : (460056725678787959/500000000000000000 : ℝ) ≤ Real.exp ((-42628249522643/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628249522643/64000000000000 : ℝ)/8) ≤ (920113451357575919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628249522643/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0802_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901597407/1000000000000 : ℝ) ≤ 4*Real.exp (33437/262144 : ℝ)*Real.exp (-mu (radius 8 (66875/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901597407/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66875/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0802_exp_radius
  have hrNumeric : (492091097043/500000000000 : ℝ) ≤ Real.exp (-66875/4194304 : ℝ) ∧ Real.exp (-66875/4194304 : ℝ) ≤ (984182194087/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492091097043/500000000000 : ℝ) ≤ (radius 8 (66875/524288 : ℝ)) ∧ (radius 8 (66875/524288 : ℝ)) ≤ (984182194087/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66875/524288 : ℝ)) (492091097043/500000000000 : ℝ) (984182194087/1000000000000 : ℝ) (44289818837/250000000000 : ℝ) (35431855071/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66875/524288 : ℝ)) (492091097043/500000000000 : ℝ) (984182194087/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492091097043/500000000000 : ℝ) (984182194087/1000000000000 : ℝ) (992091097043/1000000000000 : ℝ) (248022774261/250000000000 : ℝ) (992059571843/1000000000000 : ℝ) (248014892961/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 1 (992091097043/1000000000000 : ℝ) (248022774261/250000000000 : ℝ) (992059571843/1000000000000 : ℝ) (248014892961/250000000000 : ℝ) (992075334443/1000000000000 : ℝ) (248018833611/250000000000 : ℝ) (992075334317/1000000000000 : ℝ) (992075334319/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 2 (992075334443/1000000000000 : ℝ) (248018833611/250000000000 : ℝ) (992075334317/1000000000000 : ℝ) (992075334319/1000000000000 : ℝ) (49603766719/50000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 3 (49603766719/50000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 4 (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 5 (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 6 (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66875/524288 : ℝ)) 7 (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66875/524288 : ℝ))) (44289818837/250000000000 : ℝ) (35431855071/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44289818837/250000000000 : ℝ) (35431855071/200000000000 : ℝ) (294289818837/500000000000 : ℝ) (294289818839/500000000000 : ℝ) (105225732163/250000000000 : ℝ) (420902928661/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 1 (294289818837/500000000000 : ℝ) (294289818839/500000000000 : ℝ) (105225732163/250000000000 : ℝ) (420902928661/1000000000000 : ℝ) (504741283163/1000000000000 : ℝ) (50474128317/100000000000 : ℝ) (497729739157/1000000000000 : ℝ) (99545947833/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 2 (504741283163/1000000000000 : ℝ) (50474128317/100000000000 : ℝ) (497729739157/1000000000000 : ℝ) (99545947833/200000000000 : ℝ) (12530887779/25000000000 : ℝ) (3915902431/7812500000 : ℝ) (501223250867/1000000000000 : ℝ) (125305812719/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 3 (12530887779/25000000000 : ℝ) (3915902431/7812500000 : ℝ) (501223250867/1000000000000 : ℝ) (125305812719/250000000000 : ℝ) (501229381013/1000000000000 : ℝ) (250614690511/500000000000 : ℝ) (31326836311/62500000000 : ℝ) (100245876197/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 4 (501229381013/1000000000000 : ℝ) (250614690511/500000000000 : ℝ) (31326836311/62500000000 : ℝ) (100245876197/200000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 5 (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 6 (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66875/524288 : ℝ))) 7 (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66875/524288 : ℝ)) hmem 8 (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66875/524288 : ℝ))) hcmem 8 (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66875/524288 : ℝ)) (992075334379/1000000000000 : ℝ) (496037667191/500000000000 : ℝ) (250614690497/500000000000 : ℝ) (125307345251/250000000000 : ℝ) (396809215621/500000000000 : ℝ) (396809215631/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0802_exp_lower
  have heNumeric : (2054901597407/1000000000000 : ℝ)/4 ≤ Real.exp (-42628249522643/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901597407/1000000000000 : ℝ)/4 ≤ Real.exp ((33437/262144 : ℝ)-(396809215631/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33437/262144 : ℝ) (66875/524288 : ℝ) (396809215631/500000000000 : ℝ) (2054901597407/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0803; no trusted numerical premise.
theorem cover8_leaf0803_exp_radius : (199601784942692209/200000000000000000 : ℝ) ≤ Real.exp ((-16719/1048576 : ℝ)/8) ∧ Real.exp ((-16719/1048576 : ℝ)/8) ≤ (499004462356730523/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16719/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0803_exp_lower : (920113451229982959/1000000000000000000 : ℝ) ≤ Real.exp ((-17051299837457/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051299837457/25600000000000 : ℝ)/8) ≤ (11501418140374787/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051299837457/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0803_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862699391/125000000000 : ℝ) ≤ 4*Real.exp (66875/524288 : ℝ)*Real.exp (-mu (radius 8 (16719/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862699391/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16719/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0803_exp_radius
  have hrNumeric : (984181959439/1000000000000 : ℝ) ≤ Real.exp (-16719/1048576 : ℝ) ∧ Real.exp (-16719/1048576 : ℝ) ≤ (12302274493/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984181959439/1000000000000 : ℝ) ≤ (radius 8 (16719/131072 : ℝ)) ∧ (radius 8 (16719/131072 : ℝ)) ≤ (12302274493/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16719/131072 : ℝ)) (984181959439/1000000000000 : ℝ) (12302274493/12500000000 : ℝ) (17716057889/100000000000 : ℝ) (177160578897/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16719/131072 : ℝ)) (984181959439/1000000000000 : ℝ) (12302274493/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984181959439/1000000000000 : ℝ) (12302274493/12500000000 : ℝ) (992090979719/1000000000000 : ℝ) (24802274493/25000000000 : ℝ) (49602972679/50000000000 : ℝ) (496029726791/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 1 (992090979719/1000000000000 : ℝ) (24802274493/25000000000 : ℝ) (49602972679/50000000000 : ℝ) (496029726791/500000000000 : ℝ) (992075216649/1000000000000 : ℝ) (992075216651/1000000000000 : ℝ) (248018804131/250000000000 : ℝ) (496037608263/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 2 (992075216649/1000000000000 : ℝ) (992075216651/1000000000000 : ℝ) (248018804131/250000000000 : ℝ) (496037608263/500000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 3 (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 4 (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 5 (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 6 (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16719/131072 : ℝ)) 7 (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16719/131072 : ℝ))) (17716057889/100000000000 : ℝ) (177160578897/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17716057889/100000000000 : ℝ) (177160578897/1000000000000 : ℝ) (117716057889/200000000000 : ℝ) (588580289449/1000000000000 : ℝ) (105226119289/250000000000 : ℝ) (84180895433/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 1 (117716057889/200000000000 : ℝ) (588580289449/1000000000000 : ℝ) (105226119289/250000000000 : ℝ) (84180895433/200000000000 : ℝ) (5047423833/10000000000 : ℝ) (504742383307/1000000000000 : ℝ) (99546186063/200000000000 : ℝ) (497730930323/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 2 (5047423833/10000000000 : ℝ) (504742383307/1000000000000 : ℝ) (99546186063/200000000000 : ℝ) (497730930323/1000000000000 : ℝ) (501236656807/1000000000000 : ℝ) (100247331363/200000000000 : ℝ) (501224396861/1000000000000 : ℝ) (50122439687/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 3 (501236656807/1000000000000 : ℝ) (100247331363/200000000000 : ℝ) (501224396861/1000000000000 : ℝ) (50122439687/100000000000 : ℝ) (250615263417/500000000000 : ℝ) (501230526843/1000000000000 : ℝ) (125307631699/250000000000 : ℝ) (250615263403/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 4 (250615263417/500000000000 : ℝ) (501230526843/1000000000000 : ℝ) (125307631699/250000000000 : ℝ) (250615263403/500000000000 : ℝ) (100246105363/200000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 5 (100246105363/200000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 6 (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16719/131072 : ℝ))) 7 (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16719/131072 : ℝ)) hmem 8 (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16719/131072 : ℝ))) hcmem 8 (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16719/131072 : ℝ)) (496037608293/500000000000 : ℝ) (992075216589/1000000000000 : ℝ) (250615263407/500000000000 : ℝ) (20049221073/40000000000 : ℝ) (793620339699/1000000000000 : ℝ) (19840508493/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0803_exp_lower
  have heNumeric : (256862699391/125000000000 : ℝ)/4 ≤ Real.exp (-17051299837457/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862699391/125000000000 : ℝ)/4 ≤ Real.exp ((66875/524288 : ℝ)-(19840508493/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66875/524288 : ℝ) (16719/131072 : ℝ) (19840508493/25000000000 : ℝ) (256862699391/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0804; no trusted numerical premise.
theorem cover8_leaf0804_exp_radius : (998008894970477769/1000000000000000000 : ℝ) ≤ Real.exp ((-66877/4194304 : ℝ)/8) ∧ Real.exp ((-66877/4194304 : ℝ)/8) ≤ (99800889497047777/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66877/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0804_exp_lower : (230028362775913789/250000000000000000 : ℝ) ≤ Real.exp ((-21314124831969/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314124831969/32000000000000 : ℝ)/8) ≤ (920113451103655157/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314124831969/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0804_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901592871/1000000000000 : ℝ) ≤ 4*Real.exp (16719/131072 : ℝ)*Real.exp (-mu (radius 8 (66877/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901592871/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66877/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0804_exp_radius
  have hrNumeric : (984181724791/1000000000000 : ℝ) ≤ Real.exp (-66877/4194304 : ℝ) ∧ Real.exp (-66877/4194304 : ℝ) ≤ (123022715599/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984181724791/1000000000000 : ℝ) ≤ (radius 8 (66877/524288 : ℝ)) ∧ (radius 8 (66877/524288 : ℝ)) ≤ (123022715599/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66877/524288 : ℝ)) (984181724791/1000000000000 : ℝ) (123022715599/125000000000 : ℝ) (44290470607/250000000000 : ℝ) (88580941217/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66877/524288 : ℝ)) (984181724791/1000000000000 : ℝ) (123022715599/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984181724791/1000000000000 : ℝ) (123022715599/125000000000 : ℝ) (198418172479/200000000000 : ℝ) (248022715599/250000000000 : ℝ) (992059335317/1000000000000 : ℝ) (992059335319/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 1 (198418172479/200000000000 : ℝ) (248022715599/250000000000 : ℝ) (992059335317/1000000000000 : ℝ) (992059335319/1000000000000 : ℝ) (124009387357/125000000000 : ℝ) (496037549429/500000000000 : ℝ) (99207509873/100000000000 : ℝ) (992075098733/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 2 (124009387357/125000000000 : ℝ) (496037549429/500000000000 : ℝ) (99207509873/100000000000 : ℝ) (992075098733/1000000000000 : ℝ) (992075098793/1000000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 3 (992075098793/1000000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 4 (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 5 (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 6 (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66877/524288 : ℝ)) 7 (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66877/524288 : ℝ))) (44290470607/250000000000 : ℝ) (88580941217/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44290470607/250000000000 : ℝ) (88580941217/500000000000 : ℝ) (294290470607/500000000000 : ℝ) (588580941217/1000000000000 : ℝ) (420906025649/1000000000000 : ℝ) (420906025657/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 1 (294290470607/500000000000 : ℝ) (588580941217/1000000000000 : ℝ) (420906025649/1000000000000 : ℝ) (420906025657/1000000000000 : ℝ) (504743483431/1000000000000 : ℝ) (504743483437/1000000000000 : ℝ) (248866060733/500000000000 : ℝ) (497732121473/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 2 (504743483431/1000000000000 : ℝ) (504743483437/1000000000000 : ℝ) (248866060733/500000000000 : ℝ) (497732121473/1000000000000 : ℝ) (31327362653/62500000000 : ℝ) (100247560491/200000000000 : ℝ) (7831649107/15625000000 : ℝ) (62653192857/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 3 (31327362653/62500000000 : ℝ) (100247560491/200000000000 : ℝ) (7831649107/15625000000 : ℝ) (62653192857/125000000000 : ℝ) (62653959081/125000000000 : ℝ) (31326979541/62500000000 : ℝ) (50123167261/100000000000 : ℝ) (501231672619/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 4 (62653959081/125000000000 : ℝ) (31326979541/62500000000 : ℝ) (50123167261/100000000000 : ℝ) (501231672619/1000000000000 : ℝ) (501231672629/1000000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 5 (501231672629/1000000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 6 (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66877/524288 : ℝ))) 7 (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66877/524288 : ℝ)) hmem 8 (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66877/524288 : ℝ))) hcmem 8 (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66877/524288 : ℝ)) (124009387349/125000000000 : ℝ) (248018774699/250000000000 : ℝ) (125307918157/250000000000 : ℝ) (250615836319/500000000000 : ℝ) (793622248147/1000000000000 : ℝ) (793622248167/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0804_exp_lower
  have heNumeric : (2054901592871/1000000000000 : ℝ)/4 ≤ Real.exp (-21314124831969/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901592871/1000000000000 : ℝ)/4 ≤ Real.exp ((16719/131072 : ℝ)-(793622248167/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16719/131072 : ℝ) (66877/524288 : ℝ) (793622248167/1000000000000 : ℝ) (2054901592871/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0805; no trusted numerical premise.
theorem cover8_leaf0805_exp_radius : (499004432613747689/500000000000000000 : ℝ) ≤ Real.exp ((-33439/2097152 : ℝ)/8) ∧ Real.exp ((-33439/2097152 : ℝ)/8) ≤ (998008865227495379/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33439/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0805_exp_lower : (230028362745165691/250000000000000000 : ℝ) ≤ Real.exp ((-17051299892951/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051299892951/25600000000000 : ℝ)/8) ≤ (184022690196132553/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051299892951/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0805_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901590673/1000000000000 : ℝ) ≤ 4*Real.exp (66877/524288 : ℝ)*Real.exp (-mu (radius 8 (33439/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901590673/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33439/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0805_exp_radius
  have hrNumeric : (30755671567/31250000000 : ℝ) ≤ Real.exp (-33439/2097152 : ℝ) ∧ Real.exp (-33439/2097152 : ℝ) ≤ (196836298029/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30755671567/31250000000 : ℝ) ≤ (radius 8 (33439/262144 : ℝ)) ∧ (radius 8 (33439/262144 : ℝ)) ≤ (196836298029/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33439/262144 : ℝ)) (30755671567/31250000000 : ℝ) (196836298029/200000000000 : ℝ) (3543263719/20000000000 : ℝ) (44290796489/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33439/262144 : ℝ)) (30755671567/31250000000 : ℝ) (196836298029/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30755671567/31250000000 : ℝ) (196836298029/200000000000 : ℝ) (62005671567/62500000000 : ℝ) (992090745073/1000000000000 : ℝ) (198411843411/200000000000 : ℝ) (31001850533/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 1 (62005671567/62500000000 : ℝ) (992090745073/1000000000000 : ℝ) (198411843411/200000000000 : ℝ) (31001850533/31250000000 : ℝ) (992074981063/1000000000000 : ℝ) (198414996213/200000000000 : ℝ) (496037490469/500000000000 : ℝ) (49603749047/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 2 (992074981063/1000000000000 : ℝ) (198414996213/200000000000 : ℝ) (496037490469/500000000000 : ℝ) (49603749047/50000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 3 (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 4 (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 5 (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 6 (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33439/262144 : ℝ)) 7 (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33439/262144 : ℝ))) (3543263719/20000000000 : ℝ) (44290796489/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3543263719/20000000000 : ℝ) (44290796489/250000000000 : ℝ) (23543263719/40000000000 : ℝ) (294290796489/500000000000 : ℝ) (210453787059/500000000000 : ℝ) (210453787063/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 1 (23543263719/40000000000 : ℝ) (294290796489/500000000000 : ℝ) (210453787059/500000000000 : ℝ) (210453787063/500000000000 : ℝ) (252372291773/500000000000 : ℝ) (3943317059/7812500000 : ℝ) (497733312597/1000000000000 : ℝ) (124433328151/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 2 (252372291773/500000000000 : ℝ) (3943317059/7812500000 : ℝ) (497733312597/1000000000000 : ℝ) (124433328151/250000000000 : ℝ) (501238948071/1000000000000 : ℝ) (250619474039/500000000000 : ℝ) (250613344409/500000000000 : ℝ) (20049067553/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 3 (501238948071/1000000000000 : ℝ) (250619474039/500000000000 : ℝ) (250613344409/500000000000 : ℝ) (20049067553/40000000000 : ℝ) (125308204611/250000000000 : ℝ) (125308204613/250000000000 : ℝ) (501232818407/1000000000000 : ℝ) (100246563683/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 4 (125308204611/250000000000 : ℝ) (125308204613/250000000000 : ℝ) (501232818407/1000000000000 : ℝ) (100246563683/200000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 5 (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 6 (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33439/262144 : ℝ))) 7 (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33439/262144 : ℝ)) hmem 8 (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33439/262144 : ℝ))) hcmem 8 (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33439/262144 : ℝ)) (992074981/1000000000 : ℝ) (992074981003/1000000000000 : ℝ) (20049312737/40000000000 : ℝ) (250616409217/500000000000 : ℝ) (99203019571/125000000000 : ℝ) (158724831317/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0805_exp_lower
  have heNumeric : (2054901590673/1000000000000 : ℝ)/4 ≤ Real.exp (-17051299892951/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901590673/1000000000000 : ℝ)/4 ≤ Real.exp ((66877/524288 : ℝ)-(158724831317/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66877/524288 : ℝ) (33439/262144 : ℝ) (158724831317/200000000000 : ℝ) (2054901590673/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0806; no trusted numerical premise.
theorem cover8_leaf0806_exp_radius : (499004417742256937/500000000000000000 : ℝ) ≤ Real.exp ((-66879/4194304 : ℝ)/8) ∧ Real.exp ((-66879/4194304 : ℝ)/8) ≤ (7984070683876111/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66879/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0806_exp_lower : (920113450859280571/1000000000000000000 : ℝ) ≤ Real.exp ((-42628249799921/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628249799921/64000000000000 : ℝ)/8) ≤ (230028362714820143/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628249799921/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0806_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862698563/125000000000 : ℝ) ≤ 4*Real.exp (33439/262144 : ℝ)*Real.exp (-mu (radius 8 (66879/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862698563/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66879/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0806_exp_radius
  have hrNumeric : (984181255497/1000000000000 : ℝ) ≤ Real.exp (-66879/4194304 : ℝ) ∧ Real.exp (-66879/4194304 : ℝ) ≤ (492090627749/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984181255497/1000000000000 : ℝ) ≤ (radius 8 (66879/524288 : ℝ)) ∧ (radius 8 (66879/524288 : ℝ)) ≤ (492090627749/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66879/524288 : ℝ)) (984181255497/1000000000000 : ℝ) (492090627749/500000000000 : ℝ) (88582244731/500000000000 : ℝ) (44291122367/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66879/524288 : ℝ)) (984181255497/1000000000000 : ℝ) (492090627749/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984181255497/1000000000000 : ℝ) (492090627749/500000000000 : ℝ) (248022656937/250000000000 : ℝ) (992090627749/1000000000000 : ℝ) (124007387349/125000000000 : ℝ) (496029549397/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 1 (248022656937/250000000000 : ℝ) (992090627749/1000000000000 : ℝ) (124007387349/125000000000 : ℝ) (496029549397/500000000000 : ℝ) (99207486327/100000000000 : ℝ) (124009357909/125000000000 : ℝ) (124009357893/125000000000 : ℝ) (992074863147/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 2 (99207486327/100000000000 : ℝ) (124009357909/125000000000 : ℝ) (124009357893/125000000000 : ℝ) (992074863147/1000000000000 : ℝ) (992074863207/1000000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 3 (992074863207/1000000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 4 (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 5 (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 6 (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66879/524288 : ℝ)) 7 (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66879/524288 : ℝ))) (88582244731/500000000000 : ℝ) (44291122367/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88582244731/500000000000 : ℝ) (44291122367/250000000000 : ℝ) (588582244731/1000000000000 : ℝ) (294291122367/500000000000 : ℝ) (420909122569/1000000000000 : ℝ) (420909122577/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 1 (588582244731/1000000000000 : ℝ) (294291122367/500000000000 : ℝ) (420909122569/1000000000000 : ℝ) (420909122577/1000000000000 : ℝ) (10094913673/20000000000 : ℝ) (63093210457/125000000000 : ℝ) (124433625929/250000000000 : ℝ) (497734503723/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 2 (10094913673/20000000000 : ℝ) (63093210457/125000000000 : ℝ) (124433625929/250000000000 : ℝ) (497734503723/1000000000000 : ℝ) (501240093683/1000000000000 : ℝ) (50124009369/100000000000 : ℝ) (62653479347/125000000000 : ℝ) (501227834783/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 3 (501240093683/1000000000000 : ℝ) (50124009369/100000000000 : ℝ) (62653479347/125000000000 : ℝ) (501227834783/1000000000000 : ℝ) (501233964229/1000000000000 : ℝ) (501233964237/1000000000000 : ℝ) (15663561381/31250000000 : ℝ) (2506169821/5000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 4 (501233964229/1000000000000 : ℝ) (501233964237/1000000000000 : ℝ) (15663561381/31250000000 : ℝ) (2506169821/5000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 5 (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 6 (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66879/524288 : ℝ))) 7 (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66879/524288 : ℝ)) hmem 8 (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66879/524288 : ℝ))) hcmem 8 (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66879/524288 : ℝ)) (496037431603/500000000000 : ℝ) (99207486321/100000000000 : ℝ) (50123396421/100000000000 : ℝ) (501233964219/1000000000000 : ℝ) (79362606497/100000000000 : ℝ) (793626064989/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0806_exp_lower
  have heNumeric : (256862698563/125000000000 : ℝ)/4 ≤ Real.exp (-42628249799921/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862698563/125000000000 : ℝ)/4 ≤ Real.exp ((33439/262144 : ℝ)-(793626064989/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33439/262144 : ℝ) (66879/524288 : ℝ) (793626064989/1000000000000 : ℝ) (256862698563/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0807; no trusted numerical premise.
theorem cover8_leaf0807_exp_radius : (124751100717691657/125000000000000000 : ℝ) ≤ Real.exp ((-1045/65536 : ℝ)/8) ∧ Real.exp ((-1045/65536 : ℝ)/8) ≤ (998008805741533257/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1045/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0807_exp_lower : (115014181342567963/125000000000000000 : ℝ) ≤ Real.exp ((-17051299946397/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051299946397/25600000000000 : ℝ)/8) ≤ (184022690148108741/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051299946397/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0807_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901586383/1000000000000 : ℝ) ≤ 4*Real.exp (66879/524288 : ℝ)*Real.exp (-mu (radius 8 (1045/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901586383/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1045/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0807_exp_radius
  have hrNumeric : (19683620417/20000000000 : ℝ) ≤ Real.exp (-1045/65536 : ℝ) ∧ Real.exp (-1045/65536 : ℝ) ≤ (984181020851/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19683620417/20000000000 : ℝ) ≤ (radius 8 (1045/8192 : ℝ)) ∧ (radius 8 (1045/8192 : ℝ)) ≤ (984181020851/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1045/8192 : ℝ)) (19683620417/20000000000 : ℝ) (984181020851/1000000000000 : ℝ) (44291448241/250000000000 : ℝ) (17716579297/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1045/8192 : ℝ)) (19683620417/20000000000 : ℝ) (984181020851/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19683620417/20000000000 : ℝ) (984181020851/1000000000000 : ℝ) (39683620417/40000000000 : ℝ) (496045255213/500000000000 : ℝ) (992058980529/1000000000000 : ℝ) (992058980531/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 1 (39683620417/40000000000 : ℝ) (496045255213/500000000000 : ℝ) (992058980529/1000000000000 : ℝ) (992058980531/1000000000000 : ℝ) (992074745477/1000000000000 : ℝ) (992074745479/1000000000000 : ℝ) (992074745351/1000000000000 : ℝ) (496037372677/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 2 (992074745477/1000000000000 : ℝ) (992074745479/1000000000000 : ℝ) (992074745351/1000000000000 : ℝ) (496037372677/500000000000 : ℝ) (496037372707/500000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 3 (496037372707/500000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 4 (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 5 (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 6 (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1045/8192 : ℝ)) 7 (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1045/8192 : ℝ))) (44291448241/250000000000 : ℝ) (17716579297/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44291448241/250000000000 : ℝ) (17716579297/100000000000 : ℝ) (294291448241/500000000000 : ℝ) (117716579297/200000000000 : ℝ) (210455335501/500000000000 : ℝ) (42091067101/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 1 (294291448241/500000000000 : ℝ) (117716579297/200000000000 : ℝ) (210455335501/500000000000 : ℝ) (42091067101/100000000000 : ℝ) (252373391871/500000000000 : ℝ) (126186695937/250000000000 : ℝ) (24886784741/50000000000 : ℝ) (497735694827/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 2 (252373391871/500000000000 : ℝ) (126186695937/250000000000 : ℝ) (24886784741/50000000000 : ℝ) (497735694827/1000000000000 : ℝ) (501241239281/1000000000000 : ℝ) (62655154911/125000000000 : ℝ) (6265362259/12500000000 : ℝ) (501228980727/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 3 (501241239281/1000000000000 : ℝ) (62655154911/125000000000 : ℝ) (6265362259/12500000000 : ℝ) (501228980727/1000000000000 : ℝ) (50123511/100000000 : ℝ) (62654388751/125000000000 : ℝ) (501235109963/1000000000000 : ℝ) (501235109971/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 4 (50123511/100000000 : ℝ) (62654388751/125000000000 : ℝ) (501235109963/1000000000000 : ℝ) (501235109971/1000000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 5 (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 6 (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1045/8192 : ℝ))) 7 (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1045/8192 : ℝ)) hmem 8 (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1045/8192 : ℝ))) hcmem 8 (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1045/8192 : ℝ)) (992074745413/1000000000000 : ℝ) (992074745417/1000000000000 : ℝ) (501235109981/1000000000000 : ℝ) (50123510999/100000000000 : ℝ) (793627973351/1000000000000 : ℝ) (79362797337/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0807_exp_lower
  have heNumeric : (2054901586383/1000000000000 : ℝ)/4 ≤ Real.exp (-17051299946397/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901586383/1000000000000 : ℝ)/4 ≤ Real.exp ((66879/524288 : ℝ)-(79362797337/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66879/524288 : ℝ) (1045/8192 : ℝ) (79362797337/100000000000 : ℝ) (2054901586383/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0808; no trusted numerical premise.
theorem cover8_leaf0808_exp_radius : (39920351039942141/40000000000000000 : ℝ) ≤ Real.exp ((-66881/4194304 : ℝ)/8) ∧ Real.exp ((-66881/4194304 : ℝ)/8) ≤ (499004387999276763/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66881/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0808_exp_lower : (460056725311881039/500000000000000000 : ℝ) ≤ Real.exp ((-1332132810343/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332132810343/2000000000000 : ℝ)/8) ≤ (920113450623762079/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332132810343/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0808_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901584297/1000000000000 : ℝ) ≤ 4*Real.exp (1045/8192 : ℝ)*Real.exp (-mu (radius 8 (66881/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901584297/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66881/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0808_exp_radius
  have hrNumeric : (984180786203/1000000000000 : ℝ) ≤ Real.exp (-66881/4194304 : ℝ) ∧ Real.exp (-66881/4194304 : ℝ) ≤ (246045196551/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984180786203/1000000000000 : ℝ) ≤ (radius 8 (66881/524288 : ℝ)) ∧ (radius 8 (66881/524288 : ℝ)) ≤ (246045196551/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66881/524288 : ℝ)) (984180786203/1000000000000 : ℝ) (246045196551/250000000000 : ℝ) (22145887057/125000000000 : ℝ) (177167096463/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66881/524288 : ℝ)) (984180786203/1000000000000 : ℝ) (246045196551/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984180786203/1000000000000 : ℝ) (246045196551/250000000000 : ℝ) (992090393101/1000000000000 : ℝ) (496045196551/500000000000 : ℝ) (992058862267/1000000000000 : ℝ) (248014715567/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 1 (992090393101/1000000000000 : ℝ) (496045196551/500000000000 : ℝ) (992058862267/1000000000000 : ℝ) (248014715567/250000000000 : ℝ) (248018656921/250000000000 : ℝ) (198414925537/200000000000 : ℝ) (496037313779/500000000000 : ℝ) (24801865689/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 2 (248018656921/250000000000 : ℝ) (198414925537/200000000000 : ℝ) (496037313779/500000000000 : ℝ) (24801865689/25000000000 : ℝ) (992074627621/1000000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 3 (992074627621/1000000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 4 (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 5 (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 6 (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66881/524288 : ℝ)) 7 (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66881/524288 : ℝ))) (22145887057/125000000000 : ℝ) (177167096463/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22145887057/125000000000 : ℝ) (177167096463/1000000000000 : ℝ) (147145887057/250000000000 : ℝ) (73572943529/125000000000 : ℝ) (210456109709/500000000000 : ℝ) (105228054857/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 1 (147145887057/250000000000 : ℝ) (73572943529/125000000000 : ℝ) (210456109709/500000000000 : ℝ) (105228054857/250000000000 : ℝ) (504747883823/1000000000000 : ℝ) (50474788383/100000000000 : ℝ) (62217110739/125000000000 : ℝ) (3110855537/6250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 2 (504747883823/1000000000000 : ℝ) (50474788383/100000000000 : ℝ) (62217110739/125000000000 : ℝ) (3110855537/6250000000 : ℝ) (501242384867/1000000000000 : ℝ) (4009939079/8000000000 : ℝ) (501230126653/1000000000000 : ℝ) (501230126661/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 3 (501242384867/1000000000000 : ℝ) (4009939079/8000000000 : ℝ) (501230126653/1000000000000 : ℝ) (501230126661/1000000000000 : ℝ) (6265453197/12500000000 : ℝ) (62654531971/125000000000 : ℝ) (250618127861/500000000000 : ℝ) (501236255731/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 4 (6265453197/12500000000 : ℝ) (62654531971/125000000000 : ℝ) (250618127861/500000000000 : ℝ) (501236255731/1000000000000 : ℝ) (501236255741/1000000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 5 (501236255741/1000000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 6 (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66881/524288 : ℝ))) 7 (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66881/524288 : ℝ)) hmem 8 (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66881/524288 : ℝ))) hcmem 8 (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66881/524288 : ℝ)) (49603731381/50000000000 : ℝ) (992074627623/1000000000000 : ℝ) (25061812787/50000000000 : ℝ) (2004945023/4000000000 : ℝ) (396814940857/500000000000 : ℝ) (396814940867/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0808_exp_lower
  have heNumeric : (2054901584297/1000000000000 : ℝ)/4 ≤ Real.exp (-1332132810343/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901584297/1000000000000 : ℝ)/4 ≤ Real.exp ((1045/8192 : ℝ)-(396814940867/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1045/8192 : ℝ) (66881/524288 : ℝ) (396814940867/500000000000 : ℝ) (2054901584297/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0809; no trusted numerical premise.
theorem cover8_leaf0809_exp_radius : (24950218656389367/25000000000000000 : ℝ) ≤ Real.exp ((-33441/2097152 : ℝ)/8) ∧ Real.exp ((-33441/2097152 : ℝ)/8) ≤ (998008746255574681/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33441/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0809_exp_lower : (3680453802037583/4000000000000000 : ℝ) ≤ Real.exp ((-85256499989231/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256499989231/128000000000000 : ℝ)/8) ≤ (920113450509395751/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256499989231/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0809_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901582253/1000000000000 : ℝ) ≤ 4*Real.exp (66881/524288 : ℝ)*Real.exp (-mu (radius 8 (33441/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901582253/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33441/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0809_exp_radius
  have hrNumeric : (246045137889/250000000000 : ℝ) ≤ Real.exp (-33441/2097152 : ℝ) ∧ Real.exp (-33441/2097152 : ℝ) ≤ (984180551557/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246045137889/250000000000 : ℝ) ≤ (radius 8 (33441/262144 : ℝ)) ∧ (radius 8 (33441/262144 : ℝ)) ≤ (984180551557/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33441/262144 : ℝ)) (246045137889/250000000000 : ℝ) (984180551557/1000000000000 : ℝ) (177168399939/1000000000000 : ℝ) (35433679989/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33441/262144 : ℝ)) (246045137889/250000000000 : ℝ) (984180551557/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246045137889/250000000000 : ℝ) (984180551557/1000000000000 : ℝ) (496045137889/500000000000 : ℝ) (992090275779/1000000000000 : ℝ) (248014686001/250000000000 : ℝ) (496029372003/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 1 (496045137889/500000000000 : ℝ) (992090275779/1000000000000 : ℝ) (248014686001/250000000000 : ℝ) (496029372003/500000000000 : ℝ) (992074509891/1000000000000 : ℝ) (992074509893/1000000000000 : ℝ) (198414901953/200000000000 : ℝ) (124009313721/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 2 (992074509891/1000000000000 : ℝ) (992074509893/1000000000000 : ℝ) (198414901953/200000000000 : ℝ) (124009313721/125000000000 : ℝ) (248018627457/250000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 3 (248018627457/250000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 4 (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 5 (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 6 (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33441/262144 : ℝ)) 7 (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33441/262144 : ℝ))) (177168399939/1000000000000 : ℝ) (35433679989/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177168399939/1000000000000 : ℝ) (35433679989/200000000000 : ℝ) (588584199969/1000000000000 : ℝ) (588584199973/1000000000000 : ℝ) (210456883909/500000000000 : ℝ) (210456883913/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 1 (588584199969/1000000000000 : ℝ) (588584199973/1000000000000 : ℝ) (210456883909/500000000000 : ℝ) (210456883913/500000000000 : ℝ) (504748983893/1000000000000 : ℝ) (5047489839/10000000000 : ℝ) (497738076991/1000000000000 : ℝ) (248869038499/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 2 (504748983893/1000000000000 : ℝ) (5047489839/10000000000 : ℝ) (497738076991/1000000000000 : ℝ) (248869038499/500000000000 : ℝ) (250621765221/500000000000 : ℝ) (501243530449/1000000000000 : ℝ) (501231272573/1000000000000 : ℝ) (501231272581/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 3 (250621765221/500000000000 : ℝ) (501243530449/1000000000000 : ℝ) (501231272573/1000000000000 : ℝ) (501231272581/1000000000000 : ℝ) (501237401507/1000000000000 : ℝ) (100247480303/200000000000 : ℝ) (50123740147/100000000000 : ℝ) (250618700739/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 4 (501237401507/1000000000000 : ℝ) (100247480303/200000000000 : ℝ) (50123740147/100000000000 : ℝ) (250618700739/500000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 5 (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 6 (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33441/262144 : ℝ))) 7 (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33441/262144 : ℝ)) hmem 8 (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33441/262144 : ℝ))) hcmem 8 (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33441/262144 : ℝ)) (992074509827/1000000000000 : ℝ) (992074509831/1000000000000 : ℝ) (31327337593/62500000000 : ℝ) (501237401497/1000000000000 : ℝ) (793631790059/1000000000000 : ℝ) (793631790077/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0809_exp_lower
  have heNumeric : (2054901582253/1000000000000 : ℝ)/4 ≤ Real.exp (-85256499989231/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901582253/1000000000000 : ℝ)/4 ≤ Real.exp ((66881/524288 : ℝ)-(793631790077/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66881/524288 : ℝ) (33441/262144 : ℝ) (793631790077/1000000000000 : ℝ) (2054901582253/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0810; no trusted numerical premise.
theorem cover8_leaf0810_exp_radius : (499004358256298361/500000000000000000 : ℝ) ≤ Real.exp ((-66883/4194304 : ℝ)/8) ∧ Real.exp ((-66883/4194304 : ℝ)/8) ≤ (998008716512596723/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66883/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0810_exp_lower : (920113450396869649/1000000000000000000 : ℝ) ≤ Real.exp ((-42628250057231/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250057231/64000000000000 : ℝ)/8) ≤ (18402269007937393/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250057231/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0810_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901580243/1000000000000 : ℝ) ≤ 4*Real.exp (33441/262144 : ℝ)*Real.exp (-mu (radius 8 (66883/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901580243/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66883/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0810_exp_radius
  have hrNumeric : (984180316909/1000000000000 : ℝ) ≤ Real.exp (-66883/4194304 : ℝ) ∧ Real.exp (-66883/4194304 : ℝ) ≤ (98418031691/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984180316909/1000000000000 : ℝ) ≤ (radius 8 (66883/524288 : ℝ)) ∧ (radius 8 (66883/524288 : ℝ)) ≤ (98418031691/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66883/524288 : ℝ)) (984180316909/1000000000000 : ℝ) (98418031691/100000000000 : ℝ) (177169703411/1000000000000 : ℝ) (88584851709/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66883/524288 : ℝ)) (984180316909/1000000000000 : ℝ) (98418031691/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984180316909/1000000000000 : ℝ) (98418031691/100000000000 : ℝ) (496045079227/500000000000 : ℝ) (198418031691/200000000000 : ℝ) (992058625741/1000000000000 : ℝ) (992058625743/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 1 (496045079227/500000000000 : ℝ) (198418031691/200000000000 : ℝ) (992058625741/1000000000000 : ℝ) (992058625743/1000000000000 : ℝ) (992074392097/1000000000000 : ℝ) (992074392099/1000000000000 : ℝ) (248018597993/250000000000 : ℝ) (496037195987/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 2 (992074392097/1000000000000 : ℝ) (992074392099/1000000000000 : ℝ) (248018597993/250000000000 : ℝ) (496037195987/500000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 3 (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 4 (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 5 (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 6 (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66883/524288 : ℝ)) 7 (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66883/524288 : ℝ))) (177169703411/1000000000000 : ℝ) (88584851709/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177169703411/1000000000000 : ℝ) (88584851709/500000000000 : ℝ) (117716970341/200000000000 : ℝ) (588584851709/1000000000000 : ℝ) (420915316199/1000000000000 : ℝ) (26307207263/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 1 (117716970341/200000000000 : ℝ) (588584851709/1000000000000 : ℝ) (420915316199/1000000000000 : ℝ) (26307207263/62500000000 : ℝ) (31546880247/62500000000 : ℝ) (504750083959/1000000000000 : ℝ) (62217408507/125000000000 : ℝ) (15554352127/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 2 (31546880247/62500000000 : ℝ) (504750083959/1000000000000 : ℝ) (62217408507/125000000000 : ℝ) (15554352127/31250000000 : ℝ) (125311169001/250000000000 : ℝ) (125311169003/250000000000 : ℝ) (250616209241/500000000000 : ℝ) (50123241849/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 3 (125311169001/250000000000 : ℝ) (125311169003/250000000000 : ℝ) (250616209241/500000000000 : ℝ) (50123241849/100000000000 : ℝ) (501238547243/1000000000000 : ℝ) (501238547251/1000000000000 : ℝ) (100247709441/200000000000 : ℝ) (250619273607/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 4 (501238547243/1000000000000 : ℝ) (501238547251/1000000000000 : ℝ) (100247709441/200000000000 : ℝ) (250619273607/500000000000 : ℝ) (62654818403/125000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 5 (62654818403/125000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 6 (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66883/524288 : ℝ))) 7 (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66883/524288 : ℝ)) hmem 8 (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66883/524288 : ℝ))) hcmem 8 (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66883/524288 : ℝ)) (496037196017/500000000000 : ℝ) (992074392037/1000000000000 : ℝ) (501238547223/1000000000000 : ℝ) (501238547233/1000000000000 : ℝ) (158726739677/200000000000 : ℝ) (198408424601/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0810_exp_lower
  have heNumeric : (2054901580243/1000000000000 : ℝ)/4 ≤ Real.exp (-42628250057231/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901580243/1000000000000 : ℝ)/4 ≤ Real.exp ((33441/262144 : ℝ)-(198408424601/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33441/262144 : ℝ) (66883/524288 : ℝ) (198408424601/250000000000 : ℝ) (2054901580243/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0811; no trusted numerical premise.
theorem cover8_leaf0811_exp_radius : (19960173735392393/20000000000000000 : ℝ) ≤ Real.exp ((-16721/1048576 : ℝ)/8) ∧ Real.exp ((-16721/1048576 : ℝ)/8) ≤ (998008686769619651/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16721/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0811_exp_lower : (46005672514343693/50000000000000000 : ℝ) ≤ Real.exp ((-85256500236877/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500236877/128000000000000 : ℝ)/8) ≤ (920113450286873861/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500236877/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0811_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450789139/500000000000 : ℝ) ≤ 4*Real.exp (66883/524288 : ℝ)*Real.exp (-mu (radius 8 (16721/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450789139/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16721/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0811_exp_radius
  have hrNumeric : (492090041131/500000000000 : ℝ) ≤ Real.exp (-16721/1048576 : ℝ) ∧ Real.exp (-16721/1048576 : ℝ) ≤ (984180082263/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492090041131/500000000000 : ℝ) ≤ (radius 8 (16721/131072 : ℝ)) ∧ (radius 8 (16721/131072 : ℝ)) ≤ (984180082263/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16721/131072 : ℝ)) (492090041131/500000000000 : ℝ) (984180082263/1000000000000 : ℝ) (88585503437/500000000000 : ℝ) (1107318793/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16721/131072 : ℝ)) (492090041131/500000000000 : ℝ) (984180082263/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492090041131/500000000000 : ℝ) (984180082263/1000000000000 : ℝ) (992090041131/1000000000000 : ℝ) (248022510283/250000000000 : ℝ) (992058507479/1000000000000 : ℝ) (24801462687/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 1 (992090041131/1000000000000 : ℝ) (248022510283/250000000000 : ℝ) (992058507479/1000000000000 : ℝ) (24801462687/25000000000 : ℝ) (198414854861/200000000000 : ℝ) (496037137153/500000000000 : ℝ) (992074274179/1000000000000 : ℝ) (992074274181/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 2 (198414854861/200000000000 : ℝ) (496037137153/500000000000 : ℝ) (992074274179/1000000000000 : ℝ) (992074274181/1000000000000 : ℝ) (496037137121/500000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 3 (496037137121/500000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 4 (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 5 (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 6 (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16721/131072 : ℝ)) 7 (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16721/131072 : ℝ))) (88585503437/500000000000 : ℝ) (1107318793/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88585503437/500000000000 : ℝ) (1107318793/6250000000 : ℝ) (588585503437/1000000000000 : ℝ) (7357318793/12500000000 : ℝ) (420916864563/1000000000000 : ℝ) (420916864571/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 1 (588585503437/1000000000000 : ℝ) (7357318793/12500000000 : ℝ) (420916864563/1000000000000 : ℝ) (420916864571/1000000000000 : ℝ) (31546949/62500000 : ℝ) (252375592003/500000000000 : ℝ) (124435114777/250000000000 : ℝ) (99548091823/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 2 (31546949/62500000 : ℝ) (252375592003/500000000000 : ℝ) (124435114777/250000000000 : ℝ) (99548091823/200000000000 : ℝ) (250622910777/500000000000 : ℝ) (501245821561/1000000000000 : ℝ) (250616782189/500000000000 : ℝ) (100246712877/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 3 (250622910777/500000000000 : ℝ) (501245821561/1000000000000 : ℝ) (250616782189/500000000000 : ℝ) (100246712877/200000000000 : ℝ) (250619846483/500000000000 : ℝ) (501239692973/1000000000000 : ℝ) (3915935101/7812500000 : ℝ) (62654961617/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 4 (250619846483/500000000000 : ℝ) (501239692973/1000000000000 : ℝ) (3915935101/7812500000 : ℝ) (62654961617/125000000000 : ℝ) (501239692947/1000000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 5 (501239692947/1000000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 6 (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16721/131072 : ℝ))) 7 (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16721/131072 : ℝ)) hmem 8 (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16721/131072 : ℝ))) hcmem 8 (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16721/131072 : ℝ)) (992074274241/1000000000000 : ℝ) (248018568561/250000000000 : ℝ) (250619846473/500000000000 : ℝ) (100247938591/200000000000 : ℝ) (198408901673/250000000000 : ℝ) (793635606709/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0811_exp_lower
  have heNumeric : (1027450789139/500000000000 : ℝ)/4 ≤ Real.exp (-85256500236877/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450789139/500000000000 : ℝ)/4 ≤ Real.exp ((66883/524288 : ℝ)-(793635606709/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66883/524288 : ℝ) (16721/131072 : ℝ) (793635606709/1000000000000 : ℝ) (1027450789139/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0812; no trusted numerical premise.
theorem cover8_leaf0812_exp_radius : (124751082128330433/125000000000000000 : ℝ) ≤ Real.exp ((-66885/4194304 : ℝ)/8) ∧ Real.exp ((-66885/4194304 : ℝ)/8) ≤ (199601731405328693/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66885/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0812_exp_lower : (230028362544650821/250000000000000000 : ℝ) ≤ Real.exp ((-21314125089343/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125089343/32000000000000 : ℝ)/8) ≤ (184022690035720657/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125089343/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0812_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901576343/1000000000000 : ℝ) ≤ 4*Real.exp (16721/131072 : ℝ)*Real.exp (-mu (radius 8 (66885/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901576343/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66885/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0812_exp_radius
  have hrNumeric : (196835969523/200000000000 : ℝ) ≤ Real.exp (-66885/4194304 : ℝ) ∧ Real.exp (-66885/4194304 : ℝ) ≤ (15377810119/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196835969523/200000000000 : ℝ) ≤ (radius 8 (66885/524288 : ℝ)) ∧ (radius 8 (66885/524288 : ℝ)) ≤ (15377810119/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66885/524288 : ℝ)) (196835969523/200000000000 : ℝ) (15377810119/15625000000 : ℝ) (88586155163/500000000000 : ℝ) (177172310333/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66885/524288 : ℝ)) (196835969523/200000000000 : ℝ) (15377810119/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196835969523/200000000000 : ℝ) (15377810119/15625000000 : ℝ) (992089923807/1000000000000 : ℝ) (31002810119/31250000000 : ℝ) (31001824663/31250000000 : ℝ) (496029194609/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 1 (992089923807/1000000000000 : ℝ) (31002810119/31250000000 : ℝ) (31001824663/31250000000 : ℝ) (496029194609/500000000000 : ℝ) (992074156511/1000000000000 : ℝ) (992074156513/1000000000000 : ℝ) (496037078193/500000000000 : ℝ) (248018539097/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 2 (992074156511/1000000000000 : ℝ) (992074156513/1000000000000 : ℝ) (496037078193/500000000000 : ℝ) (248018539097/250000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 3 (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 4 (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 5 (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 6 (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66885/524288 : ℝ)) 7 (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66885/524288 : ℝ))) (88586155163/500000000000 : ℝ) (177172310333/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88586155163/500000000000 : ℝ) (177172310333/1000000000000 : ℝ) (588586155163/1000000000000 : ℝ) (588586155167/1000000000000 : ℝ) (420918412909/1000000000000 : ℝ) (210459206459/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 1 (588586155163/1000000000000 : ℝ) (588586155167/1000000000000 : ℝ) (420918412909/1000000000000 : ℝ) (210459206459/500000000000 : ℝ) (126188071009/250000000000 : ℝ) (504752284043/1000000000000 : ℝ) (497741650147/1000000000000 : ℝ) (99548330031/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 2 (126188071009/250000000000 : ℝ) (504752284043/1000000000000 : ℝ) (497741650147/1000000000000 : ℝ) (99548330031/200000000000 : ℝ) (501246967091/1000000000000 : ℝ) (501246967099/1000000000000 : ℝ) (250617355131/500000000000 : ℝ) (50123471027/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 3 (501246967091/1000000000000 : ℝ) (501246967099/1000000000000 : ℝ) (250617355131/500000000000 : ℝ) (50123471027/100000000000 : ℝ) (125310209669/250000000000 : ℝ) (100248167737/200000000000 : ℝ) (501240838639/1000000000000 : ℝ) (62655104831/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 4 (125310209669/250000000000 : ℝ) (100248167737/200000000000 : ℝ) (501240838639/1000000000000 : ℝ) (62655104831/125000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 5 (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 6 (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66885/524288 : ℝ))) 7 (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66885/524288 : ℝ)) hmem 8 (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66885/524288 : ℝ))) hcmem 8 (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66885/524288 : ℝ)) (31002317389/31250000000 : ℝ) (992074156451/1000000000000 : ℝ) (501240838657/1000000000000 : ℝ) (501240838667/1000000000000 : ℝ) (39681875749/50000000000 : ℝ) (793637514999/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0812_exp_lower
  have heNumeric : (2054901576343/1000000000000 : ℝ)/4 ≤ Real.exp (-21314125089343/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901576343/1000000000000 : ℝ)/4 ≤ Real.exp ((16721/131072 : ℝ)-(793637514999/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16721/131072 : ℝ) (66885/524288 : ℝ) (793637514999/1000000000000 : ℝ) (2054901576343/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0813; no trusted numerical premise.
theorem cover8_leaf0813_exp_radius : (199601725456733633/200000000000000000 : ℝ) ≤ Real.exp ((-33443/2097152 : ℝ)/8) ∧ Real.exp ((-33443/2097152 : ℝ)/8) ≤ (499004313641834083/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33443/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0813_exp_lower : (920113450073783133/1000000000000000000 : ℝ) ≤ Real.exp ((-85256500474027/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500474027/128000000000000 : ℝ)/8) ≤ (460056725036891567/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500474027/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0813_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490157447/100000000000 : ℝ) ≤ 4*Real.exp (66885/524288 : ℝ)*Real.exp (-mu (radius 8 (33443/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490157447/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33443/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0813_exp_radius
  have hrNumeric : (984179612969/1000000000000 : ℝ) ≤ Real.exp (-33443/2097152 : ℝ) ∧ Real.exp (-33443/2097152 : ℝ) ≤ (98417961297/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984179612969/1000000000000 : ℝ) ≤ (radius 8 (33443/262144 : ℝ)) ∧ (radius 8 (33443/262144 : ℝ)) ≤ (98417961297/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33443/262144 : ℝ)) (984179612969/1000000000000 : ℝ) (98417961297/100000000000 : ℝ) (44293403441/250000000000 : ℝ) (17717361377/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33443/262144 : ℝ)) (984179612969/1000000000000 : ℝ) (98417961297/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984179612969/1000000000000 : ℝ) (98417961297/100000000000 : ℝ) (248022451621/250000000000 : ℝ) (198417961297/200000000000 : ℝ) (496029135477/500000000000 : ℝ) (198411654191/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 1 (248022451621/250000000000 : ℝ) (198417961297/200000000000 : ℝ) (496029135477/500000000000 : ℝ) (198411654191/200000000000 : ℝ) (992074038719/1000000000000 : ℝ) (3100231371/3125000000 : ℝ) (992074038593/1000000000000 : ℝ) (198414807719/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 2 (992074038719/1000000000000 : ℝ) (3100231371/3125000000 : ℝ) (992074038593/1000000000000 : ℝ) (198414807719/200000000000 : ℝ) (7750578427/7812500000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 3 (7750578427/7812500000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 4 (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 5 (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 6 (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33443/262144 : ℝ)) 7 (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33443/262144 : ℝ))) (44293403441/250000000000 : ℝ) (17717361377/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44293403441/250000000000 : ℝ) (17717361377/100000000000 : ℝ) (294293403441/500000000000 : ℝ) (117717361377/200000000000 : ℝ) (26307497577/62500000000 : ℝ) (10522999031/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 1 (294293403441/500000000000 : ℝ) (117717361377/200000000000 : ℝ) (26307497577/62500000000 : ℝ) (10522999031/25000000000 : ℝ) (504753384057/1000000000000 : ℝ) (504753384063/1000000000000 : ℝ) (31108927573/62500000000 : ℝ) (19909713647/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 2 (504753384057/1000000000000 : ℝ) (504753384063/1000000000000 : ℝ) (31108927573/62500000000 : ℝ) (19909713647/40000000000 : ℝ) (125312028153/250000000000 : ℝ) (501248112619/1000000000000 : ℝ) (501235856129/1000000000000 : ℝ) (62654482017/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 3 (125312028153/250000000000 : ℝ) (501248112619/1000000000000 : ℝ) (501235856129/1000000000000 : ℝ) (62654482017/125000000000 : ℝ) (50124198437/100000000000 : ℝ) (250620992189/500000000000 : ℝ) (501241984333/1000000000000 : ℝ) (501241984341/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 4 (50124198437/100000000000 : ℝ) (250620992189/500000000000 : ℝ) (501241984333/1000000000000 : ℝ) (501241984341/1000000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 5 (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 6 (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33443/262144 : ℝ))) 7 (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33443/262144 : ℝ)) hmem 8 (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33443/262144 : ℝ))) hcmem 8 (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33443/262144 : ℝ)) (198414807731/200000000000 : ℝ) (496037019329/500000000000 : ℝ) (501241984351/1000000000000 : ℝ) (12531049609/25000000000 : ℝ) (396819711621/500000000000 : ℝ) (793639423259/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0813_exp_lower
  have heNumeric : (205490157447/100000000000 : ℝ)/4 ≤ Real.exp (-85256500474027/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490157447/100000000000 : ℝ)/4 ≤ Real.exp ((66885/524288 : ℝ)-(793639423259/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66885/524288 : ℝ) (33443/262144 : ℝ) (793639423259/1000000000000 : ℝ) (205490157447/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0814; no trusted numerical premise.
theorem cover8_leaf0814_exp_radius : (124751074692586719/125000000000000000 : ℝ) ≤ Real.exp ((-66887/4194304 : ℝ)/8) ∧ Real.exp ((-66887/4194304 : ℝ)/8) ≤ (998008597540693753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66887/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0814_exp_lower : (92011344996999811/100000000000000000 : ℝ) ≤ Real.exp ((-8525650058953/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525650058953/12800000000000 : ℝ)/8) ≤ (920113449969998111/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525650058953/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0814_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862696577/125000000000 : ℝ) ≤ 4*Real.exp (33443/262144 : ℝ)*Real.exp (-mu (radius 8 (66887/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862696577/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66887/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0814_exp_radius
  have hrNumeric : (492089689161/500000000000 : ℝ) ≤ Real.exp (-66887/4194304 : ℝ) ∧ Real.exp (-66887/4194304 : ℝ) ≤ (984179378323/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492089689161/500000000000 : ℝ) ≤ (radius 8 (66887/524288 : ℝ)) ∧ (radius 8 (66887/524288 : ℝ)) ≤ (984179378323/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66887/524288 : ℝ)) (492089689161/500000000000 : ℝ) (984179378323/1000000000000 : ℝ) (44293729299/250000000000 : ℝ) (177174917203/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66887/524288 : ℝ)) (492089689161/500000000000 : ℝ) (984179378323/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492089689161/500000000000 : ℝ) (984179378323/1000000000000 : ℝ) (992089689161/1000000000000 : ℝ) (496044844581/500000000000 : ℝ) (992058152691/1000000000000 : ℝ) (992058152693/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 1 (992089689161/1000000000000 : ℝ) (496044844581/500000000000 : ℝ) (992058152691/1000000000000 : ℝ) (992058152693/1000000000000 : ℝ) (496036960463/500000000000 : ℝ) (31002310029/31250000000 : ℝ) (1240092401/1250000000 : ℝ) (992073920803/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 2 (496036960463/500000000000 : ℝ) (31002310029/31250000000 : ℝ) (1240092401/1250000000 : ℝ) (992073920803/1000000000000 : ℝ) (992073920863/1000000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 3 (992073920863/1000000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 4 (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 5 (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 6 (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66887/524288 : ℝ)) 7 (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66887/524288 : ℝ))) (44293729299/250000000000 : ℝ) (177174917203/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44293729299/250000000000 : ℝ) (177174917203/1000000000000 : ℝ) (294293729299/500000000000 : ℝ) (294293729301/500000000000 : ℝ) (420921509543/1000000000000 : ℝ) (26307594347/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 1 (294293729299/500000000000 : ℝ) (294293729301/500000000000 : ℝ) (420921509543/1000000000000 : ℝ) (26307594347/62500000000 : ℝ) (50475448407/100000000000 : ℝ) (504754484077/1000000000000 : ℝ) (24887201609/50000000000 : ℝ) (124436008047/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 2 (50475448407/100000000000 : ℝ) (504754484077/1000000000000 : ℝ) (24887201609/50000000000 : ℝ) (124436008047/250000000000 : ℝ) (801998813/1600000000 : ℝ) (501249258133/1000000000000 : ℝ) (125309250497/250000000000 : ℝ) (125309250499/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 3 (801998813/1600000000 : ℝ) (501249258133/1000000000000 : ℝ) (125309250497/250000000000 : ℝ) (125309250499/250000000000 : ℝ) (62655391257/125000000000 : ℝ) (100248626013/200000000000 : ℝ) (501243130019/1000000000000 : ℝ) (125310782507/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 4 (62655391257/125000000000 : ℝ) (100248626013/200000000000 : ℝ) (501243130019/1000000000000 : ℝ) (125310782507/250000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 5 (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 6 (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66887/524288 : ℝ))) 7 (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66887/524288 : ℝ)) hmem 8 (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66887/524288 : ℝ))) hcmem 8 (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66887/524288 : ℝ)) (496036960431/500000000000 : ℝ) (496036960433/500000000000 : ℝ) (501243130037/1000000000000 : ℝ) (501243130047/1000000000000 : ℝ) (79364133149/100000000000 : ℝ) (79364133151/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0814_exp_lower
  have heNumeric : (256862696577/125000000000 : ℝ)/4 ≤ Real.exp (-8525650058953/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862696577/125000000000 : ℝ)/4 ≤ Real.exp ((33443/262144 : ℝ)-(79364133151/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33443/262144 : ℝ) (66887/524288 : ℝ) (79364133151/100000000000 : ℝ) (256862696577/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0815; no trusted numerical premise.
theorem cover8_leaf0815_exp_radius : (499004283898860113/500000000000000000 : ℝ) ≤ Real.exp ((-8361/524288 : ℝ)/8) ∧ Real.exp ((-8361/524288 : ℝ)/8) ≤ (998008567797720227/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8361/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0815_exp_lower : (92011344986851337/100000000000000000 : ℝ) ≤ Real.exp ((-85256500702473/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500702473/128000000000000 : ℝ)/8) ≤ (920113449868513371/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500702473/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0815_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901570803/1000000000000 : ℝ) ≤ 4*Real.exp (66887/524288 : ℝ)*Real.exp (-mu (radius 8 (8361/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901570803/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8361/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0815_exp_radius
  have hrNumeric : (39367165747/40000000000 : ℝ) ≤ Real.exp (-8361/524288 : ℝ) ∧ Real.exp (-8361/524288 : ℝ) ≤ (246044785919/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39367165747/40000000000 : ℝ) ≤ (radius 8 (8361/65536 : ℝ)) ∧ (radius 8 (8361/65536 : ℝ)) ≤ (246044785919/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8361/65536 : ℝ)) (39367165747/40000000000 : ℝ) (246044785919/250000000000 : ℝ) (177176220619/1000000000000 : ℝ) (88588110313/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8361/65536 : ℝ)) (39367165747/40000000000 : ℝ) (246044785919/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39367165747/40000000000 : ℝ) (246044785919/250000000000 : ℝ) (992089571837/1000000000000 : ℝ) (496044785919/500000000000 : ℝ) (248014508607/250000000000 : ℝ) (99205803443/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 1 (992089571837/1000000000000 : ℝ) (496044785919/500000000000 : ℝ) (248014508607/250000000000 : ℝ) (99205803443/100000000000 : ℝ) (248018450783/250000000000 : ℝ) (496036901567/500000000000 : ℝ) (992073803007/1000000000000 : ℝ) (992073803009/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 2 (248018450783/250000000000 : ℝ) (496036901567/500000000000 : ℝ) (992073803007/1000000000000 : ℝ) (992073803009/1000000000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 3 (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 4 (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 5 (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 6 (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8361/65536 : ℝ)) 7 (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8361/65536 : ℝ))) (177176220619/1000000000000 : ℝ) (88588110313/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177176220619/1000000000000 : ℝ) (88588110313/500000000000 : ℝ) (588588110309/1000000000000 : ℝ) (588588110313/1000000000000 : ℝ) (420923057837/1000000000000 : ℝ) (210461528923/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 1 (588588110309/1000000000000 : ℝ) (588588110313/1000000000000 : ℝ) (420923057837/1000000000000 : ℝ) (210461528923/500000000000 : ℝ) (504755584073/1000000000000 : ℝ) (6309444801/12500000000 : ℝ) (497745223179/1000000000000 : ℝ) (497745223187/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 2 (504755584073/1000000000000 : ℝ) (6309444801/12500000000 : ℝ) (497745223179/1000000000000 : ℝ) (497745223187/1000000000000 : ℝ) (250625201813/500000000000 : ℝ) (250625201817/500000000000 : ℝ) (100247629567/200000000000 : ℝ) (501238147843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 3 (250625201813/500000000000 : ℝ) (250625201817/500000000000 : ℝ) (100247629567/200000000000 : ℝ) (501238147843/1000000000000 : ℝ) (50124427573/100000000000 : ℝ) (501244275739/1000000000000 : ℝ) (501244275693/1000000000000 : ℝ) (250622137851/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 4 (50124427573/100000000000 : ℝ) (501244275739/1000000000000 : ℝ) (501244275693/1000000000000 : ℝ) (250622137851/500000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 5 (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 6 (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8361/65536 : ℝ))) 7 (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8361/65536 : ℝ)) hmem 8 (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8361/65536 : ℝ))) hcmem 8 (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8361/65536 : ℝ)) (992073803069/1000000000000 : ℝ) (15501153173/15625000000 : ℝ) (501244275711/1000000000000 : ℝ) (501244275721/1000000000000 : ℝ) (396821619861/500000000000 : ℝ) (793643239741/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0815_exp_lower
  have heNumeric : (2054901570803/1000000000000 : ℝ)/4 ≤ Real.exp (-85256500702473/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901570803/1000000000000 : ℝ)/4 ≤ Real.exp ((66887/524288 : ℝ)-(793643239741/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66887/524288 : ℝ) (8361/65536 : ℝ) (793643239741/1000000000000 : ℝ) (2054901570803/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0816; no trusted numerical premise.
theorem cover8_leaf0816_exp_radius : (499004269027373793/500000000000000000 : ℝ) ≤ Real.exp ((-66889/4194304 : ℝ)/8) ∧ Real.exp ((-66889/4194304 : ℝ)/8) ≤ (998008538054747587/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66889/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0816_exp_lower : (920113449770018999/1000000000000000000 : ℝ) ≤ Real.exp ((-10657062601511/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062601511/16000000000000 : ℝ)/8) ≤ (920113449770019/1000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062601511/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0816_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901569043/1000000000000 : ℝ) ≤ 4*Real.exp (8361/65536 : ℝ)*Real.exp (-mu (radius 8 (66889/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901569043/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66889/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0816_exp_radius
  have hrNumeric : (984178909029/1000000000000 : ℝ) ≤ Real.exp (-66889/4194304 : ℝ) ∧ Real.exp (-66889/4194304 : ℝ) ≤ (98417890903/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984178909029/1000000000000 : ℝ) ≤ (radius 8 (66889/524288 : ℝ)) ∧ (radius 8 (66889/524288 : ℝ)) ≤ (98417890903/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66889/524288 : ℝ)) (984178909029/1000000000000 : ℝ) (98417890903/100000000000 : ℝ) (177177524027/1000000000000 : ℝ) (88588762017/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66889/524288 : ℝ)) (984178909029/1000000000000 : ℝ) (98417890903/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984178909029/1000000000000 : ℝ) (98417890903/100000000000 : ℝ) (496044727257/500000000000 : ℝ) (198417890903/200000000000 : ℝ) (496028958083/500000000000 : ℝ) (124007239521/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 1 (496044727257/500000000000 : ℝ) (198417890903/200000000000 : ℝ) (496028958083/500000000000 : ℝ) (124007239521/125000000000 : ℝ) (49603684267/50000000000 : ℝ) (496036842671/500000000000 : ℝ) (496036842607/500000000000 : ℝ) (992073685217/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 2 (49603684267/50000000000 : ℝ) (496036842671/500000000000 : ℝ) (496036842607/500000000000 : ℝ) (992073685217/1000000000000 : ℝ) (992073685277/1000000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 3 (992073685277/1000000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 4 (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 5 (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 6 (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66889/524288 : ℝ)) 7 (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66889/524288 : ℝ))) (177177524027/1000000000000 : ℝ) (88588762017/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177177524027/1000000000000 : ℝ) (88588762017/500000000000 : ℝ) (588588762013/1000000000000 : ℝ) (588588762017/1000000000000 : ℝ) (420924606107/1000000000000 : ℝ) (420924606117/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 1 (588588762013/1000000000000 : ℝ) (588588762017/1000000000000 : ℝ) (420924606107/1000000000000 : ℝ) (420924606117/1000000000000 : ℝ) (25237834203/50000000000 : ℝ) (504756684067/1000000000000 : ℝ) (6221830177/12500000000 : ℝ) (62218301771/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 2 (25237834203/50000000000 : ℝ) (504756684067/1000000000000 : ℝ) (6221830177/12500000000 : ℝ) (62218301771/125000000000 : ℝ) (50125154911/100000000000 : ℝ) (250625774559/500000000000 : ℝ) (100247858733/200000000000 : ℝ) (501239293673/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 3 (50125154911/100000000000 : ℝ) (250625774559/500000000000 : ℝ) (100247858733/200000000000 : ℝ) (501239293673/1000000000000 : ℝ) (501245421387/1000000000000 : ℝ) (125311355349/250000000000 : ℝ) (10024908427/20000000000 : ℝ) (501245421359/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 4 (501245421387/1000000000000 : ℝ) (125311355349/250000000000 : ℝ) (10024908427/20000000000 : ℝ) (501245421359/1000000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 5 (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 6 (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66889/524288 : ℝ))) 7 (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66889/524288 : ℝ)) hmem 8 (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66889/524288 : ℝ))) hcmem 8 (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66889/524288 : ℝ)) (248018421319/250000000000 : ℝ) (6200460533/6250000000 : ℝ) (62655677671/125000000000 : ℝ) (250622710689/500000000000 : ℝ) (396822573963/500000000000 : ℝ) (396822573973/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0816_exp_lower
  have heNumeric : (2054901569043/1000000000000 : ℝ)/4 ≤ Real.exp (-10657062601511/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901569043/1000000000000 : ℝ)/4 ≤ Real.exp ((8361/65536 : ℝ)-(396822573973/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8361/65536 : ℝ) (66889/524288 : ℝ) (396822573973/500000000000 : ℝ) (2054901569043/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0817; no trusted numerical premise.
theorem cover8_leaf0817_exp_radius : (124751063538971979/125000000000000000 : ℝ) ≤ Real.exp ((-33445/2097152 : ℝ)/8) ∧ Real.exp ((-33445/2097152 : ℝ)/8) ≤ (998008508311775833/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33445/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0817_exp_lower : (920113449672904799/1000000000000000000 : ℝ) ≤ Real.exp ((-85256500920167/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500920167/128000000000000 : ℝ)/8) ≤ (1150141812091131/1250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500920167/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0817_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725391827/250000000000 : ℝ) ≤ 4*Real.exp (66889/524288 : ℝ)*Real.exp (-mu (radius 8 (33445/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725391827/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33445/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0817_exp_radius
  have hrNumeric : (492089337191/500000000000 : ℝ) ≤ Real.exp (-33445/2097152 : ℝ) ∧ Real.exp (-33445/2097152 : ℝ) ≤ (984178674383/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492089337191/500000000000 : ℝ) ≤ (radius 8 (33445/262144 : ℝ)) ∧ (radius 8 (33445/262144 : ℝ)) ≤ (984178674383/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33445/262144 : ℝ)) (492089337191/500000000000 : ℝ) (984178674383/1000000000000 : ℝ) (17717882743/100000000000 : ℝ) (177178827437/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33445/262144 : ℝ)) (492089337191/500000000000 : ℝ) (984178674383/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492089337191/500000000000 : ℝ) (984178674383/1000000000000 : ℝ) (992089337191/1000000000000 : ℝ) (124011167149/125000000000 : ℝ) (992057797903/1000000000000 : ℝ) (198411559581/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 1 (992089337191/1000000000000 : ℝ) (124011167149/125000000000 : ℝ) (992057797903/1000000000000 : ℝ) (198411559581/200000000000 : ℝ) (992073567547/1000000000000 : ℝ) (992073567549/1000000000000 : ℝ) (992073567421/1000000000000 : ℝ) (15501149491/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 2 (992073567547/1000000000000 : ℝ) (992073567549/1000000000000 : ℝ) (992073567421/1000000000000 : ℝ) (15501149491/15625000000 : ℝ) (248018391871/250000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 3 (248018391871/250000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 4 (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 5 (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 6 (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33445/262144 : ℝ)) 7 (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33445/262144 : ℝ))) (17717882743/100000000000 : ℝ) (177178827437/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17717882743/100000000000 : ℝ) (177178827437/1000000000000 : ℝ) (117717882743/200000000000 : ℝ) (588589413719/1000000000000 : ℝ) (210463077183/500000000000 : ℝ) (52615769297/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 1 (117717882743/200000000000 : ℝ) (588589413719/1000000000000 : ℝ) (210463077183/500000000000 : ℝ) (52615769297/125000000000 : ℝ) (12618944601/25000000000 : ℝ) (31547361503/62500000000 : ℝ) (124436901283/250000000000 : ℝ) (497747605141/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 2 (12618944601/25000000000 : ℝ) (31547361503/62500000000 : ℝ) (124436901283/250000000000 : ℝ) (497747605141/1000000000000 : ℝ) (250626347293/500000000000 : ℝ) (100250538919/200000000000 : ℝ) (501240439487/1000000000000 : ℝ) (501240439497/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 3 (250626347293/500000000000 : ℝ) (100250538919/200000000000 : ℝ) (501240439487/1000000000000 : ℝ) (501240439497/1000000000000 : ℝ) (125311641759/250000000000 : ℝ) (250623283523/500000000000 : ℝ) (501246566999/1000000000000 : ℝ) (501246567009/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 4 (125311641759/250000000000 : ℝ) (250623283523/500000000000 : ℝ) (501246566999/1000000000000 : ℝ) (501246567009/1000000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 5 (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 6 (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33445/262144 : ℝ))) 7 (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33445/262144 : ℝ)) hmem 8 (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33445/262144 : ℝ))) hcmem 8 (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33445/262144 : ℝ)) (992073567483/1000000000000 : ℝ) (992073567487/1000000000000 : ℝ) (501246567017/1000000000000 : ℝ) (125311641757/250000000000 : ℝ) (396823528059/500000000000 : ℝ) (793647056139/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0817_exp_lower
  have heNumeric : (513725391827/250000000000 : ℝ)/4 ≤ Real.exp (-85256500920167/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725391827/250000000000 : ℝ)/4 ≤ Real.exp ((66889/524288 : ℝ)-(793647056139/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66889/524288 : ℝ) (33445/262144 : ℝ) (793647056139/1000000000000 : ℝ) (513725391827/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0818; no trusted numerical premise.
theorem cover8_leaf0818_exp_radius : (199601695713760993/200000000000000000 : ℝ) ≤ Real.exp ((-66891/4194304 : ℝ)/8) ∧ Real.exp ((-66891/4194304 : ℝ)/8) ≤ (499004239284402483/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66891/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0818_exp_lower : (184022689915802199/200000000000000000 : ℝ) ≤ Real.exp ((-42628250512331/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250512331/64000000000000 : ℝ)/8) ≤ (230028362394752749/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250512331/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0818_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901565631/1000000000000 : ℝ) ≤ 4*Real.exp (33445/262144 : ℝ)*Real.exp (-mu (radius 8 (66891/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901565631/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66891/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0818_exp_radius
  have hrNumeric : (123022304967/125000000000 : ℝ) ≤ Real.exp (-66891/4194304 : ℝ) ∧ Real.exp (-66891/4194304 : ℝ) ≤ (984178439737/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123022304967/125000000000 : ℝ) ≤ (radius 8 (66891/524288 : ℝ)) ∧ (radius 8 (66891/524288 : ℝ)) ≤ (984178439737/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66891/524288 : ℝ)) (123022304967/125000000000 : ℝ) (984178439737/1000000000000 : ℝ) (88590065409/500000000000 : ℝ) (7087205233/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66891/524288 : ℝ)) (123022304967/125000000000 : ℝ) (984178439737/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123022304967/125000000000 : ℝ) (984178439737/1000000000000 : ℝ) (248022304967/250000000000 : ℝ) (992089219869/1000000000000 : ℝ) (992057679641/1000000000000 : ℝ) (992057679643/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 1 (248022304967/250000000000 : ℝ) (992089219869/1000000000000 : ℝ) (992057679641/1000000000000 : ℝ) (992057679643/1000000000000 : ℝ) (496036724877/500000000000 : ℝ) (248018362439/250000000000 : ℝ) (992073449629/1000000000000 : ℝ) (992073449631/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 2 (496036724877/500000000000 : ℝ) (248018362439/250000000000 : ℝ) (992073449629/1000000000000 : ℝ) (992073449631/1000000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 3 (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 4 (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 5 (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 6 (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66891/524288 : ℝ)) 7 (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66891/524288 : ℝ))) (88590065409/500000000000 : ℝ) (7087205233/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88590065409/500000000000 : ℝ) (7087205233/40000000000 : ℝ) (588590065409/1000000000000 : ℝ) (588590065413/1000000000000 : ℝ) (210463851301/500000000000 : ℝ) (420927702611/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 1 (588590065409/1000000000000 : ℝ) (588590065413/1000000000000 : ℝ) (210463851301/500000000000 : ℝ) (420927702611/1000000000000 : ℝ) (100951776801/200000000000 : ℝ) (126189721003/250000000000 : ℝ) (497748796087/1000000000000 : ℝ) (99549759219/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 2 (100951776801/200000000000 : ℝ) (126189721003/250000000000 : ℝ) (497748796087/1000000000000 : ℝ) (99549759219/200000000000 : ℝ) (250626920023/500000000000 : ℝ) (250626920027/500000000000 : ℝ) (501241585293/1000000000000 : ℝ) (250620792651/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 3 (250626920023/500000000000 : ℝ) (250626920027/500000000000 : ℝ) (501241585293/1000000000000 : ℝ) (250620792651/500000000000 : ℝ) (501247712669/1000000000000 : ℝ) (250623856339/500000000000 : ℝ) (62655964079/125000000000 : ℝ) (501247712641/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 4 (501247712669/1000000000000 : ℝ) (250623856339/500000000000 : ℝ) (62655964079/125000000000 : ℝ) (501247712641/1000000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 5 (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 6 (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66891/524288 : ℝ))) 7 (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66891/524288 : ℝ)) hmem 8 (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66891/524288 : ℝ))) hcmem 8 (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66891/524288 : ℝ)) (992073449691/1000000000000 : ℝ) (496036724847/500000000000 : ℝ) (10024954253/20000000000 : ℝ) (25062385633/50000000000 : ℝ) (158729792857/200000000000 : ℝ) (49603060269/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0818_exp_lower
  have heNumeric : (2054901565631/1000000000000 : ℝ)/4 ≤ Real.exp (-42628250512331/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901565631/1000000000000 : ℝ)/4 ≤ Real.exp ((33445/262144 : ℝ)-(49603060269/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33445/262144 : ℝ) (66891/524288 : ℝ) (49603060269/62500000000 : ℝ) (2054901565631/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0819; no trusted numerical premise.
theorem cover8_leaf0819_exp_radius : (124751056103229373/125000000000000000 : ℝ) ≤ Real.exp ((-16723/1048576 : ℝ)/8) ∧ Real.exp ((-16723/1048576 : ℝ)/8) ≤ (199601689765166997/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16723/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0819_exp_lower : (57507090592942027/62500000000000000 : ℝ) ≤ Real.exp ((-85256501126981/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501126981/128000000000000 : ℝ)/8) ≤ (920113449487072433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501126981/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0819_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725390997/250000000000 : ℝ) ≤ 4*Real.exp (66891/524288 : ℝ)*Real.exp (-mu (radius 8 (16723/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725390997/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16723/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0819_exp_radius
  have hrNumeric : (98417820509/100000000000 : ℝ) ≤ Real.exp (-16723/1048576 : ℝ) ∧ Real.exp (-16723/1048576 : ℝ) ≤ (984178205091/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98417820509/100000000000 : ℝ) ≤ (radius 8 (16723/131072 : ℝ)) ∧ (radius 8 (16723/131072 : ℝ)) ≤ (984178205091/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16723/131072 : ℝ)) (98417820509/100000000000 : ℝ) (984178205091/1000000000000 : ℝ) (44295358549/250000000000 : ℝ) (88590717101/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16723/131072 : ℝ)) (98417820509/100000000000 : ℝ) (984178205091/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98417820509/100000000000 : ℝ) (984178205091/1000000000000 : ℝ) (198417820509/200000000000 : ℝ) (496044551273/500000000000 : ℝ) (992057561379/1000000000000 : ℝ) (49602878069/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 1 (198417820509/200000000000 : ℝ) (496044551273/500000000000 : ℝ) (992057561379/1000000000000 : ℝ) (49602878069/50000000000 : ℝ) (496036665981/500000000000 : ℝ) (992073331963/1000000000000 : ℝ) (248018332959/250000000000 : ℝ) (496036665919/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 2 (496036665981/500000000000 : ℝ) (992073331963/1000000000000 : ℝ) (248018332959/250000000000 : ℝ) (496036665919/500000000000 : ℝ) (992073331899/1000000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 3 (992073331899/1000000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 4 (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 5 (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 6 (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16723/131072 : ℝ)) 7 (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16723/131072 : ℝ))) (44295358549/250000000000 : ℝ) (88590717101/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44295358549/250000000000 : ℝ) (88590717101/500000000000 : ℝ) (294295358549/500000000000 : ℝ) (588590717101/1000000000000 : ℝ) (21046462541/50000000000 : ℝ) (105232312707/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 1 (294295358549/500000000000 : ℝ) (588590717101/1000000000000 : ℝ) (21046462541/50000000000 : ℝ) (105232312707/250000000000 : ℝ) (504759983959/1000000000000 : ℝ) (100951996793/200000000000 : ℝ) (497749987029/1000000000000 : ℝ) (124437496759/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 2 (504759983959/1000000000000 : ℝ) (100951996793/200000000000 : ℝ) (497749987029/1000000000000 : ℝ) (124437496759/250000000000 : ℝ) (250627492747/500000000000 : ℝ) (501254985501/1000000000000 : ℝ) (501242731087/1000000000000 : ℝ) (100248546219/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 3 (250627492747/500000000000 : ℝ) (501254985501/1000000000000 : ℝ) (501242731087/1000000000000 : ℝ) (100248546219/200000000000 : ℝ) (50124885829/100000000000 : ℝ) (250624429149/500000000000 : ℝ) (501248858253/1000000000000 : ℝ) (501248858261/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 4 (50124885829/100000000000 : ℝ) (250624429149/500000000000 : ℝ) (501248858253/1000000000000 : ℝ) (501248858261/1000000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 5 (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 6 (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16723/131072 : ℝ))) 7 (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16723/131072 : ℝ)) hmem 8 (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16723/131072 : ℝ))) hcmem 8 (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16723/131072 : ℝ)) (496036665949/500000000000 : ℝ) (992073331901/1000000000000 : ℝ) (501248858271/1000000000000 : ℝ) (12531221457/25000000000 : ℝ) (396825436217/500000000000 : ℝ) (198412718113/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0819_exp_lower
  have heNumeric : (513725390997/250000000000 : ℝ)/4 ≤ Real.exp (-85256501126981/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725390997/250000000000 : ℝ)/4 ≤ Real.exp ((66891/524288 : ℝ)-(198412718113/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66891/524288 : ℝ) (16723/131072 : ℝ) (198412718113/250000000000 : ℝ) (513725390997/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0820; no trusted numerical premise.
theorem cover8_leaf0820_exp_radius : (99800841908286589/100000000000000000 : ℝ) ≤ Real.exp ((-66893/4194304 : ℝ)/8) ∧ Real.exp ((-66893/4194304 : ℝ)/8) ≤ (998008419082865891/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66893/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0820_exp_lower : (23002836234912851/25000000000000000 : ℝ) ≤ Real.exp ((-21314125306941/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125306941/32000000000000 : ℝ)/8) ≤ (920113449396514041/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125306941/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0820_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490156237/100000000000 : ℝ) ≤ 4*Real.exp (16723/131072 : ℝ)*Real.exp (-mu (radius 8 (66893/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490156237/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66893/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0820_exp_radius
  have hrNumeric : (984177970443/1000000000000 : ℝ) ≤ Real.exp (-66893/4194304 : ℝ) ∧ Real.exp (-66893/4194304 : ℝ) ≤ (246044492611/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984177970443/1000000000000 : ℝ) ≤ (radius 8 (66893/524288 : ℝ)) ∧ (radius 8 (66893/524288 : ℝ)) ≤ (246044492611/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66893/524288 : ℝ)) (984177970443/1000000000000 : ℝ) (246044492611/250000000000 : ℝ) (177182737569/1000000000000 : ℝ) (22147842197/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66893/524288 : ℝ)) (984177970443/1000000000000 : ℝ) (246044492611/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984177970443/1000000000000 : ℝ) (246044492611/250000000000 : ℝ) (992088985221/1000000000000 : ℝ) (496044492611/500000000000 : ℝ) (248014360779/250000000000 : ℝ) (496028721559/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 1 (992088985221/1000000000000 : ℝ) (496044492611/500000000000 : ℝ) (248014360779/250000000000 : ℝ) (496028721559/500000000000 : ℝ) (124009151771/125000000000 : ℝ) (99207321417/100000000000 : ℝ) (992073214043/1000000000000 : ℝ) (198414642809/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 2 (124009151771/125000000000 : ℝ) (99207321417/100000000000 : ℝ) (992073214043/1000000000000 : ℝ) (198414642809/200000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 3 (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 4 (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 5 (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 6 (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66893/524288 : ℝ)) 7 (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66893/524288 : ℝ))) (177182737569/1000000000000 : ℝ) (22147842197/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177182737569/1000000000000 : ℝ) (22147842197/125000000000 : ℝ) (36786960549/62500000000 : ℝ) (147147842197/250000000000 : ℝ) (210465399513/500000000000 : ℝ) (84186159807/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 1 (36786960549/62500000000 : ℝ) (147147842197/250000000000 : ℝ) (210465399513/500000000000 : ℝ) (84186159807/200000000000 : ℝ) (100952216781/200000000000 : ℝ) (63095135489/125000000000 : ℝ) (497751177961/1000000000000 : ℝ) (497751177969/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 2 (100952216781/200000000000 : ℝ) (63095135489/125000000000 : ℝ) (497751177961/1000000000000 : ℝ) (497751177969/1000000000000 : ℝ) (501256130933/1000000000000 : ℝ) (501256130941/1000000000000 : ℝ) (62655484609/125000000000 : ℝ) (501243876881/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 3 (501256130933/1000000000000 : ℝ) (501256130941/1000000000000 : ℝ) (62655484609/125000000000 : ℝ) (501243876881/1000000000000 : ℝ) (250625001951/500000000000 : ℝ) (501250003911/1000000000000 : ℝ) (100250000773/200000000000 : ℝ) (250625001937/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 4 (250625001951/500000000000 : ℝ) (501250003911/1000000000000 : ℝ) (100250000773/200000000000 : ℝ) (250625001937/500000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 5 (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 6 (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66893/524288 : ℝ))) 7 (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66893/524288 : ℝ)) hmem 8 (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66893/524288 : ℝ))) hcmem 8 (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66893/524288 : ℝ)) (198414642821/200000000000 : ℝ) (248018303527/250000000000 : ℝ) (501250003883/1000000000000 : ℝ) (501250003893/1000000000000 : ℝ) (793652780569/1000000000000 : ℝ) (198413195147/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0820_exp_lower
  have heNumeric : (205490156237/100000000000 : ℝ)/4 ≤ Real.exp (-21314125306941/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490156237/100000000000 : ℝ)/4 ≤ Real.exp ((16723/131072 : ℝ)-(198413195147/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16723/131072 : ℝ) (66893/524288 : ℝ) (198413195147/250000000000 : ℝ) (205490156237/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0821; no trusted numerical premise.
theorem cover8_leaf0821_exp_radius : (499004194669948841/500000000000000000 : ℝ) ≤ Real.exp ((-33447/2097152 : ℝ)/8) ∧ Real.exp ((-33447/2097152 : ℝ)/8) ≤ (998008389339897683/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33447/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0821_exp_lower : (28753545290904563/31250000000000000 : ℝ) ≤ Real.exp ((-85256501325219/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501325219/128000000000000 : ℝ)/8) ≤ (920113449308946017/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501325219/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0821_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980312161/200000000000 : ℝ) ≤ 4*Real.exp (66893/524288 : ℝ)*Real.exp (-mu (radius 8 (33447/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980312161/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33447/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0821_exp_radius
  have hrNumeric : (984177735797/1000000000000 : ℝ) ≤ Real.exp (-33447/2097152 : ℝ) ∧ Real.exp (-33447/2097152 : ℝ) ≤ (492088867899/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984177735797/1000000000000 : ℝ) ≤ (radius 8 (33447/262144 : ℝ)) ∧ (radius 8 (33447/262144 : ℝ)) ≤ (492088867899/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33447/262144 : ℝ)) (984177735797/1000000000000 : ℝ) (492088867899/500000000000 : ℝ) (177184040927/1000000000000 : ℝ) (88592020467/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33447/262144 : ℝ)) (984177735797/1000000000000 : ℝ) (492088867899/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984177735797/1000000000000 : ℝ) (492088867899/500000000000 : ℝ) (496044433949/500000000000 : ℝ) (992088867899/1000000000000 : ℝ) (496028662427/500000000000 : ℝ) (198411464971/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 1 (496044433949/500000000000 : ℝ) (992088867899/1000000000000 : ℝ) (496028662427/500000000000 : ℝ) (198411464971/200000000000 : ℝ) (124009137047/125000000000 : ℝ) (992073096377/1000000000000 : ℝ) (793658477/800000000 : ℝ) (248018274063/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 2 (124009137047/125000000000 : ℝ) (992073096377/1000000000000 : ℝ) (793658477/800000000 : ℝ) (248018274063/250000000000 : ℝ) (992073096313/1000000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 3 (992073096313/1000000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 4 (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 5 (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 6 (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33447/262144 : ℝ)) 7 (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33447/262144 : ℝ))) (177184040927/1000000000000 : ℝ) (88592020467/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177184040927/1000000000000 : ℝ) (88592020467/500000000000 : ℝ) (588592020463/1000000000000 : ℝ) (588592020467/1000000000000 : ℝ) (420932347209/1000000000000 : ℝ) (210466173609/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 1 (588592020463/1000000000000 : ℝ) (588592020467/1000000000000 : ℝ) (420932347209/1000000000000 : ℝ) (210466173609/500000000000 : ℝ) (126190545959/250000000000 : ℝ) (504762183843/1000000000000 : ℝ) (124438092219/250000000000 : ℝ) (124438092221/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 2 (126190545959/250000000000 : ℝ) (504762183843/1000000000000 : ℝ) (124438092219/250000000000 : ℝ) (124438092221/250000000000 : ℝ) (125314319089/250000000000 : ℝ) (125314319091/250000000000 : ℝ) (250622511321/500000000000 : ℝ) (10024900453/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 3 (125314319089/250000000000 : ℝ) (125314319091/250000000000 : ℝ) (250622511321/500000000000 : ℝ) (10024900453/20000000000 : ℝ) (501251149499/1000000000000 : ℝ) (501251149507/1000000000000 : ℝ) (501251149461/1000000000000 : ℝ) (50125114947/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 4 (501251149499/1000000000000 : ℝ) (501251149507/1000000000000 : ℝ) (501251149461/1000000000000 : ℝ) (50125114947/100000000000 : ℝ) (12531278737/25000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 5 (12531278737/25000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 6 (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33447/262144 : ℝ))) 7 (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33447/262144 : ℝ)) hmem 8 (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33447/262144 : ℝ))) hcmem 8 (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33447/262144 : ℝ)) (124009137039/125000000000 : ℝ) (198414619263/200000000000 : ℝ) (501251149479/1000000000000 : ℝ) (501251149489/1000000000000 : ℝ) (793654688679/1000000000000 : ℝ) (396827344349/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0821_exp_lower
  have heNumeric : (410980312161/200000000000 : ℝ)/4 ≤ Real.exp (-85256501325219/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980312161/200000000000 : ℝ)/4 ≤ Real.exp ((66893/524288 : ℝ)-(396827344349/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66893/524288 : ℝ) (33447/262144 : ℝ) (396827344349/500000000000 : ℝ) (410980312161/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0822; no trusted numerical premise.
theorem cover8_leaf0822_exp_radius : (24950208989923259/25000000000000000 : ℝ) ≤ Real.exp ((-66895/4194304 : ℝ)/8) ∧ Real.exp ((-66895/4194304 : ℝ)/8) ≤ (998008359596930361/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66895/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0822_exp_lower : (230028362305919569/250000000000000000 : ℝ) ≤ Real.exp ((-42628250710057/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250710057/64000000000000 : ℝ)/8) ≤ (920113449223678277/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250710057/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0822_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450779641/500000000000 : ℝ) ≤ 4*Real.exp (33447/262144 : ℝ)*Real.exp (-mu (radius 8 (66895/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450779641/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66895/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0822_exp_radius
  have hrNumeric : (984177501151/1000000000000 : ℝ) ≤ Real.exp (-66895/4194304 : ℝ) ∧ Real.exp (-66895/4194304 : ℝ) ≤ (30755546911/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984177501151/1000000000000 : ℝ) ≤ (radius 8 (66895/524288 : ℝ)) ∧ (radius 8 (66895/524288 : ℝ)) ≤ (30755546911/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66895/524288 : ℝ)) (984177501151/1000000000000 : ℝ) (30755546911/31250000000 : ℝ) (44296336069/250000000000 : ℝ) (88592672141/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66895/524288 : ℝ)) (984177501151/1000000000000 : ℝ) (30755546911/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984177501151/1000000000000 : ℝ) (30755546911/31250000000 : ℝ) (39683550023/40000000000 : ℝ) (62005546911/62500000000 : ℝ) (992057206591/1000000000000 : ℝ) (992057206593/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 1 (39683550023/40000000000 : ℝ) (62005546911/62500000000 : ℝ) (992057206591/1000000000000 : ℝ) (992057206593/1000000000000 : ℝ) (992072978583/1000000000000 : ℝ) (198414595717/200000000000 : ℝ) (992072978457/1000000000000 : ℝ) (49603648923/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 2 (992072978583/1000000000000 : ℝ) (198414595717/200000000000 : ℝ) (992072978457/1000000000000 : ℝ) (49603648923/50000000000 : ℝ) (24801824463/25000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 3 (24801824463/25000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 4 (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 5 (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 6 (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66895/524288 : ℝ)) 7 (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66895/524288 : ℝ))) (44296336069/250000000000 : ℝ) (88592672141/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44296336069/250000000000 : ℝ) (88592672141/500000000000 : ℝ) (294296336069/500000000000 : ℝ) (588592672141/1000000000000 : ℝ) (3367471163/8000000000 : ℝ) (420933895383/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 1 (294296336069/500000000000 : ℝ) (588592672141/1000000000000 : ℝ) (3367471163/8000000000 : ℝ) (420933895383/1000000000000 : ℝ) (126190820939/250000000000 : ℝ) (252381641881/500000000000 : ℝ) (248876779889/500000000000 : ℝ) (99550711957/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 2 (126190820939/250000000000 : ℝ) (252381641881/500000000000 : ℝ) (248876779889/500000000000 : ℝ) (99550711957/200000000000 : ℝ) (501258421767/1000000000000 : ℝ) (250629210887/500000000000 : ℝ) (501246168399/1000000000000 : ℝ) (250623084203/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 3 (501258421767/1000000000000 : ℝ) (250629210887/500000000000 : ℝ) (501246168399/1000000000000 : ℝ) (250623084203/500000000000 : ℝ) (501252295083/1000000000000 : ℝ) (50125229509/100000000000 : ℝ) (100250459009/200000000000 : ℝ) (501252295053/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 4 (501252295083/1000000000000 : ℝ) (50125229509/100000000000 : ℝ) (100250459009/200000000000 : ℝ) (501252295053/1000000000000 : ℝ) (62656536883/125000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 5 (62656536883/125000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 6 (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66895/524288 : ℝ))) 7 (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66895/524288 : ℝ)) hmem 8 (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66895/524288 : ℝ))) hcmem 8 (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66895/524288 : ℝ)) (992072978519/1000000000000 : ℝ) (992072978523/1000000000000 : ℝ) (501252295063/1000000000000 : ℝ) (15664134221/31250000000 : ℝ) (79365659677/100000000000 : ℝ) (198414149197/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0822_exp_lower
  have heNumeric : (1027450779641/500000000000 : ℝ)/4 ≤ Real.exp (-42628250710057/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450779641/500000000000 : ℝ)/4 ≤ Real.exp ((33447/262144 : ℝ)-(198414149197/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33447/262144 : ℝ) (66895/524288 : ℝ) (198414149197/250000000000 : ℝ) (1027450779641/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0823; no trusted numerical premise.
theorem cover8_leaf0823_exp_radius : (39920333194158557/40000000000000000 : ℝ) ≤ Real.exp ((-4181/262144 : ℝ)/8) ∧ Real.exp ((-4181/262144 : ℝ)/8) ≤ (499004164926981963/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4181/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0823_exp_lower : (28753545285607677/31250000000000000 : ℝ) ≤ Real.exp ((-85256501513857/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501513857/128000000000000 : ℝ)/8) ≤ (184022689827889133/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501513857/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0823_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901557777/1000000000000 : ℝ) ≤ 4*Real.exp (66895/524288 : ℝ)*Real.exp (-mu (radius 8 (4181/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901557777/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4181/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0823_exp_radius
  have hrNumeric : (123022158313/125000000000 : ℝ) ≤ Real.exp (-4181/262144 : ℝ) ∧ Real.exp (-4181/262144 : ℝ) ≤ (196835453301/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123022158313/125000000000 : ℝ) ≤ (radius 8 (4181/32768 : ℝ)) ∧ (radius 8 (4181/32768 : ℝ)) ≤ (196835453301/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4181/32768 : ℝ)) (123022158313/125000000000 : ℝ) (196835453301/200000000000 : ℝ) (177186647619/1000000000000 : ℝ) (88593323813/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4181/32768 : ℝ)) (123022158313/125000000000 : ℝ) (196835453301/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123022158313/125000000000 : ℝ) (196835453301/200000000000 : ℝ) (248022158313/250000000000 : ℝ) (992088633253/1000000000000 : ℝ) (992057088329/1000000000000 : ℝ) (99205708833/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 1 (248022158313/250000000000 : ℝ) (992088633253/1000000000000 : ℝ) (992057088329/1000000000000 : ℝ) (99205708833/100000000000 : ℝ) (99207286079/100000000000 : ℝ) (124009107599/125000000000 : ℝ) (198414572133/200000000000 : ℝ) (992072860667/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 2 (99207286079/100000000000 : ℝ) (124009107599/125000000000 : ℝ) (198414572133/200000000000 : ℝ) (992072860667/1000000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 3 (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 4 (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 5 (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 6 (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4181/32768 : ℝ)) 7 (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4181/32768 : ℝ))) (177186647619/1000000000000 : ℝ) (88593323813/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177186647619/1000000000000 : ℝ) (88593323813/500000000000 : ℝ) (588593323809/1000000000000 : ℝ) (588593323813/1000000000000 : ℝ) (420935443529/1000000000000 : ℝ) (210467721769/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 1 (588593323809/1000000000000 : ℝ) (588593323813/1000000000000 : ℝ) (420935443529/1000000000000 : ℝ) (210467721769/500000000000 : ℝ) (504764383669/1000000000000 : ℝ) (126191095919/250000000000 : ℝ) (497754750671/1000000000000 : ℝ) (497754750679/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 2 (504764383669/1000000000000 : ℝ) (126191095919/250000000000 : ℝ) (497754750671/1000000000000 : ℝ) (497754750679/1000000000000 : ℝ) (50125956717/100000000000 : ℝ) (250629783589/500000000000 : ℝ) (125311828537/250000000000 : ℝ) (125311828539/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 3 (50125956717/100000000000 : ℝ) (250629783589/500000000000 : ℝ) (125311828537/250000000000 : ℝ) (125311828539/250000000000 : ℝ) (501253440659/1000000000000 : ℝ) (501253440667/1000000000000 : ℝ) (501253440621/1000000000000 : ℝ) (50125344063/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 4 (501253440659/1000000000000 : ℝ) (501253440667/1000000000000 : ℝ) (501253440621/1000000000000 : ℝ) (50125344063/100000000000 : ℝ) (783208501/1562500000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 5 (783208501/1562500000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 6 (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4181/32768 : ℝ))) 7 (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4181/32768 : ℝ)) hmem 8 (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4181/32768 : ℝ))) hcmem 8 (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4181/32768 : ℝ)) (992072860727/1000000000000 : ℝ) (99207286073/100000000000 : ℝ) (501253440639/1000000000000 : ℝ) (501253440649/1000000000000 : ℝ) (793658504849/1000000000000 : ℝ) (793658504869/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0823_exp_lower
  have heNumeric : (2054901557777/1000000000000 : ℝ)/4 ≤ Real.exp (-85256501513857/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901557777/1000000000000 : ℝ)/4 ≤ Real.exp ((66895/524288 : ℝ)-(793658504869/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66895/524288 : ℝ) (4181/32768 : ℝ) (793658504869/1000000000000 : ℝ) (2054901557777/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0824; no trusted numerical premise.
theorem cover8_leaf0824_exp_radius : (998008300110998377/1000000000000000000 : ℝ) ≤ Real.exp ((-66897/4194304 : ℝ)/8) ∧ Real.exp ((-66897/4194304 : ℝ)/8) ≤ (499004150055499189/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66897/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0824_exp_lower : (920113449058548463/1000000000000000000 : ℝ) ≤ Real.exp ((-5328531350243/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328531350243/8000000000000 : ℝ)/8) ≤ (57507090566159279/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328531350243/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0824_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725389083/250000000000 : ℝ) ≤ 4*Real.exp (4181/32768 : ℝ)*Real.exp (-mu (radius 8 (66897/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725389083/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66897/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0824_exp_radius
  have hrNumeric : (492088515929/500000000000 : ℝ) ≤ Real.exp (-66897/4194304 : ℝ) ∧ Real.exp (-66897/4194304 : ℝ) ≤ (984177031859/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492088515929/500000000000 : ℝ) ≤ (radius 8 (66897/524288 : ℝ)) ∧ (radius 8 (66897/524288 : ℝ)) ≤ (984177031859/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66897/524288 : ℝ)) (492088515929/500000000000 : ℝ) (984177031859/1000000000000 : ℝ) (44296987737/250000000000 : ℝ) (88593975477/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66897/524288 : ℝ)) (492088515929/500000000000 : ℝ) (984177031859/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492088515929/500000000000 : ℝ) (984177031859/1000000000000 : ℝ) (992088515929/1000000000000 : ℝ) (99208851593/100000000000 : ℝ) (496028485033/500000000000 : ℝ) (248014242517/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 1 (992088515929/1000000000000 : ℝ) (99208851593/100000000000 : ℝ) (496028485033/500000000000 : ℝ) (248014242517/250000000000 : ℝ) (992072742997/1000000000000 : ℝ) (992072742999/1000000000000 : ℝ) (124009092859/125000000000 : ℝ) (496036371437/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 2 (992072742997/1000000000000 : ℝ) (992072742999/1000000000000 : ℝ) (124009092859/125000000000 : ℝ) (496036371437/500000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 3 (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 4 (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 5 (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 6 (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66897/524288 : ℝ)) 7 (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66897/524288 : ℝ))) (44296987737/250000000000 : ℝ) (88593975477/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44296987737/250000000000 : ℝ) (88593975477/500000000000 : ℝ) (294296987737/500000000000 : ℝ) (588593975477/1000000000000 : ℝ) (21046849583/50000000000 : ℝ) (105234247917/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 1 (294296987737/500000000000 : ℝ) (588593975477/1000000000000 : ℝ) (21046849583/50000000000 : ℝ) (105234247917/250000000000 : ℝ) (504765483567/1000000000000 : ℝ) (504765483573/1000000000000 : ℝ) (248877970773/500000000000 : ℝ) (497755941553/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 2 (504765483567/1000000000000 : ℝ) (504765483573/1000000000000 : ℝ) (248877970773/500000000000 : ℝ) (497755941553/1000000000000 : ℝ) (125315178139/250000000000 : ℝ) (501260712563/1000000000000 : ℝ) (12531211497/25000000000 : ℝ) (31328028743/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 3 (125315178139/250000000000 : ℝ) (501260712563/1000000000000 : ℝ) (12531211497/25000000000 : ℝ) (31328028743/62500000000 : ℝ) (250627293109/500000000000 : ℝ) (250627293113/500000000000 : ℝ) (25062729309/50000000000 : ℝ) (501254586189/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 4 (250627293109/500000000000 : ℝ) (250627293113/500000000000 : ℝ) (25062729309/50000000000 : ℝ) (501254586189/1000000000000 : ℝ) (501254586199/1000000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 5 (501254586199/1000000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 6 (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66897/524288 : ℝ))) 7 (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66897/524288 : ℝ)) hmem 8 (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66897/524288 : ℝ))) hcmem 8 (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66897/524288 : ℝ)) (496036371467/500000000000 : ℝ) (992072742937/1000000000000 : ℝ) (250627293099/500000000000 : ℝ) (15664205819/31250000000 : ℝ) (396830206451/500000000000 : ℝ) (793660412921/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0824_exp_lower
  have heNumeric : (513725389083/250000000000 : ℝ)/4 ≤ Real.exp (-5328531350243/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725389083/250000000000 : ℝ)/4 ≤ Real.exp ((4181/32768 : ℝ)-(793660412921/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4181/32768 : ℝ) (66897/524288 : ℝ) (793660412921/1000000000000 : ℝ) (513725389083/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0800_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0800_certificate
#check SmaleRate.Proofs.cover8_leaf0801_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0801_certificate
#check SmaleRate.Proofs.cover8_leaf0802_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0802_certificate
#check SmaleRate.Proofs.cover8_leaf0803_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0803_certificate
#check SmaleRate.Proofs.cover8_leaf0804_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0804_certificate
#check SmaleRate.Proofs.cover8_leaf0805_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0805_certificate
#check SmaleRate.Proofs.cover8_leaf0806_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0806_certificate
#check SmaleRate.Proofs.cover8_leaf0807_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0807_certificate
#check SmaleRate.Proofs.cover8_leaf0808_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0808_certificate
#check SmaleRate.Proofs.cover8_leaf0809_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0809_certificate
#check SmaleRate.Proofs.cover8_leaf0810_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0810_certificate
#check SmaleRate.Proofs.cover8_leaf0811_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0811_certificate
#check SmaleRate.Proofs.cover8_leaf0812_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0812_certificate
#check SmaleRate.Proofs.cover8_leaf0813_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0813_certificate
#check SmaleRate.Proofs.cover8_leaf0814_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0814_certificate
#check SmaleRate.Proofs.cover8_leaf0815_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0815_certificate
#check SmaleRate.Proofs.cover8_leaf0816_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0816_certificate
#check SmaleRate.Proofs.cover8_leaf0817_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0817_certificate
#check SmaleRate.Proofs.cover8_leaf0818_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0818_certificate
#check SmaleRate.Proofs.cover8_leaf0819_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0819_certificate
#check SmaleRate.Proofs.cover8_leaf0820_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0820_certificate
#check SmaleRate.Proofs.cover8_leaf0821_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0821_certificate
#check SmaleRate.Proofs.cover8_leaf0822_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0822_certificate
#check SmaleRate.Proofs.cover8_leaf0823_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0823_certificate
#check SmaleRate.Proofs.cover8_leaf0824_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0824_certificate
