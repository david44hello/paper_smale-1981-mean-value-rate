/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1125; no trusted numerical premise.
theorem cover8_leaf1125_exp_radius : (99799934751865629/100000000000000000 : ℝ) ≤ Real.exp ((-33599/2097152 : ℝ)/8) ∧ Real.exp ((-33599/2097152 : ℝ)/8) ≤ (997999347518656291/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33599/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1125_exp_lower : (460056762761109669/500000000000000000 : ℝ) ≤ Real.exp ((-17051283301399/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051283301399/25600000000000 : ℝ)/8) ≤ (920113525522219339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051283301399/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1125_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902922471/1000000000000 : ℝ) ≤ 4*Real.exp (67197/524288 : ℝ)*Real.exp (-mu (radius 8 (33599/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902922471/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33599/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1125_exp_radius
  have hrNumeric : (6150665037/6250000000 : ℝ) ≤ Real.exp (-33599/2097152 : ℝ) ∧ Real.exp (-33599/2097152 : ℝ) ≤ (984106405921/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (6150665037/6250000000 : ℝ) ≤ (radius 8 (33599/262144 : ℝ)) ∧ (radius 8 (33599/262144 : ℝ)) ≤ (984106405921/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33599/262144 : ℝ)) (6150665037/6250000000 : ℝ) (984106405921/1000000000000 : ℝ) (22197473753/125000000000 : ℝ) (177579790031/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33599/262144 : ℝ)) (6150665037/6250000000 : ℝ) (984106405921/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (6150665037/6250000000 : ℝ) (984106405921/1000000000000 : ℝ) (12400665037/12500000000 : ℝ) (992053202961/1000000000000 : ℝ) (992021373721/1000000000000 : ℝ) (496010686861/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 1 (12400665037/12500000000 : ℝ) (992053202961/1000000000000 : ℝ) (992021373721/1000000000000 : ℝ) (496010686861/500000000000 : ℝ) (49601864417/50000000000 : ℝ) (496018644171/500000000000 : ℝ) (248009322053/250000000000 : ℝ) (496018644107/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 2 (49601864417/50000000000 : ℝ) (496018644171/500000000000 : ℝ) (248009322053/250000000000 : ℝ) (496018644107/500000000000 : ℝ) (248009322069/250000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 3 (248009322069/250000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 4 (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 5 (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 6 (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33599/262144 : ℝ)) 7 (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33599/262144 : ℝ))) (22197473753/125000000000 : ℝ) (177579790031/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22197473753/125000000000 : ℝ) (177579790031/1000000000000 : ℝ) (147197473753/250000000000 : ℝ) (73598736877/125000000000 : ℝ) (105350542839/250000000000 : ℝ) (84280434273/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 1 (147197473753/250000000000 : ℝ) (73598736877/125000000000 : ℝ) (105350542839/250000000000 : ℝ) (84280434273/200000000000 : ℝ) (15784251037/31250000000 : ℝ) (505096033191/1000000000000 : ℝ) (498113782413/1000000000000 : ℝ) (498113782421/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 2 (15784251037/31250000000 : ℝ) (505096033191/1000000000000 : ℝ) (498113782413/1000000000000 : ℝ) (498113782421/1000000000000 : ℝ) (250802453899/500000000000 : ℝ) (250802453903/500000000000 : ℝ) (50159275869/100000000000 : ℝ) (501592758699/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 3 (250802453899/500000000000 : ℝ) (250802453903/500000000000 : ℝ) (50159275869/100000000000 : ℝ) (501592758699/1000000000000 : ℝ) (125399708311/250000000000 : ℝ) (501598833253/1000000000000 : ℝ) (501598833207/1000000000000 : ℝ) (7837481769/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 4 (125399708311/250000000000 : ℝ) (501598833253/1000000000000 : ℝ) (501598833207/1000000000000 : ℝ) (7837481769/15625000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 5 (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 6 (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33599/262144 : ℝ))) 7 (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33599/262144 : ℝ)) hmem 8 (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33599/262144 : ℝ))) hcmem 8 (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33599/262144 : ℝ)) (39681491531/40000000000 : ℝ) (496018644139/500000000000 : ℝ) (20063953329/40000000000 : ℝ) (100319766647/200000000000 : ℝ) (794233860021/1000000000000 : ℝ) (19855846501/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1125_exp_lower
  have heNumeric : (2054902922471/1000000000000 : ℝ)/4 ≤ Real.exp (-17051283301399/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902922471/1000000000000 : ℝ)/4 ≤ Real.exp ((67197/524288 : ℝ)-(19855846501/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67197/524288 : ℝ) (33599/262144 : ℝ) (19855846501/25000000000 : ℝ) (2054902922471/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1126; no trusted numerical premise.
theorem cover8_leaf1126_exp_radius : (249499829443989609/250000000000000000 : ℝ) ≤ Real.exp ((-67199/4194304 : ℝ)/8) ∧ Real.exp ((-67199/4194304 : ℝ)/8) ≤ (997999317775958437/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67199/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1126_exp_lower : (460056763054892303/500000000000000000 : ℝ) ≤ Real.exp ((-8525641585309/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525641585309/12800000000000 : ℝ)/8) ≤ (920113526109784607/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525641585309/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1126_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862866621/125000000000 : ℝ) ≤ 4*Real.exp (33599/262144 : ℝ)*Real.exp (-mu (radius 8 (67199/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862866621/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67199/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1126_exp_radius
  have hrNumeric : (98410617129/100000000000 : ℝ) ≤ Real.exp (-67199/4194304 : ℝ) ∧ Real.exp (-67199/4194304 : ℝ) ≤ (984106171291/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98410617129/100000000000 : ℝ) ≤ (radius 8 (67199/524288 : ℝ)) ∧ (radius 8 (67199/524288 : ℝ)) ≤ (984106171291/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67199/524288 : ℝ)) (98410617129/100000000000 : ℝ) (984106171291/1000000000000 : ℝ) (35516218057/200000000000 : ℝ) (177581090291/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67199/524288 : ℝ)) (98410617129/100000000000 : ℝ) (984106171291/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98410617129/100000000000 : ℝ) (984106171291/1000000000000 : ℝ) (198410617129/200000000000 : ℝ) (496026542823/500000000000 : ℝ) (496010627731/500000000000 : ℝ) (124002656933/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 1 (198410617129/200000000000 : ℝ) (496026542823/500000000000 : ℝ) (496010627731/500000000000 : ℝ) (124002656933/125000000000 : ℝ) (992037170553/1000000000000 : ℝ) (198407434111/200000000000 : ℝ) (39681486817/40000000000 : ℝ) (248009292607/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 2 (992037170553/1000000000000 : ℝ) (198407434111/200000000000 : ℝ) (39681486817/40000000000 : ℝ) (248009292607/250000000000 : ℝ) (992037170489/1000000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 3 (992037170489/1000000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 4 (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 5 (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 6 (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67199/524288 : ℝ)) 7 (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67199/524288 : ℝ))) (35516218057/200000000000 : ℝ) (177581090291/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35516218057/200000000000 : ℝ) (177581090291/1000000000000 : ℝ) (294395272571/500000000000 : ℝ) (294395272573/500000000000 : ℝ) (105350928533/250000000000 : ℝ) (421403714141/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 1 (294395272571/500000000000 : ℝ) (294395272573/500000000000 : ℝ) (105350928533/250000000000 : ℝ) (421403714141/1000000000000 : ℝ) (505097129637/1000000000000 : ℝ) (126274282411/250000000000 : ℝ) (498114969227/1000000000000 : ℝ) (99622993847/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 2 (505097129637/1000000000000 : ℝ) (126274282411/250000000000 : ℝ) (498114969227/1000000000000 : ℝ) (99622993847/200000000000 : ℝ) (62700756179/125000000000 : ℝ) (3135037809/6250000000 : ℝ) (250796950333/500000000000 : ℝ) (250796950337/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 3 (62700756179/125000000000 : ℝ) (3135037809/6250000000 : ℝ) (250796950333/500000000000 : ℝ) (250796950337/500000000000 : ℝ) (501599975049/1000000000000 : ℝ) (501599975057/1000000000000 : ℝ) (125399993753/250000000000 : ℝ) (501599975021/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 4 (501599975049/1000000000000 : ℝ) (501599975057/1000000000000 : ℝ) (125399993753/250000000000 : ℝ) (501599975021/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 5 (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 6 (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67199/524288 : ℝ))) 7 (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67199/524288 : ℝ)) hmem 8 (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67199/524288 : ℝ))) hcmem 8 (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67199/524288 : ℝ)) (124004646311/125000000000 : ℝ) (248009292623/250000000000 : ℝ) (50159997503/100000000000 : ℝ) (501599975039/1000000000000 : ℝ) (794235762261/1000000000000 : ℝ) (19855894057/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1126_exp_lower
  have heNumeric : (256862866621/125000000000 : ℝ)/4 ≤ Real.exp (-8525641585309/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862866621/125000000000 : ℝ)/4 ≤ Real.exp ((33599/262144 : ℝ)-(19855894057/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33599/262144 : ℝ) (67199/524288 : ℝ) (19855894057/25000000000 : ℝ) (256862866621/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1127; no trusted numerical premise.
theorem cover8_leaf1127_exp_radius : (249499822008315367/250000000000000000 : ℝ) ≤ Real.exp ((-525/32768 : ℝ)/8) ∧ Real.exp ((-525/32768 : ℝ)/8) ≤ (997999288033261469/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-525/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1127_exp_lower : (920113526700455259/1000000000000000000 : ℝ) ≤ Real.exp ((-85256415195729/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256415195729/128000000000000 : ℝ)/8) ≤ (46005676335022763/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256415195729/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1127_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451471761/500000000000 : ℝ) ≤ 4*Real.exp (67199/524288 : ℝ)*Real.exp (-mu (radius 8 (525/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451471761/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (525/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1127_exp_radius
  have hrNumeric : (984105936661/1000000000000 : ℝ) ≤ Real.exp (-525/32768 : ℝ) ∧ Real.exp (-525/32768 : ℝ) ≤ (492052968331/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984105936661/1000000000000 : ℝ) ≤ (radius 8 (525/4096 : ℝ)) ∧ (radius 8 (525/4096 : ℝ)) ≤ (492052968331/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (525/4096 : ℝ)) (984105936661/1000000000000 : ℝ) (492052968331/500000000000 : ℝ) (17758239053/100000000000 : ℝ) (177582390537/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (525/4096 : ℝ)) (984105936661/1000000000000 : ℝ) (492052968331/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (525/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984105936661/1000000000000 : ℝ) (492052968331/500000000000 : ℝ) (99205296833/100000000000 : ℝ) (992052968331/1000000000000 : ℝ) (248005284301/250000000000 : ℝ) (496010568603/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (525/4096 : ℝ)) 1 (99205296833/100000000000 : ℝ) (992052968331/1000000000000 : ℝ) (248005284301/250000000000 : ℝ) (496010568603/500000000000 : ℝ) (992037052767/1000000000000 : ℝ) (992037052769/1000000000000 : ℝ) (992037052639/1000000000000 : ℝ) (992037052641/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (525/4096 : ℝ)) 2 (992037052767/1000000000000 : ℝ) (992037052769/1000000000000 : ℝ) (992037052639/1000000000000 : ℝ) (992037052641/1000000000000 : ℝ) (992037052703/1000000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (525/4096 : ℝ)) 3 (992037052703/1000000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (525/4096 : ℝ)) 4 (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (525/4096 : ℝ)) 5 (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (525/4096 : ℝ)) 6 (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (525/4096 : ℝ)) 7 (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (525/4096 : ℝ))) (17758239053/100000000000 : ℝ) (177582390537/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17758239053/100000000000 : ℝ) (177582390537/1000000000000 : ℝ) (117758239053/200000000000 : ℝ) (588791195269/1000000000000 : ℝ) (105351314221/250000000000 : ℝ) (421405256893/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 1 (117758239053/200000000000 : ℝ) (588791195269/1000000000000 : ℝ) (105351314221/250000000000 : ℝ) (421405256893/1000000000000 : ℝ) (252549113037/500000000000 : ℝ) (505098226081/1000000000000 : ℝ) (498116156023/1000000000000 : ℝ) (498116156031/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 2 (252549113037/500000000000 : ℝ) (505098226081/1000000000000 : ℝ) (498116156023/1000000000000 : ℝ) (498116156031/1000000000000 : ℝ) (62700898881/125000000000 : ℝ) (31350449441/62500000000 : ℝ) (4012760341/8000000000 : ℝ) (501595042633/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 3 (62700898881/125000000000 : ℝ) (31350449441/62500000000 : ℝ) (4012760341/8000000000 : ℝ) (501595042633/1000000000000 : ℝ) (125400279209/250000000000 : ℝ) (100320223369/200000000000 : ℝ) (501601116799/1000000000000 : ℝ) (62700139601/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 4 (125400279209/250000000000 : ℝ) (100320223369/200000000000 : ℝ) (501601116799/1000000000000 : ℝ) (62700139601/125000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 5 (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 6 (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (525/4096 : ℝ))) 7 (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (525/4096 : ℝ)) hmem 8 (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (525/4096 : ℝ))) hcmem 8 (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (525/4096 : ℝ)) (496018526351/500000000000 : ℝ) (198407410541/200000000000 : ℝ) (501601116817/1000000000000 : ℝ) (501601116827/1000000000000 : ℝ) (397118832237/500000000000 : ℝ) (794237664493/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1127_exp_lower
  have heNumeric : (1027451471761/500000000000 : ℝ)/4 ≤ Real.exp (-85256415195729/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451471761/500000000000 : ℝ)/4 ≤ Real.exp ((67199/524288 : ℝ)-(794237664493/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67199/524288 : ℝ) (525/4096 : ℝ) (794237664493/1000000000000 : ℝ) (1027451471761/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1128; no trusted numerical premise.
theorem cover8_leaf1128_exp_radius : (997999258290565387/1000000000000000000 : ℝ) ≤ Real.exp ((-67201/4194304 : ℝ)/8) ∧ Real.exp ((-67201/4194304 : ℝ)/8) ≤ (249499814572641347/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67201/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1128_exp_lower : (920113527293196167/1000000000000000000 : ℝ) ≤ Real.exp ((-666065738563/1000000000000 : ℝ)/8) ∧ Real.exp ((-666065738563/1000000000000 : ℝ)/8) ≤ (115014190911649521/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666065738563/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1128_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16053929329/7812500000 : ℝ) ≤ 4*Real.exp (525/4096 : ℝ)*Real.exp (-mu (radius 8 (67201/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (16053929329/7812500000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67201/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1128_exp_radius
  have hrNumeric : (61506606377/62500000000 : ℝ) ≤ Real.exp (-67201/4194304 : ℝ) ∧ Real.exp (-67201/4194304 : ℝ) ≤ (984105702033/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61506606377/62500000000 : ℝ) ≤ (radius 8 (67201/524288 : ℝ)) ∧ (radius 8 (67201/524288 : ℝ)) ≤ (984105702033/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67201/524288 : ℝ)) (61506606377/62500000000 : ℝ) (984105702033/1000000000000 : ℝ) (88791845383/500000000000 : ℝ) (44395922693/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67201/524288 : ℝ)) (61506606377/62500000000 : ℝ) (984105702033/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61506606377/62500000000 : ℝ) (984105702033/1000000000000 : ℝ) (124006606377/125000000000 : ℝ) (992052851017/1000000000000 : ℝ) (496010509473/500000000000 : ℝ) (248005254737/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 1 (124006606377/125000000000 : ℝ) (992052851017/1000000000000 : ℝ) (496010509473/500000000000 : ℝ) (248005254737/250000000000 : ℝ) (992036934981/1000000000000 : ℝ) (992036934983/1000000000000 : ℝ) (992036934853/1000000000000 : ℝ) (198407386971/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 2 (992036934981/1000000000000 : ℝ) (992036934983/1000000000000 : ℝ) (992036934853/1000000000000 : ℝ) (198407386971/200000000000 : ℝ) (992036934917/1000000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 3 (992036934917/1000000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 4 (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 5 (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 6 (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67201/524288 : ℝ)) 7 (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67201/524288 : ℝ))) (88791845383/500000000000 : ℝ) (44395922693/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88791845383/500000000000 : ℝ) (44395922693/250000000000 : ℝ) (588791845383/1000000000000 : ℝ) (294395922693/500000000000 : ℝ) (21070339981/50000000000 : ℝ) (105351699907/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 1 (588791845383/1000000000000 : ℝ) (294395922693/500000000000 : ℝ) (21070339981/50000000000 : ℝ) (105351699907/250000000000 : ℝ) (505099322501/1000000000000 : ℝ) (505099322507/1000000000000 : ℝ) (498117342807/1000000000000 : ℝ) (249058671407/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 2 (505099322501/1000000000000 : ℝ) (505099322507/1000000000000 : ℝ) (498117342807/1000000000000 : ℝ) (249058671407/500000000000 : ℝ) (250804166327/500000000000 : ℝ) (501608332661/1000000000000 : ℝ) (125399046143/250000000000 : ℝ) (25079809229/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 3 (250804166327/500000000000 : ℝ) (501608332661/1000000000000 : ℝ) (125399046143/250000000000 : ℝ) (25079809229/50000000000 : ℝ) (501602258613/1000000000000 : ℝ) (501602258621/1000000000000 : ℝ) (31350141161/62500000000 : ℝ) (62700282323/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 4 (501602258613/1000000000000 : ℝ) (501602258621/1000000000000 : ℝ) (31350141161/62500000000 : ℝ) (62700282323/125000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 5 (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 6 (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67201/524288 : ℝ))) 7 (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67201/524288 : ℝ)) hmem 8 (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67201/524288 : ℝ))) hcmem 8 (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67201/524288 : ℝ)) (248009233729/250000000000 : ℝ) (992036934919/1000000000000 : ℝ) (250801129297/500000000000 : ℝ) (501602258603/1000000000000 : ℝ) (79423956667/100000000000 : ℝ) (24819986459/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1128_exp_lower
  have heNumeric : (16053929329/7812500000 : ℝ)/4 ≤ Real.exp (-666065738563/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16053929329/7812500000 : ℝ)/4 ≤ Real.exp ((525/4096 : ℝ)-(24819986459/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (525/4096 : ℝ) (67201/524288 : ℝ) (24819986459/31250000000 : ℝ) (16053929329/7812500000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1129; no trusted numerical premise.
theorem cover8_leaf1129_exp_radius : (62374951784241887/62500000000000000 : ℝ) ≤ Real.exp ((-33601/2097152 : ℝ)/8) ∧ Real.exp ((-33601/2097152 : ℝ)/8) ≤ (997999228547870193/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33601/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1129_exp_lower : (92011352788800733/100000000000000000 : ℝ) ≤ Real.exp ((-17051282774819/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051282774819/25600000000000 : ℝ)/8) ≤ (920113527888007331/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051282774819/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1129_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902964739/1000000000000 : ℝ) ≤ 4*Real.exp (67201/524288 : ℝ)*Real.exp (-mu (radius 8 (33601/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902964739/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33601/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1129_exp_radius
  have hrNumeric : (984105467403/1000000000000 : ℝ) ≤ Real.exp (-33601/2097152 : ℝ) ∧ Real.exp (-33601/2097152 : ℝ) ≤ (246026366851/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984105467403/1000000000000 : ℝ) ≤ (radius 8 (33601/262144 : ℝ)) ∧ (radius 8 (33601/262144 : ℝ)) ≤ (246026366851/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33601/262144 : ℝ)) (984105467403/1000000000000 : ℝ) (246026366851/250000000000 : ℝ) (177584990991/1000000000000 : ℝ) (88792495499/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33601/262144 : ℝ)) (984105467403/1000000000000 : ℝ) (246026366851/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984105467403/1000000000000 : ℝ) (246026366851/250000000000 : ℝ) (992052733701/1000000000000 : ℝ) (496026366851/500000000000 : ℝ) (62001306293/62500000000 : ℝ) (99202090069/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 1 (992052733701/1000000000000 : ℝ) (496026366851/500000000000 : ℝ) (62001306293/62500000000 : ℝ) (99202090069/100000000000 : ℝ) (496018408597/500000000000 : ℝ) (248009204299/250000000000 : ℝ) (496018408533/500000000000 : ℝ) (992036817069/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 2 (496018408597/500000000000 : ℝ) (248009204299/250000000000 : ℝ) (496018408533/500000000000 : ℝ) (992036817069/1000000000000 : ℝ) (99203681713/100000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 3 (99203681713/100000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 4 (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 5 (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 6 (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33601/262144 : ℝ)) 7 (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33601/262144 : ℝ))) (177584990991/1000000000000 : ℝ) (88792495499/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177584990991/1000000000000 : ℝ) (88792495499/500000000000 : ℝ) (117758499099/200000000000 : ℝ) (588792495499/1000000000000 : ℝ) (6584505349/15625000000 : ℝ) (210704171173/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 1 (117758499099/200000000000 : ℝ) (588792495499/1000000000000 : ℝ) (6584505349/15625000000 : ℝ) (210704171173/500000000000 : ℝ) (101020083783/200000000000 : ℝ) (505100418923/1000000000000 : ℝ) (19924741183/40000000000 : ℝ) (31132408099/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 2 (101020083783/200000000000 : ℝ) (505100418923/1000000000000 : ℝ) (19924741183/40000000000 : ℝ) (31132408099/62500000000 : ℝ) (100321894849/200000000000 : ℝ) (250804737127/500000000000 : ℝ) (100319465301/200000000000 : ℝ) (100319465303/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 3 (100321894849/200000000000 : ℝ) (250804737127/500000000000 : ℝ) (100319465301/200000000000 : ℝ) (100319465303/200000000000 : ℝ) (4012827203/8000000000 : ℝ) (100320680077/200000000000 : ℝ) (250801700169/500000000000 : ℝ) (125400850087/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 4 (4012827203/8000000000 : ℝ) (100320680077/200000000000 : ℝ) (250801700169/500000000000 : ℝ) (125400850087/250000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 5 (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 6 (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33601/262144 : ℝ))) 7 (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33601/262144 : ℝ)) hmem 8 (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33601/262144 : ℝ))) hcmem 8 (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33601/262144 : ℝ)) (992036817129/1000000000000 : ℝ) (992036817133/1000000000000 : ℝ) (125400850089/250000000000 : ℝ) (501603400367/1000000000000 : ℝ) (794241468843/1000000000000 : ℝ) (158848293773/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1129_exp_lower
  have heNumeric : (2054902964739/1000000000000 : ℝ)/4 ≤ Real.exp (-17051282774819/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902964739/1000000000000 : ℝ)/4 ≤ Real.exp ((67201/524288 : ℝ)-(158848293773/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67201/524288 : ℝ) (33601/262144 : ℝ) (158848293773/200000000000 : ℝ) (2054902964739/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1130; no trusted numerical premise.
theorem cover8_leaf1130_exp_radius : (997999198805175883/1000000000000000000 : ℝ) ≤ Real.exp ((-67203/4194304 : ℝ)/8) ∧ Real.exp ((-67203/4194304 : ℝ)/8) ≤ (249499799701293971/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67203/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1130_exp_lower : (920113528485233793/1000000000000000000 : ℝ) ≤ Real.exp ((-42628206604719/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628206604719/64000000000000 : ℝ)/8) ≤ (460056764242616897/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628206604719/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1130_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902975409/1000000000000 : ℝ) ≤ 4*Real.exp (33601/262144 : ℝ)*Real.exp (-mu (radius 8 (67203/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902975409/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67203/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1130_exp_radius
  have hrNumeric : (492052616387/500000000000 : ℝ) ≤ Real.exp (-67203/4194304 : ℝ) ∧ Real.exp (-67203/4194304 : ℝ) ≤ (39364209311/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492052616387/500000000000 : ℝ) ≤ (radius 8 (67203/524288 : ℝ)) ∧ (radius 8 (67203/524288 : ℝ)) ≤ (39364209311/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67203/524288 : ℝ)) (492052616387/500000000000 : ℝ) (39364209311/40000000000 : ℝ) (177586291207/1000000000000 : ℝ) (88793145607/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67203/524288 : ℝ)) (492052616387/500000000000 : ℝ) (39364209311/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492052616387/500000000000 : ℝ) (39364209311/40000000000 : ℝ) (992052616387/1000000000000 : ℝ) (248013154097/250000000000 : ℝ) (99202078243/100000000000 : ℝ) (992020782431/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 1 (992052616387/1000000000000 : ℝ) (248013154097/250000000000 : ℝ) (99202078243/100000000000 : ℝ) (992020782431/1000000000000 : ℝ) (62002293713/62500000000 : ℝ) (99203669941/100000000000 : ℝ) (12400458741/12500000000 : ℝ) (496018349641/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 2 (62002293713/62500000000 : ℝ) (99203669941/100000000000 : ℝ) (12400458741/12500000000 : ℝ) (496018349641/500000000000 : ℝ) (62002293709/62500000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 3 (62002293709/62500000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 4 (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 5 (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 6 (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67203/524288 : ℝ)) 7 (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67203/524288 : ℝ))) (177586291207/1000000000000 : ℝ) (88793145607/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177586291207/1000000000000 : ℝ) (88793145607/500000000000 : ℝ) (588793145603/1000000000000 : ℝ) (588793145607/1000000000000 : ℝ) (421409885037/1000000000000 : ℝ) (210704942523/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 1 (588793145603/1000000000000 : ℝ) (588793145607/1000000000000 : ℝ) (421409885037/1000000000000 : ℝ) (210704942523/500000000000 : ℝ) (12627537883/25000000000 : ℝ) (505101515327/1000000000000 : ℝ) (124529929083/250000000000 : ℝ) (24905985817/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 2 (12627537883/25000000000 : ℝ) (505101515327/1000000000000 : ℝ) (124529929083/250000000000 : ℝ) (24905985817/50000000000 : ℝ) (250805307913/500000000000 : ℝ) (250805307917/500000000000 : ℝ) (125399617107/250000000000 : ℝ) (501598468437/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 3 (250805307913/500000000000 : ℝ) (250805307917/500000000000 : ℝ) (125399617107/250000000000 : ℝ) (501598468437/1000000000000 : ℝ) (501604542127/1000000000000 : ℝ) (62700567767/125000000000 : ℝ) (50160454209/100000000000 : ℝ) (501604542099/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 4 (501604542127/1000000000000 : ℝ) (62700567767/125000000000 : ℝ) (50160454209/100000000000 : ℝ) (501604542099/1000000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 5 (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 6 (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67203/524288 : ℝ))) 7 (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67203/524288 : ℝ)) hmem 8 (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67203/524288 : ℝ))) hcmem 8 (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67203/524288 : ℝ)) (992036699343/1000000000000 : ℝ) (496018349673/500000000000 : ℝ) (125401135527/250000000000 : ℝ) (250802271059/500000000000 : ℝ) (397121685501/500000000000 : ℝ) (794243371021/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1130_exp_lower
  have heNumeric : (2054902975409/1000000000000 : ℝ)/4 ≤ Real.exp (-42628206604719/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902975409/1000000000000 : ℝ)/4 ≤ Real.exp ((33601/262144 : ℝ)-(794243371021/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33601/262144 : ℝ) (67203/524288 : ℝ) (794243371021/1000000000000 : ℝ) (2054902975409/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1131; no trusted numerical premise.
theorem cover8_leaf1131_exp_radius : (997999169062482461/1000000000000000000 : ℝ) ≤ Real.exp ((-16801/1048576 : ℝ)/8) ∧ Real.exp ((-16801/1048576 : ℝ)/8) ≤ (498999584531241231/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16801/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1131_exp_lower : (920113529084530511/1000000000000000000 : ℝ) ≤ Real.exp ((-85256412542477/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256412542477/128000000000000 : ℝ)/8) ≤ (57507095567783157/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256412542477/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1131_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902986117/1000000000000 : ℝ) ≤ 4*Real.exp (67203/524288 : ℝ)*Real.exp (-mu (radius 8 (16801/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902986117/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16801/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1131_exp_radius
  have hrNumeric : (196820999629/200000000000 : ℝ) ≤ Real.exp (-16801/1048576 : ℝ) ∧ Real.exp (-16801/1048576 : ℝ) ≤ (492052499073/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196820999629/200000000000 : ℝ) ≤ (radius 8 (16801/131072 : ℝ)) ∧ (radius 8 (16801/131072 : ℝ)) ≤ (492052499073/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16801/131072 : ℝ)) (196820999629/200000000000 : ℝ) (492052499073/500000000000 : ℝ) (177587591413/1000000000000 : ℝ) (8879379571/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16801/131072 : ℝ)) (196820999629/200000000000 : ℝ) (492052499073/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196820999629/200000000000 : ℝ) (492052499073/500000000000 : ℝ) (7750410149/7812500000 : ℝ) (992052499073/1000000000000 : ℝ) (248005166043/250000000000 : ℝ) (992020664173/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 1 (7750410149/7812500000 : ℝ) (992052499073/1000000000000 : ℝ) (248005166043/250000000000 : ℝ) (992020664173/1000000000000 : ℝ) (496018290811/500000000000 : ℝ) (992036581623/1000000000000 : ℝ) (496018290747/500000000000 : ℝ) (124004572687/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 2 (496018290811/500000000000 : ℝ) (992036581623/1000000000000 : ℝ) (496018290747/500000000000 : ℝ) (124004572687/125000000000 : ℝ) (496018290779/500000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 3 (496018290779/500000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 4 (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 5 (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 6 (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16801/131072 : ℝ)) 7 (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16801/131072 : ℝ))) (177587591413/1000000000000 : ℝ) (8879379571/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177587591413/1000000000000 : ℝ) (8879379571/50000000000 : ℝ) (294396897853/500000000000 : ℝ) (58879379571/100000000000 : ℝ) (421411427719/1000000000000 : ℝ) (421411427729/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 1 (294396897853/500000000000 : ℝ) (58879379571/100000000000 : ℝ) (421411427719/1000000000000 : ℝ) (421411427729/1000000000000 : ℝ) (1973057077/3906250000 : ℝ) (12627565293/25000000000 : ℝ) (19924836123/40000000000 : ℝ) (498120903083/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 2 (1973057077/3906250000 : ℝ) (12627565293/25000000000 : ℝ) (19924836123/40000000000 : ℝ) (498120903083/1000000000000 : ℝ) (501611757393/1000000000000 : ℝ) (250805878701/500000000000 : ℝ) (250799805169/500000000000 : ℝ) (501599610347/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 3 (501611757393/1000000000000 : ℝ) (250805878701/500000000000 : ℝ) (250799805169/500000000000 : ℝ) (501599610347/1000000000000 : ℝ) (100321136773/200000000000 : ℝ) (4012845471/8000000000 : ℝ) (125401420957/250000000000 : ℝ) (250802841919/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 4 (100321136773/200000000000 : ℝ) (4012845471/8000000000 : ℝ) (125401420957/250000000000 : ℝ) (250802841919/500000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 5 (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 6 (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16801/131072 : ℝ))) 7 (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16801/131072 : ℝ)) hmem 8 (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16801/131072 : ℝ))) hcmem 8 (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16801/131072 : ℝ)) (992036581557/1000000000000 : ℝ) (24800914539/25000000000 : ℝ) (250802841923/500000000000 : ℝ) (501605683857/1000000000000 : ℝ) (397122636569/500000000000 : ℝ) (794245273159/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1131_exp_lower
  have heNumeric : (2054902986117/1000000000000 : ℝ)/4 ≤ Real.exp (-85256412542477/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902986117/1000000000000 : ℝ)/4 ≤ Real.exp ((67203/524288 : ℝ)-(794245273159/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67203/524288 : ℝ) (16801/131072 : ℝ) (794245273159/1000000000000 : ℝ) (2054902986117/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1132; no trusted numerical premise.
theorem cover8_leaf1132_exp_radius : (39919965572791597/40000000000000000 : ℝ) ≤ Real.exp ((-67205/4194304 : ℝ)/8) ∧ Real.exp ((-67205/4194304 : ℝ)/8) ≤ (498999569659894963/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67205/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1132_exp_lower : (920113529686127513/1000000000000000000 : ℝ) ≤ Real.exp ((-21314102968239/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314102968239/32000000000000 : ℝ)/8) ≤ (460056764843063757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314102968239/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1132_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980599373/200000000000 : ℝ) ≤ 4*Real.exp (16801/131072 : ℝ)*Real.exp (-mu (radius 8 (67205/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980599373/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67205/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1132_exp_radius
  have hrNumeric : (246026190879/250000000000 : ℝ) ≤ Real.exp (-67205/4194304 : ℝ) ∧ Real.exp (-67205/4194304 : ℝ) ≤ (984104763517/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246026190879/250000000000 : ℝ) ≤ (radius 8 (67205/524288 : ℝ)) ∧ (radius 8 (67205/524288 : ℝ)) ≤ (984104763517/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67205/524288 : ℝ)) (246026190879/250000000000 : ℝ) (984104763517/1000000000000 : ℝ) (177588891609/1000000000000 : ℝ) (5549652863/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67205/524288 : ℝ)) (246026190879/250000000000 : ℝ) (984104763517/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246026190879/250000000000 : ℝ) (984104763517/1000000000000 : ℝ) (496026190879/500000000000 : ℝ) (992052381759/1000000000000 : ℝ) (496010272957/500000000000 : ℝ) (198404109183/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 1 (496026190879/500000000000 : ℝ) (992052381759/1000000000000 : ℝ) (496010272957/500000000000 : ℝ) (198404109183/200000000000 : ℝ) (248009115959/250000000000 : ℝ) (992036463837/1000000000000 : ℝ) (248009115927/250000000000 : ℝ) (99203646371/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 2 (248009115959/250000000000 : ℝ) (992036463837/1000000000000 : ℝ) (248009115927/250000000000 : ℝ) (99203646371/100000000000 : ℝ) (248009115943/250000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 3 (248009115943/250000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 4 (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 5 (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 6 (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67205/524288 : ℝ)) 7 (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67205/524288 : ℝ))) (177588891609/1000000000000 : ℝ) (5549652863/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177588891609/1000000000000 : ℝ) (5549652863/31250000000 : ℝ) (147198611451/250000000000 : ℝ) (36799652863/62500000000 : ℝ) (84282594077/200000000000 : ℝ) (210706485197/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 1 (147198611451/250000000000 : ℝ) (36799652863/62500000000 : ℝ) (84282594077/200000000000 : ℝ) (210706485197/500000000000 : ℝ) (252551854047/500000000000 : ℝ) (505103708101/1000000000000 : ℝ) (99624417961/200000000000 : ℝ) (498122089813/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 2 (252551854047/500000000000 : ℝ) (505103708101/1000000000000 : ℝ) (99624417961/200000000000 : ℝ) (498122089813/1000000000000 : ℝ) (501612898949/1000000000000 : ℝ) (501612898957/1000000000000 : ℝ) (125400188059/250000000000 : ℝ) (125400188061/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 3 (501612898949/1000000000000 : ℝ) (501612898957/1000000000000 : ℝ) (125400188059/250000000000 : ℝ) (125400188061/250000000000 : ℝ) (62700853199/125000000000 : ℝ) (501606825601/1000000000000 : ℝ) (100321365111/200000000000 : ℝ) (125401706391/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 4 (62700853199/125000000000 : ℝ) (501606825601/1000000000000 : ℝ) (100321365111/200000000000 : ℝ) (125401706391/250000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 5 (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 6 (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67205/524288 : ℝ))) 7 (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67205/524288 : ℝ)) hmem 8 (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67205/524288 : ℝ))) hcmem 8 (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67205/524288 : ℝ)) (992036463771/1000000000000 : ℝ) (496018231887/500000000000 : ℝ) (501606825573/1000000000000 : ℝ) (501606825583/1000000000000 : ℝ) (794247175257/1000000000000 : ℝ) (794247175277/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1132_exp_lower
  have heNumeric : (410980599373/200000000000 : ℝ)/4 ≤ Real.exp (-21314102968239/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980599373/200000000000 : ℝ)/4 ≤ Real.exp ((16801/131072 : ℝ)-(794247175277/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16801/131072 : ℝ) (67205/524288 : ℝ) (794247175277/1000000000000 : ℝ) (410980599373/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1133; no trusted numerical premise.
theorem cover8_leaf1133_exp_radius : (249499777394274569/250000000000000000 : ℝ) ≤ Real.exp ((-33603/2097152 : ℝ)/8) ∧ Real.exp ((-33603/2097152 : ℝ)/8) ≤ (997999109577098277/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33603/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1133_exp_lower : (920113530289679757/1000000000000000000 : ℝ) ≤ Real.exp ((-85256411201259/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256411201259/128000000000000 : ℝ)/8) ≤ (460056765144839879/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256411201259/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1133_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903007649/1000000000000 : ℝ) ≤ 4*Real.exp (67205/524288 : ℝ)*Real.exp (-mu (radius 8 (33603/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903007649/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33603/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1133_exp_radius
  have hrNumeric : (984104528887/1000000000000 : ℝ) ≤ Real.exp (-33603/2097152 : ℝ) ∧ Real.exp (-33603/2097152 : ℝ) ≤ (123013066111/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984104528887/1000000000000 : ℝ) ≤ (radius 8 (33603/262144 : ℝ)) ∧ (radius 8 (33603/262144 : ℝ)) ≤ (123013066111/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33603/262144 : ℝ)) (984104528887/1000000000000 : ℝ) (123013066111/125000000000 : ℝ) (35518038359/200000000000 : ℝ) (88795095901/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33603/262144 : ℝ)) (984104528887/1000000000000 : ℝ) (123013066111/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984104528887/1000000000000 : ℝ) (123013066111/125000000000 : ℝ) (992052264443/1000000000000 : ℝ) (248013066111/250000000000 : ℝ) (124002553457/125000000000 : ℝ) (992020427657/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 1 (992052264443/1000000000000 : ℝ) (248013066111/250000000000 : ℝ) (124002553457/125000000000 : ℝ) (992020427657/1000000000000 : ℝ) (992036346049/1000000000000 : ℝ) (992036346051/1000000000000 : ℝ) (992036345921/1000000000000 : ℝ) (992036345923/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 2 (992036346049/1000000000000 : ℝ) (992036346051/1000000000000 : ℝ) (992036345921/1000000000000 : ℝ) (992036345923/1000000000000 : ℝ) (198407269197/200000000000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 3 (198407269197/200000000000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 4 (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 5 (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 6 (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33603/262144 : ℝ)) 7 (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33603/262144 : ℝ))) (35518038359/200000000000 : ℝ) (88795095901/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35518038359/200000000000 : ℝ) (88795095901/500000000000 : ℝ) (588795095897/1000000000000 : ℝ) (588795095901/1000000000000 : ℝ) (421414513033/1000000000000 : ℝ) (210707256521/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 1 (588795095897/1000000000000 : ℝ) (588795095901/1000000000000 : ℝ) (421414513033/1000000000000 : ℝ) (210707256521/500000000000 : ℝ) (101020960893/200000000000 : ℝ) (63138100559/125000000000 : ℝ) (249061638261/500000000000 : ℝ) (49812327653/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 2 (101020960893/200000000000 : ℝ) (63138100559/125000000000 : ℝ) (249061638261/500000000000 : ℝ) (49812327653/100000000000 : ℝ) (501614040493/1000000000000 : ℝ) (501614040501/1000000000000 : ℝ) (250800947061/500000000000 : ℝ) (50160189413/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 3 (501614040493/1000000000000 : ℝ) (501614040501/1000000000000 : ℝ) (250800947061/500000000000 : ℝ) (50160189413/100000000000 : ℝ) (501607967307/1000000000000 : ℝ) (125401991829/250000000000 : ℝ) (50160796727/100000000000 : ℝ) (501607967279/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 4 (501607967307/1000000000000 : ℝ) (125401991829/250000000000 : ℝ) (50160796727/100000000000 : ℝ) (501607967279/1000000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 5 (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 6 (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33603/262144 : ℝ))) 7 (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33603/262144 : ℝ)) hmem 8 (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33603/262144 : ℝ))) hcmem 8 (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33603/262144 : ℝ)) (7750283953/7812500000 : ℝ) (992036345987/1000000000000 : ℝ) (62700995911/125000000000 : ℝ) (250803983649/500000000000 : ℝ) (794249077359/1000000000000 : ℝ) (397124538689/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1133_exp_lower
  have heNumeric : (2054903007649/1000000000000 : ℝ)/4 ≤ Real.exp (-85256411201259/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903007649/1000000000000 : ℝ)/4 ≤ Real.exp ((67205/524288 : ℝ)-(397124538689/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67205/524288 : ℝ) (33603/262144 : ℝ) (397124538689/500000000000 : ℝ) (2054903007649/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1134; no trusted numerical premise.
theorem cover8_leaf1134_exp_radius : (997999079834407513/1000000000000000000 : ℝ) ≤ Real.exp ((-67207/4194304 : ℝ)/8) ∧ Real.exp ((-67207/4194304 : ℝ)/8) ≤ (498999539917203757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67207/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1134_exp_lower : (115014191362042173/125000000000000000 : ℝ) ≤ Real.exp ((-42628205263053/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628205263053/64000000000000 : ℝ)/8) ≤ (184022706179267477/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628205263053/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1134_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903018487/1000000000000 : ℝ) ≤ 4*Real.exp (33603/262144 : ℝ)*Real.exp (-mu (radius 8 (67207/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903018487/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67207/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1134_exp_radius
  have hrNumeric : (984104294259/1000000000000 : ℝ) ≤ Real.exp (-67207/4194304 : ℝ) ∧ Real.exp (-67207/4194304 : ℝ) ≤ (49205214713/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984104294259/1000000000000 : ℝ) ≤ (radius 8 (67207/524288 : ℝ)) ∧ (radius 8 (67207/524288 : ℝ)) ≤ (49205214713/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67207/524288 : ℝ)) (984104294259/1000000000000 : ℝ) (49205214713/50000000000 : ℝ) (88795745983/500000000000 : ℝ) (177591491973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67207/524288 : ℝ)) (984104294259/1000000000000 : ℝ) (49205214713/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984104294259/1000000000000 : ℝ) (49205214713/50000000000 : ℝ) (992052147129/1000000000000 : ℝ) (99205214713/100000000000 : ℝ) (496010154699/500000000000 : ℝ) (992020309399/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 1 (992052147129/1000000000000 : ℝ) (99205214713/100000000000 : ℝ) (496010154699/500000000000 : ℝ) (992020309399/1000000000000 : ℝ) (992036228263/1000000000000 : ℝ) (198407245653/200000000000 : ℝ) (198407245627/200000000000 : ℝ) (992036228137/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 2 (992036228263/1000000000000 : ℝ) (198407245653/200000000000 : ℝ) (198407245627/200000000000 : ℝ) (992036228137/1000000000000 : ℝ) (992036228199/1000000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 3 (992036228199/1000000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 4 (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 5 (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 6 (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67207/524288 : ℝ)) 7 (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67207/524288 : ℝ))) (88795745983/500000000000 : ℝ) (177591491973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88795745983/500000000000 : ℝ) (177591491973/1000000000000 : ℝ) (588795745983/1000000000000 : ℝ) (588795745987/1000000000000 : ℝ) (421416055657/1000000000000 : ℝ) (210708027833/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 1 (588795745983/1000000000000 : ℝ) (588795745987/1000000000000 : ℝ) (421416055657/1000000000000 : ℝ) (210708027833/500000000000 : ℝ) (25255295041/50000000000 : ℝ) (505105900827/1000000000000 : ℝ) (498124463221/1000000000000 : ℝ) (498124463229/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 2 (25255295041/50000000000 : ℝ) (505105900827/1000000000000 : ℝ) (498124463221/1000000000000 : ℝ) (498124463229/1000000000000 : ℝ) (25080759101/50000000000 : ℝ) (125403795507/250000000000 : ℝ) (501603035991/1000000000000 : ℝ) (501603035999/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 3 (25080759101/50000000000 : ℝ) (125403795507/250000000000 : ℝ) (501603035991/1000000000000 : ℝ) (501603035999/1000000000000 : ℝ) (100321821801/200000000000 : ℝ) (250804554507/500000000000 : ℝ) (62701138621/125000000000 : ℝ) (501609108977/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 4 (100321821801/200000000000 : ℝ) (250804554507/500000000000 : ℝ) (62701138621/125000000000 : ℝ) (501609108977/1000000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 5 (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 6 (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67207/524288 : ℝ))) 7 (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67207/524288 : ℝ)) hmem 8 (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67207/524288 : ℝ))) hcmem 8 (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67207/524288 : ℝ)) (496018114099/500000000000 : ℝ) (992036228201/1000000000000 : ℝ) (250804554493/500000000000 : ℝ) (125402277249/250000000000 : ℝ) (794250979433/1000000000000 : ℝ) (198562744863/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1134_exp_lower
  have heNumeric : (2054903018487/1000000000000 : ℝ)/4 ≤ Real.exp (-42628205263053/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903018487/1000000000000 : ℝ)/4 ≤ Real.exp ((33603/262144 : ℝ)-(198562744863/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33603/262144 : ℝ) (67207/524288 : ℝ) (198562744863/250000000000 : ℝ) (2054903018487/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1135; no trusted numerical premise.
theorem cover8_leaf1135_exp_radius : (249499762522929409/250000000000000000 : ℝ) ≤ Real.exp ((-8401/524288 : ℝ)/8) ∧ Real.exp ((-8401/524288 : ℝ)/8) ≤ (997999050091717637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8401/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1135_exp_lower : (460056765752072577/500000000000000000 : ℝ) ≤ Real.exp ((-85256409849673/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256409849673/128000000000000 : ℝ)/8) ≤ (184022706300829031/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256409849673/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1135_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903029347/1000000000000 : ℝ) ≤ 4*Real.exp (67207/524288 : ℝ)*Real.exp (-mu (radius 8 (8401/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903029347/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8401/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1135_exp_radius
  have hrNumeric : (98410405963/100000000000 : ℝ) ≤ Real.exp (-8401/524288 : ℝ) ∧ Real.exp (-8401/524288 : ℝ) ≤ (984104059631/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98410405963/100000000000 : ℝ) ≤ (radius 8 (8401/65536 : ℝ)) ∧ (radius 8 (8401/65536 : ℝ)) ≤ (984104059631/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8401/65536 : ℝ)) (98410405963/100000000000 : ℝ) (984104059631/1000000000000 : ℝ) (177592792133/1000000000000 : ℝ) (8879639607/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8401/65536 : ℝ)) (98410405963/100000000000 : ℝ) (984104059631/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98410405963/100000000000 : ℝ) (984104059631/1000000000000 : ℝ) (198410405963/200000000000 : ℝ) (124006503727/125000000000 : ℝ) (49601009557/50000000000 : ℝ) (992020191141/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 1 (198410405963/200000000000 : ℝ) (124006503727/125000000000 : ℝ) (49601009557/50000000000 : ℝ) (992020191141/1000000000000 : ℝ) (992036110477/1000000000000 : ℝ) (992036110479/1000000000000 : ℝ) (992036110349/1000000000000 : ℝ) (992036110351/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 2 (992036110477/1000000000000 : ℝ) (992036110479/1000000000000 : ℝ) (992036110349/1000000000000 : ℝ) (992036110351/1000000000000 : ℝ) (992036110413/1000000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 3 (992036110413/1000000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 4 (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 5 (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 6 (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8401/65536 : ℝ)) 7 (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8401/65536 : ℝ))) (177592792133/1000000000000 : ℝ) (8879639607/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177592792133/1000000000000 : ℝ) (8879639607/50000000000 : ℝ) (294398198033/500000000000 : ℝ) (58879639607/100000000000 : ℝ) (421417598271/1000000000000 : ℝ) (10535439957/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 1 (294398198033/500000000000 : ℝ) (58879639607/100000000000 : ℝ) (421417598271/1000000000000 : ℝ) (10535439957/25000000000 : ℝ) (31569187323/62500000000 : ℝ) (20204279887/40000000000 : ℝ) (62265706239/125000000000 : ℝ) (48645083/97656250 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 2 (31569187323/62500000000 : ℝ) (20204279887/40000000000 : ℝ) (62265706239/125000000000 : ℝ) (48645083/97656250 : ℝ) (25080816177/50000000000 : ℝ) (125404080887/250000000000 : ℝ) (125401044463/250000000000 : ℝ) (501604177861/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 3 (25080816177/50000000000 : ℝ) (125404080887/250000000000 : ℝ) (125401044463/250000000000 : ℝ) (501604177861/1000000000000 : ℝ) (62701281337/125000000000 : ℝ) (100322050141/200000000000 : ℝ) (501610250659/1000000000000 : ℝ) (125402562667/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 4 (62701281337/125000000000 : ℝ) (100322050141/200000000000 : ℝ) (501610250659/1000000000000 : ℝ) (125402562667/250000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 5 (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 6 (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8401/65536 : ℝ))) 7 (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8401/65536 : ℝ)) hmem 8 (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8401/65536 : ℝ))) hcmem 8 (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8401/65536 : ℝ)) (248009027603/250000000000 : ℝ) (198407222083/200000000000 : ℝ) (501610250677/1000000000000 : ℝ) (501610250687/1000000000000 : ℝ) (99281610187/125000000000 : ℝ) (198563220379/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1135_exp_lower
  have heNumeric : (2054903029347/1000000000000 : ℝ)/4 ≤ Real.exp (-85256409849673/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903029347/1000000000000 : ℝ)/4 ≤ Real.exp ((67207/524288 : ℝ)-(198563220379/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67207/524288 : ℝ) (8401/65536 : ℝ) (198563220379/250000000000 : ℝ) (2054903029347/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1136; no trusted numerical premise.
theorem cover8_leaf1136_exp_radius : (498999510174514323/500000000000000000 : ℝ) ≤ Real.exp ((-67209/4194304 : ℝ)/8) ∧ Real.exp ((-67209/4194304 : ℝ)/8) ≤ (997999020349028647/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67209/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1136_exp_lower : (460056766057184111/500000000000000000 : ℝ) ≤ Real.exp ((-10657051146319/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657051146319/16000000000000 : ℝ)/8) ≤ (920113532114368223/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657051146319/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1136_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903040249/1000000000000 : ℝ) ≤ 4*Real.exp (8401/65536 : ℝ)*Real.exp (-mu (radius 8 (67209/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903040249/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67209/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1136_exp_radius
  have hrNumeric : (984103825001/1000000000000 : ℝ) ≤ Real.exp (-67209/4194304 : ℝ) ∧ Real.exp (-67209/4194304 : ℝ) ≤ (492051912501/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984103825001/1000000000000 : ℝ) ≤ (radius 8 (67209/524288 : ℝ)) ∧ (radius 8 (67209/524288 : ℝ)) ≤ (492051912501/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67209/524288 : ℝ)) (984103825001/1000000000000 : ℝ) (492051912501/500000000000 : ℝ) (17759409229/100000000000 : ℝ) (22199261537/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67209/524288 : ℝ)) (984103825001/1000000000000 : ℝ) (492051912501/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984103825001/1000000000000 : ℝ) (492051912501/500000000000 : ℝ) (79364153/80000000 : ℝ) (992051912501/1000000000000 : ℝ) (496010036441/500000000000 : ℝ) (992020072883/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 1 (79364153/80000000 : ℝ) (992051912501/1000000000000 : ℝ) (496010036441/500000000000 : ℝ) (992020072883/1000000000000 : ℝ) (992035992691/1000000000000 : ℝ) (248008998173/250000000000 : ℝ) (992035992563/1000000000000 : ℝ) (198407198513/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 2 (992035992691/1000000000000 : ℝ) (248008998173/250000000000 : ℝ) (992035992563/1000000000000 : ℝ) (198407198513/200000000000 : ℝ) (992035992627/1000000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 3 (992035992627/1000000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 4 (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 5 (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 6 (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67209/524288 : ℝ)) 7 (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67209/524288 : ℝ))) (17759409229/100000000000 : ℝ) (22199261537/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17759409229/100000000000 : ℝ) (22199261537/125000000000 : ℝ) (117759409229/200000000000 : ℝ) (147199261537/250000000000 : ℝ) (105354785217/250000000000 : ℝ) (105354785219/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 1 (117759409229/200000000000 : ℝ) (147199261537/250000000000 : ℝ) (105354785217/250000000000 : ℝ) (105354785219/250000000000 : ℝ) (252554046753/500000000000 : ℝ) (63138511689/125000000000 : ℝ) (49812683659/100000000000 : ℝ) (498126836597/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 2 (252554046753/500000000000 : ℝ) (63138511689/125000000000 : ℝ) (49812683659/100000000000 : ℝ) (498126836597/1000000000000 : ℝ) (62702183131/125000000000 : ℝ) (100323493011/200000000000 : ℝ) (250802659851/500000000000 : ℝ) (50160531971/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 3 (62702183131/125000000000 : ℝ) (100323493011/200000000000 : ℝ) (250802659851/500000000000 : ℝ) (50160531971/100000000000 : ℝ) (4012891139/8000000000 : ℝ) (501611392383/1000000000000 : ℝ) (250805696169/500000000000 : ℝ) (250805696173/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 4 (4012891139/8000000000 : ℝ) (501611392383/1000000000000 : ℝ) (250805696169/500000000000 : ℝ) (250805696173/500000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 5 (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 6 (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67209/524288 : ℝ))) 7 (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67209/524288 : ℝ)) hmem 8 (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67209/524288 : ℝ))) hcmem 8 (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67209/524288 : ℝ)) (496017996313/500000000000 : ℝ) (992035992629/1000000000000 : ℝ) (125402848089/250000000000 : ℝ) (100322278473/200000000000 : ℝ) (794254783541/1000000000000 : ℝ) (794254783559/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1136_exp_lower
  have heNumeric : (2054903040249/1000000000000 : ℝ)/4 ≤ Real.exp (-10657051146319/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903040249/1000000000000 : ℝ)/4 ≤ Real.exp ((8401/65536 : ℝ)-(794254783559/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8401/65536 : ℝ) (67209/524288 : ℝ) (794254783559/1000000000000 : ℝ) (2054903040249/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1137; no trusted numerical premise.
theorem cover8_leaf1137_exp_radius : (498999495303170271/500000000000000000 : ℝ) ≤ Real.exp ((-33605/2097152 : ℝ)/8) ∧ Real.exp ((-33605/2097152 : ℝ)/8) ≤ (997998990606340543/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33605/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1137_exp_lower : (460056766363733323/500000000000000000 : ℝ) ≤ Real.exp ((-85256408488231/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256408488231/128000000000000 : ℝ)/8) ≤ (920113532727466647/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256408488231/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1137_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903051203/1000000000000 : ℝ) ≤ 4*Real.exp (67209/524288 : ℝ)*Real.exp (-mu (radius 8 (33605/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903051203/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33605/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1137_exp_radius
  have hrNumeric : (984103590373/1000000000000 : ℝ) ≤ Real.exp (-33605/2097152 : ℝ) ∧ Real.exp (-33605/2097152 : ℝ) ≤ (492051795187/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984103590373/1000000000000 : ℝ) ≤ (radius 8 (33605/262144 : ℝ)) ∧ (radius 8 (33605/262144 : ℝ)) ≤ (492051795187/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33605/262144 : ℝ)) (984103590373/1000000000000 : ℝ) (492051795187/500000000000 : ℝ) (177595392431/1000000000000 : ℝ) (88797696219/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33605/262144 : ℝ)) (984103590373/1000000000000 : ℝ) (492051795187/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984103590373/1000000000000 : ℝ) (492051795187/500000000000 : ℝ) (496025897593/500000000000 : ℝ) (992051795187/1000000000000 : ℝ) (15500311791/15625000000 : ℝ) (7936159637/8000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 1 (496025897593/500000000000 : ℝ) (992051795187/1000000000000 : ℝ) (15500311791/15625000000 : ℝ) (7936159637/8000000000 : ℝ) (198407174981/200000000000 : ℝ) (496017937453/500000000000 : ℝ) (992035874777/1000000000000 : ℝ) (992035874779/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 2 (198407174981/200000000000 : ℝ) (496017937453/500000000000 : ℝ) (992035874777/1000000000000 : ℝ) (992035874779/1000000000000 : ℝ) (992035874841/1000000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 3 (992035874841/1000000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 4 (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 5 (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 6 (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33605/262144 : ℝ)) 7 (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33605/262144 : ℝ))) (177595392431/1000000000000 : ℝ) (88797696219/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177595392431/1000000000000 : ℝ) (88797696219/500000000000 : ℝ) (117759539243/200000000000 : ℝ) (588797696219/1000000000000 : ℝ) (421420683439/1000000000000 : ℝ) (421420683449/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 1 (117759539243/200000000000 : ℝ) (588797696219/1000000000000 : ℝ) (421420683439/1000000000000 : ℝ) (421420683449/1000000000000 : ℝ) (505109189827/1000000000000 : ℝ) (252554594917/500000000000 : ℝ) (498128023249/1000000000000 : ℝ) (498128023257/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 2 (505109189827/1000000000000 : ℝ) (252554594917/500000000000 : ℝ) (498128023249/1000000000000 : ℝ) (498128023257/1000000000000 : ℝ) (250809303269/500000000000 : ℝ) (250809303273/500000000000 : ℝ) (250803230767/500000000000 : ℝ) (501606461543/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 3 (250809303269/500000000000 : ℝ) (250809303273/500000000000 : ℝ) (250803230767/500000000000 : ℝ) (501606461543/1000000000000 : ℝ) (125403133509/250000000000 : ℝ) (100322506809/200000000000 : ℝ) (501612533999/1000000000000 : ℝ) (62701566751/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 4 (125403133509/250000000000 : ℝ) (100322506809/200000000000 : ℝ) (501612533999/1000000000000 : ℝ) (62701566751/125000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 5 (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 6 (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33605/262144 : ℝ))) 7 (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33605/262144 : ℝ)) hmem 8 (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33605/262144 : ℝ))) hcmem 8 (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33605/262144 : ℝ)) (24800896871/25000000000 : ℝ) (992035874843/1000000000000 : ℝ) (501612534017/1000000000000 : ℝ) (501612534027/1000000000000 : ℝ) (397128342779/500000000000 : ℝ) (794256685577/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1137_exp_lower
  have heNumeric : (2054903051203/1000000000000 : ℝ)/4 ≤ Real.exp (-85256408488231/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903051203/1000000000000 : ℝ)/4 ≤ Real.exp ((67209/524288 : ℝ)-(794256685577/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67209/524288 : ℝ) (33605/262144 : ℝ) (794256685577/1000000000000 : ℝ) (2054903051203/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1138; no trusted numerical premise.
theorem cover8_leaf1138_exp_radius : (249499740215913331/250000000000000000 : ℝ) ≤ Real.exp ((-67211/4194304 : ℝ)/8) ∧ Real.exp ((-67211/4194304 : ℝ)/8) ≤ (39919958434546133/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67211/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1138_exp_lower : (36804541333673209/40000000000000000 : ℝ) ≤ Real.exp ((-42628203902251/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628203902251/64000000000000 : ℝ)/8) ≤ (460056766670915113/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628203902251/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1138_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745153109/50000000000 : ℝ) ≤ 4*Real.exp (33605/262144 : ℝ)*Real.exp (-mu (radius 8 (67211/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745153109/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67211/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1138_exp_radius
  have hrNumeric : (30753229867/31250000000 : ℝ) ≤ Real.exp (-67211/4194304 : ℝ) ∧ Real.exp (-67211/4194304 : ℝ) ≤ (196820671149/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30753229867/31250000000 : ℝ) ≤ (radius 8 (67211/524288 : ℝ)) ∧ (radius 8 (67211/524288 : ℝ)) ≤ (196820671149/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67211/524288 : ℝ)) (30753229867/31250000000 : ℝ) (196820671149/200000000000 : ℝ) (22199586571/125000000000 : ℝ) (7103867703/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67211/524288 : ℝ)) (30753229867/31250000000 : ℝ) (196820671149/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30753229867/31250000000 : ℝ) (196820671149/200000000000 : ℝ) (62003229867/62500000000 : ℝ) (992051677873/1000000000000 : ℝ) (496009918183/500000000000 : ℝ) (992019836367/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 1 (62003229867/62500000000 : ℝ) (992051677873/1000000000000 : ℝ) (496009918183/500000000000 : ℝ) (992019836367/1000000000000 : ℝ) (992035757119/1000000000000 : ℝ) (3100111741/3125000000 : ℝ) (992035756991/1000000000000 : ℝ) (992035756993/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 2 (992035757119/1000000000000 : ℝ) (3100111741/3125000000 : ℝ) (992035756991/1000000000000 : ℝ) (992035756993/1000000000000 : ℝ) (198407151411/200000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 3 (198407151411/200000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 4 (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 5 (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 6 (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67211/524288 : ℝ)) 7 (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67211/524288 : ℝ))) (22199586571/125000000000 : ℝ) (7103867703/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22199586571/125000000000 : ℝ) (7103867703/40000000000 : ℝ) (147199586571/250000000000 : ℝ) (36799896643/62500000000 : ℝ) (421422226001/1000000000000 : ℝ) (42142222601/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 1 (147199586571/250000000000 : ℝ) (36799896643/62500000000 : ℝ) (421422226001/1000000000000 : ℝ) (42142222601/100000000000 : ℝ) (252555143071/500000000000 : ℝ) (505110286149/1000000000000 : ℝ) (498129209901/1000000000000 : ℝ) (498129209909/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 2 (252555143071/500000000000 : ℝ) (505110286149/1000000000000 : ℝ) (498129209901/1000000000000 : ℝ) (498129209909/1000000000000 : ℝ) (501619748021/1000000000000 : ℝ) (501619748029/1000000000000 : ℝ) (3135047521/6250000000 : ℝ) (62700950421/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 3 (501619748021/1000000000000 : ℝ) (501619748029/1000000000000 : ℝ) (3135047521/6250000000 : ℝ) (62700950421/125000000000 : ℝ) (50161367569/100000000000 : ℝ) (501613675699/1000000000000 : ℝ) (501613675653/1000000000000 : ℝ) (250806837831/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 4 (50161367569/100000000000 : ℝ) (501613675699/1000000000000 : ℝ) (501613675653/1000000000000 : ℝ) (250806837831/500000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 5 (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 6 (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67211/524288 : ℝ))) 7 (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67211/524288 : ℝ)) hmem 8 (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67211/524288 : ℝ))) hcmem 8 (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67211/524288 : ℝ)) (496017878527/500000000000 : ℝ) (992035757057/1000000000000 : ℝ) (501613675671/1000000000000 : ℝ) (501613675681/1000000000000 : ℝ) (158851717513/200000000000 : ℝ) (12410290431/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1138_exp_lower
  have heNumeric : (102745153109/50000000000 : ℝ)/4 ≤ Real.exp (-42628203902251/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745153109/50000000000 : ℝ)/4 ≤ Real.exp ((33605/262144 : ℝ)-(12410290431/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33605/262144 : ℝ) (67211/524288 : ℝ) (12410290431/15625000000 : ℝ) (102745153109/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1139; no trusted numerical premise.
theorem cover8_leaf1139_exp_radius : (997998931120966993/1000000000000000000 : ℝ) ≤ Real.exp ((-16803/1048576 : ℝ)/8) ∧ Real.exp ((-16803/1048576 : ℝ)/8) ≤ (498999465560483497/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16803/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1139_exp_lower : (36804541358367367/40000000000000000 : ℝ) ≤ Real.exp ((-17051281423489/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051281423489/25600000000000 : ℝ)/8) ≤ (57507095872449011/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051281423489/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1139_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490307321/100000000000 : ℝ) ≤ 4*Real.exp (67211/524288 : ℝ)*Real.exp (-mu (radius 8 (16803/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490307321/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16803/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1139_exp_radius
  have hrNumeric : (246025780279/250000000000 : ℝ) ≤ Real.exp (-16803/1048576 : ℝ) ∧ Real.exp (-16803/1048576 : ℝ) ≤ (984103121117/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246025780279/250000000000 : ℝ) ≤ (radius 8 (16803/131072 : ℝ)) ∧ (radius 8 (16803/131072 : ℝ)) ≤ (984103121117/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16803/131072 : ℝ)) (246025780279/250000000000 : ℝ) (984103121117/1000000000000 : ℝ) (17759799269/100000000000 : ℝ) (177597992697/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16803/131072 : ℝ)) (246025780279/250000000000 : ℝ) (984103121117/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246025780279/250000000000 : ℝ) (984103121117/1000000000000 : ℝ) (496025780279/500000000000 : ℝ) (992051560559/1000000000000 : ℝ) (248004929527/250000000000 : ℝ) (992019718109/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 1 (496025780279/500000000000 : ℝ) (992051560559/1000000000000 : ℝ) (248004929527/250000000000 : ℝ) (992019718109/1000000000000 : ℝ) (992035639333/1000000000000 : ℝ) (496017819667/500000000000 : ℝ) (198407127841/200000000000 : ℝ) (992035639207/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 2 (992035639333/1000000000000 : ℝ) (496017819667/500000000000 : ℝ) (198407127841/200000000000 : ℝ) (992035639207/1000000000000 : ℝ) (992035639269/1000000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 3 (992035639269/1000000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 4 (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 5 (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 6 (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16803/131072 : ℝ)) 7 (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16803/131072 : ℝ))) (17759799269/100000000000 : ℝ) (177597992697/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17759799269/100000000000 : ℝ) (177597992697/1000000000000 : ℝ) (117759799269/200000000000 : ℝ) (588798996349/1000000000000 : ℝ) (421423768539/1000000000000 : ℝ) (105355942137/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 1 (117759799269/200000000000 : ℝ) (588798996349/1000000000000 : ℝ) (421423768539/1000000000000 : ℝ) (105355942137/250000000000 : ℝ) (252555691221/500000000000 : ℝ) (505111382449/1000000000000 : ℝ) (249065198267/500000000000 : ℝ) (249065198271/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 2 (252555691221/500000000000 : ℝ) (505111382449/1000000000000 : ℝ) (249065198267/500000000000 : ℝ) (249065198271/500000000000 : ℝ) (31351305593/62500000000 : ℝ) (62702611187/125000000000 : ℝ) (31350546573/62500000000 : ℝ) (501608745177/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 3 (31351305593/62500000000 : ℝ) (62702611187/125000000000 : ℝ) (31350546573/62500000000 : ℝ) (501608745177/1000000000000 : ℝ) (31350926083/62500000000 : ℝ) (501614817337/1000000000000 : ℝ) (501614817291/1000000000000 : ℝ) (5016148173/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 4 (31350926083/62500000000 : ℝ) (501614817337/1000000000000 : ℝ) (501614817291/1000000000000 : ℝ) (5016148173/10000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 5 (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 6 (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16803/131072 : ℝ))) 7 (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16803/131072 : ℝ)) hmem 8 (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16803/131072 : ℝ))) hcmem 8 (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16803/131072 : ℝ)) (248008909817/250000000000 : ℝ) (992035639271/1000000000000 : ℝ) (501614817309/1000000000000 : ℝ) (501614817319/1000000000000 : ℝ) (397130244773/500000000000 : ℝ) (158852097913/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1139_exp_lower
  have heNumeric : (205490307321/100000000000 : ℝ)/4 ≤ Real.exp (-17051281423489/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490307321/100000000000 : ℝ)/4 ≤ Real.exp ((67211/524288 : ℝ)-(158852097913/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67211/524288 : ℝ) (16803/131072 : ℝ) (158852097913/200000000000 : ℝ) (205490307321/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1140; no trusted numerical premise.
theorem cover8_leaf1140_exp_radius : (997998901378281549/1000000000000000000 : ℝ) ≤ Real.exp ((-67213/4194304 : ℝ)/8) ∧ Real.exp ((-67213/4194304 : ℝ)/8) ≤ (19959978027565631/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67213/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1140_exp_lower : (184022706915583659/200000000000000000 : ℝ) ≤ Real.exp ((-21314101607213/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314101607213/32000000000000 : ℝ)/8) ≤ (115014191822239787/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314101607213/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1140_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980616853/200000000000 : ℝ) ≤ 4*Real.exp (16803/131072 : ℝ)*Real.exp (-mu (radius 8 (67213/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980616853/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67213/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1140_exp_radius
  have hrNumeric : (984102886487/1000000000000 : ℝ) ≤ Real.exp (-67213/4194304 : ℝ) ∧ Real.exp (-67213/4194304 : ℝ) ≤ (123012860811/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984102886487/1000000000000 : ℝ) ≤ (radius 8 (67213/524288 : ℝ)) ∧ (radius 8 (67213/524288 : ℝ)) ≤ (123012860811/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67213/524288 : ℝ)) (984102886487/1000000000000 : ℝ) (123012860811/125000000000 : ℝ) (22199911601/125000000000 : ℝ) (88799646407/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67213/524288 : ℝ)) (984102886487/1000000000000 : ℝ) (123012860811/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984102886487/1000000000000 : ℝ) (123012860811/125000000000 : ℝ) (992051443243/1000000000000 : ℝ) (248012860811/250000000000 : ℝ) (19840391997/20000000000 : ℝ) (992019599851/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 1 (992051443243/1000000000000 : ℝ) (248012860811/250000000000 : ℝ) (19840391997/20000000000 : ℝ) (992019599851/1000000000000 : ℝ) (496017760773/500000000000 : ℝ) (248008880387/250000000000 : ℝ) (496017760709/500000000000 : ℝ) (49601776071/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 2 (496017760773/500000000000 : ℝ) (248008880387/250000000000 : ℝ) (496017760709/500000000000 : ℝ) (49601776071/50000000000 : ℝ) (496017760741/500000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 3 (496017760741/500000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 4 (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 5 (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 6 (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67213/524288 : ℝ)) 7 (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67213/524288 : ℝ))) (22199911601/125000000000 : ℝ) (88799646407/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22199911601/125000000000 : ℝ) (88799646407/500000000000 : ℝ) (147199911601/250000000000 : ℝ) (588799646407/1000000000000 : ℝ) (421425311067/1000000000000 : ℝ) (16857012443/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 1 (147199911601/250000000000 : ℝ) (588799646407/1000000000000 : ℝ) (421425311067/1000000000000 : ℝ) (16857012443/40000000000 : ℝ) (101022495747/200000000000 : ℝ) (505112478741/1000000000000 : ℝ) (12453289579/25000000000 : ℝ) (498131583167/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 2 (101022495747/200000000000 : ℝ) (505112478741/1000000000000 : ℝ) (12453289579/25000000000 : ℝ) (498131583167/1000000000000 : ℝ) (501622030947/1000000000000 : ℝ) (250811015477/500000000000 : ℝ) (50160988697/100000000000 : ℝ) (501609886977/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 3 (501622030947/1000000000000 : ℝ) (250811015477/500000000000 : ℝ) (50160988697/100000000000 : ℝ) (501609886977/1000000000000 : ℝ) (250807979479/500000000000 : ℝ) (250807979483/500000000000 : ℝ) (501615958921/1000000000000 : ℝ) (501615958929/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 4 (250807979479/500000000000 : ℝ) (250807979483/500000000000 : ℝ) (501615958921/1000000000000 : ℝ) (501615958929/1000000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 5 (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 6 (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67213/524288 : ℝ))) 7 (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67213/524288 : ℝ)) hmem 8 (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67213/524288 : ℝ))) hcmem 8 (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67213/524288 : ℝ)) (992035521481/1000000000000 : ℝ) (248008880371/250000000000 : ℝ) (501615958939/1000000000000 : ℝ) (125403989737/250000000000 : ℝ) (198565597879/250000000000 : ℝ) (397131195767/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1140_exp_lower
  have heNumeric : (410980616853/200000000000 : ℝ)/4 ≤ Real.exp (-21314101607213/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980616853/200000000000 : ℝ)/4 ≤ Real.exp ((16803/131072 : ℝ)-(397131195767/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16803/131072 : ℝ) (67213/524288 : ℝ) (397131195767/500000000000 : ℝ) (410980616853/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1141; no trusted numerical premise.
theorem cover8_leaf1141_exp_radius : (99799887163559699/100000000000000000 : ℝ) ≤ Real.exp ((-33607/2097152 : ℝ)/8) ∧ Real.exp ((-33607/2097152 : ℝ)/8) ≤ (997998871635596991/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33607/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1141_exp_lower : (460056767599878899/500000000000000000 : ℝ) ≤ Real.exp ((-85256405736803/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256405736803/128000000000000 : ℝ)/8) ≤ (920113535199757799/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256405736803/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1141_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16439224763/8000000000 : ℝ) ≤ 4*Real.exp (67213/524288 : ℝ)*Real.exp (-mu (radius 8 (33607/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (16439224763/8000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33607/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1141_exp_radius
  have hrNumeric : (984102651859/1000000000000 : ℝ) ≤ Real.exp (-33607/2097152 : ℝ) ∧ Real.exp (-33607/2097152 : ℝ) ≤ (49205132593/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984102651859/1000000000000 : ℝ) ≤ (radius 8 (33607/262144 : ℝ)) ∧ (radius 8 (33607/262144 : ℝ)) ≤ (49205132593/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33607/262144 : ℝ)) (984102651859/1000000000000 : ℝ) (49205132593/50000000000 : ℝ) (17760059291/100000000000 : ℝ) (44400148229/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33607/262144 : ℝ)) (984102651859/1000000000000 : ℝ) (49205132593/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984102651859/1000000000000 : ℝ) (49205132593/50000000000 : ℝ) (992051325929/1000000000000 : ℝ) (99205132593/100000000000 : ℝ) (124002435199/125000000000 : ℝ) (992019481593/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 1 (992051325929/1000000000000 : ℝ) (99205132593/100000000000 : ℝ) (124002435199/125000000000 : ℝ) (992019481593/1000000000000 : ℝ) (12400442547/12500000000 : ℝ) (496017701881/500000000000 : ℝ) (62002212727/62500000000 : ℝ) (496017701817/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 2 (12400442547/12500000000 : ℝ) (496017701881/500000000000 : ℝ) (62002212727/62500000000 : ℝ) (496017701817/500000000000 : ℝ) (62002212731/62500000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 3 (62002212731/62500000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 4 (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 5 (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 6 (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33607/262144 : ℝ)) 7 (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33607/262144 : ℝ))) (17760059291/100000000000 : ℝ) (44400148229/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17760059291/100000000000 : ℝ) (44400148229/250000000000 : ℝ) (117760059291/200000000000 : ℝ) (294400148229/500000000000 : ℝ) (42142685357/100000000000 : ℝ) (210713426789/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 1 (117760059291/200000000000 : ℝ) (294400148229/500000000000 : ℝ) (42142685357/100000000000 : ℝ) (210713426789/500000000000 : ℝ) (126278393753/250000000000 : ℝ) (252556787509/500000000000 : ℝ) (498132769767/1000000000000 : ℝ) (249066384887/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 2 (126278393753/250000000000 : ℝ) (252556787509/500000000000 : ℝ) (498132769767/1000000000000 : ℝ) (249066384887/500000000000 : ℝ) (501623172389/1000000000000 : ℝ) (125405793099/250000000000 : ℝ) (501611028753/1000000000000 : ℝ) (501611028761/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 3 (501623172389/1000000000000 : ℝ) (125405793099/250000000000 : ℝ) (501611028753/1000000000000 : ℝ) (501611028761/1000000000000 : ℝ) (501617100571/1000000000000 : ℝ) (501617100579/1000000000000 : ℝ) (250808550267/500000000000 : ℝ) (250808550271/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 4 (501617100571/1000000000000 : ℝ) (501617100579/1000000000000 : ℝ) (250808550267/500000000000 : ℝ) (250808550271/500000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 5 (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 6 (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33607/262144 : ℝ))) 7 (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33607/262144 : ℝ)) hmem 8 (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33607/262144 : ℝ))) hcmem 8 (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33607/262144 : ℝ)) (198407080739/200000000000 : ℝ) (496017701849/500000000000 : ℝ) (62702137569/125000000000 : ℝ) (501617100561/1000000000000 : ℝ) (794264293459/1000000000000 : ℝ) (198566073369/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1141_exp_lower
  have heNumeric : (16439224763/8000000000 : ℝ)/4 ≤ Real.exp (-85256405736803/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16439224763/8000000000 : ℝ)/4 ≤ Real.exp ((67213/524288 : ℝ)-(198566073369/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67213/524288 : ℝ) (33607/262144 : ℝ) (198566073369/250000000000 : ℝ) (16439224763/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1142; no trusted numerical premise.
theorem cover8_leaf1142_exp_radius : (997998841892913319/1000000000000000000 : ℝ) ≤ Real.exp ((-67215/4194304 : ℝ)/8) ∧ Real.exp ((-67215/4194304 : ℝ)/8) ≤ (24949971047322833/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67215/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1142_exp_lower : (230028383955686861/250000000000000000 : ℝ) ≤ Real.exp ((-42628202521737/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628202521737/64000000000000 : ℝ)/8) ≤ (184022707164549489/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628202521737/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1142_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980621301/200000000000 : ℝ) ≤ 4*Real.exp (33607/262144 : ℝ)*Real.exp (-mu (radius 8 (67215/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980621301/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67215/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1142_exp_radius
  have hrNumeric : (98410241723/100000000000 : ℝ) ≤ Real.exp (-67215/4194304 : ℝ) ∧ Real.exp (-67215/4194304 : ℝ) ≤ (984102417231/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98410241723/100000000000 : ℝ) ≤ (radius 8 (67215/524288 : ℝ)) ∧ (radius 8 (67215/524288 : ℝ)) ≤ (984102417231/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67215/524288 : ℝ)) (98410241723/100000000000 : ℝ) (984102417231/1000000000000 : ℝ) (11100118313/62500000000 : ℝ) (88800946507/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67215/524288 : ℝ)) (98410241723/100000000000 : ℝ) (984102417231/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98410241723/100000000000 : ℝ) (984102417231/1000000000000 : ℝ) (198410241723/200000000000 : ℝ) (124006401077/125000000000 : ℝ) (496009681667/500000000000 : ℝ) (198403872667/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 1 (198410241723/200000000000 : ℝ) (124006401077/125000000000 : ℝ) (496009681667/500000000000 : ℝ) (198403872667/200000000000 : ℝ) (496017642987/500000000000 : ℝ) (124004410747/125000000000 : ℝ) (496017642923/500000000000 : ℝ) (124004410731/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 2 (496017642987/500000000000 : ℝ) (124004410747/125000000000 : ℝ) (496017642923/500000000000 : ℝ) (124004410731/125000000000 : ℝ) (99203528591/100000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 3 (99203528591/100000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 4 (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 5 (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 6 (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67215/524288 : ℝ)) 7 (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67215/524288 : ℝ))) (11100118313/62500000000 : ℝ) (88800946507/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11100118313/62500000000 : ℝ) (88800946507/500000000000 : ℝ) (73600118313/125000000000 : ℝ) (588800946507/1000000000000 : ℝ) (210714198031/500000000000 : ℝ) (42142839607/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 1 (73600118313/125000000000 : ℝ) (588800946507/1000000000000 : ℝ) (210714198031/500000000000 : ℝ) (42142839607/100000000000 : ℝ) (505114671283/1000000000000 : ℝ) (505114671289/1000000000000 : ℝ) (249066978183/500000000000 : ℝ) (498133956373/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 2 (505114671283/1000000000000 : ℝ) (505114671289/1000000000000 : ℝ) (249066978183/500000000000 : ℝ) (498133956373/1000000000000 : ℝ) (15675759807/31250000000 : ℝ) (501624313831/1000000000000 : ℝ) (50161217053/100000000000 : ℝ) (250806085269/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 3 (15675759807/31250000000 : ℝ) (501624313831/1000000000000 : ℝ) (50161217053/100000000000 : ℝ) (250806085269/500000000000 : ℝ) (501618242177/1000000000000 : ℝ) (100323648437/200000000000 : ℝ) (25080912107/50000000000 : ℝ) (125404560537/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 4 (501618242177/1000000000000 : ℝ) (100323648437/200000000000 : ℝ) (25080912107/50000000000 : ℝ) (125404560537/250000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 5 (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 6 (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67215/524288 : ℝ))) 7 (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67215/524288 : ℝ)) hmem 8 (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67215/524288 : ℝ))) hcmem 8 (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67215/524288 : ℝ)) (992035285909/1000000000000 : ℝ) (124004410739/125000000000 : ℝ) (250809121079/500000000000 : ℝ) (501618242167/1000000000000 : ℝ) (794266195391/1000000000000 : ℝ) (49641637213/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1142_exp_lower
  have heNumeric : (410980621301/200000000000 : ℝ)/4 ≤ Real.exp (-42628202521737/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980621301/200000000000 : ℝ)/4 ≤ Real.exp ((33607/262144 : ℝ)-(49641637213/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33607/262144 : ℝ) (67215/524288 : ℝ) (49641637213/62500000000 : ℝ) (410980621301/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1143; no trusted numerical premise.
theorem cover8_leaf1143_exp_radius : (997998812150230533/1000000000000000000 : ℝ) ≤ Real.exp ((-4201/262144 : ℝ)/8) ∧ Real.exp ((-4201/262144 : ℝ)/8) ≤ (498999406075115267/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4201/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1143_exp_lower : (460056768224306223/500000000000000000 : ℝ) ≤ Real.exp ((-17051280869389/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051280869389/25600000000000 : ℝ)/8) ≤ (920113536448612447/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051280869389/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1143_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903117687/1000000000000 : ℝ) ≤ 4*Real.exp (67215/524288 : ℝ)*Real.exp (-mu (radius 8 (4201/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903117687/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4201/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1143_exp_radius
  have hrNumeric : (492051091301/500000000000 : ℝ) ≤ Real.exp (-4201/262144 : ℝ) ∧ Real.exp (-4201/262144 : ℝ) ≤ (984102182603/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492051091301/500000000000 : ℝ) ≤ (radius 8 (4201/32768 : ℝ)) ∧ (radius 8 (4201/32768 : ℝ)) ≤ (984102182603/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4201/32768 : ℝ)) (492051091301/500000000000 : ℝ) (984102182603/1000000000000 : ℝ) (17760319309/100000000000 : ℝ) (177603193097/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4201/32768 : ℝ)) (492051091301/500000000000 : ℝ) (984102182603/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492051091301/500000000000 : ℝ) (984102182603/1000000000000 : ℝ) (992051091301/1000000000000 : ℝ) (496025545651/500000000000 : ℝ) (248004811269/250000000000 : ℝ) (992019245077/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 1 (992051091301/1000000000000 : ℝ) (496025545651/500000000000 : ℝ) (248004811269/250000000000 : ℝ) (992019245077/1000000000000 : ℝ) (248008792047/250000000000 : ℝ) (99203516819/100000000000 : ℝ) (49601758403/50000000000 : ℝ) (496017584031/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 2 (248008792047/250000000000 : ℝ) (99203516819/100000000000 : ℝ) (49601758403/50000000000 : ℝ) (496017584031/500000000000 : ℝ) (248008792031/250000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 3 (248008792031/250000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 4 (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 5 (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 6 (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4201/32768 : ℝ)) 7 (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4201/32768 : ℝ))) (17760319309/100000000000 : ℝ) (177603193097/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17760319309/100000000000 : ℝ) (177603193097/1000000000000 : ℝ) (117760319309/200000000000 : ℝ) (588801596549/1000000000000 : ℝ) (42142993853/100000000000 : ℝ) (21071496927/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 1 (117760319309/200000000000 : ℝ) (588801596549/1000000000000 : ℝ) (42142993853/100000000000 : ℝ) (21071496927/50000000000 : ℝ) (505115767537/1000000000000 : ℝ) (101023153509/200000000000 : ℝ) (249067571473/500000000000 : ℝ) (99627028591/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 2 (505115767537/1000000000000 : ℝ) (101023153509/200000000000 : ℝ) (249067571473/500000000000 : ℝ) (99627028591/200000000000 : ℝ) (501625455241/1000000000000 : ℝ) (2006501821/4000000000 : ℝ) (501613312289/1000000000000 : ℝ) (501613312299/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 3 (501625455241/1000000000000 : ℝ) (2006501821/4000000000 : ℝ) (501613312289/1000000000000 : ℝ) (501613312299/1000000000000 : ℝ) (100323876753/200000000000 : ℝ) (20064775351/40000000000 : ℝ) (31351211483/62500000000 : ℝ) (250809691869/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 4 (100323876753/200000000000 : ℝ) (20064775351/40000000000 : ℝ) (31351211483/62500000000 : ℝ) (250809691869/500000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 5 (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 6 (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4201/32768 : ℝ))) 7 (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4201/32768 : ℝ)) hmem 8 (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4201/32768 : ℝ))) hcmem 8 (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4201/32768 : ℝ)) (992035168123/1000000000000 : ℝ) (496017584063/500000000000 : ℝ) (250809691873/500000000000 : ℝ) (501619383757/1000000000000 : ℝ) (158853619459/200000000000 : ℝ) (158853619463/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1143_exp_lower
  have heNumeric : (2054903117687/1000000000000 : ℝ)/4 ≤ Real.exp (-17051280869389/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903117687/1000000000000 : ℝ)/4 ≤ Real.exp ((67215/524288 : ℝ)-(158853619463/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67215/524288 : ℝ) (4201/32768 : ℝ) (158853619463/200000000000 : ℝ) (2054903117687/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1144; no trusted numerical premise.
theorem cover8_leaf1144_exp_radius : (498999391203774317/500000000000000000 : ℝ) ≤ Real.exp ((-67217/4194304 : ℝ)/8) ∧ Real.exp ((-67217/4194304 : ℝ)/8) ≤ (199599756481509727/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67217/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1144_exp_lower : (460056768538561387/500000000000000000 : ℝ) ≤ Real.exp ((-5328525227967/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328525227967/8000000000000 : ℝ)/8) ≤ (36804541483084911/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328525227967/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1144_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903128917/1000000000000 : ℝ) ≤ 4*Real.exp (4201/32768 : ℝ)*Real.exp (-mu (radius 8 (67217/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903128917/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67217/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1144_exp_radius
  have hrNumeric : (492050973987/500000000000 : ℝ) ≤ Real.exp (-67217/4194304 : ℝ) ∧ Real.exp (-67217/4194304 : ℝ) ≤ (39364077919/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492050973987/500000000000 : ℝ) ≤ (radius 8 (67217/524288 : ℝ)) ∧ (radius 8 (67217/524288 : ℝ)) ≤ (39364077919/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67217/524288 : ℝ)) (492050973987/500000000000 : ℝ) (39364077919/40000000000 : ℝ) (177604493163/1000000000000 : ℝ) (177604493169/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67217/524288 : ℝ)) (492050973987/500000000000 : ℝ) (39364077919/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492050973987/500000000000 : ℝ) (39364077919/40000000000 : ℝ) (992050973987/1000000000000 : ℝ) (248012743497/250000000000 : ℝ) (496009563409/500000000000 : ℝ) (49600956341/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 1 (992050973987/1000000000000 : ℝ) (248012743497/250000000000 : ℝ) (496009563409/500000000000 : ℝ) (49600956341/50000000000 : ℝ) (496017525201/500000000000 : ℝ) (248008762601/250000000000 : ℝ) (496017525137/500000000000 : ℝ) (992035050277/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 2 (496017525201/500000000000 : ℝ) (248008762601/250000000000 : ℝ) (496017525137/500000000000 : ℝ) (992035050277/1000000000000 : ℝ) (496017525169/500000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 3 (496017525169/500000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 4 (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 5 (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 6 (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67217/524288 : ℝ)) 7 (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67217/524288 : ℝ))) (177604493163/1000000000000 : ℝ) (177604493169/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177604493163/1000000000000 : ℝ) (177604493169/1000000000000 : ℝ) (588802246581/1000000000000 : ℝ) (117760449317/200000000000 : ℝ) (210715740491/500000000000 : ℝ) (42143148099/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 1 (588802246581/1000000000000 : ℝ) (117760449317/200000000000 : ℝ) (210715740491/500000000000 : ℝ) (42143148099/100000000000 : ℝ) (505116863781/1000000000000 : ℝ) (126279215947/250000000000 : ℝ) (249068164757/500000000000 : ℝ) (498136329521/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 2 (505116863781/1000000000000 : ℝ) (126279215947/250000000000 : ℝ) (249068164757/500000000000 : ℝ) (498136329521/1000000000000 : ℝ) (501626596647/1000000000000 : ℝ) (100325319331/200000000000 : ℝ) (501614454037/1000000000000 : ℝ) (100322890809/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 3 (501626596647/1000000000000 : ℝ) (100325319331/200000000000 : ℝ) (501614454037/1000000000000 : ℝ) (100322890809/200000000000 : ℝ) (250810262671/500000000000 : ℝ) (10032410507/20000000000 : ℝ) (100324105061/200000000000 : ℝ) (250810262657/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 4 (250810262671/500000000000 : ℝ) (10032410507/20000000000 : ℝ) (100324105061/200000000000 : ℝ) (250810262657/500000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 5 (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 6 (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67217/524288 : ℝ))) 7 (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67217/524288 : ℝ)) hmem 8 (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67217/524288 : ℝ))) hcmem 8 (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67217/524288 : ℝ)) (992035050337/1000000000000 : ℝ) (992035050341/1000000000000 : ℝ) (501620525323/1000000000000 : ℝ) (125405131333/250000000000 : ℝ) (794269999181/1000000000000 : ℝ) (794269999199/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1144_exp_lower
  have heNumeric : (2054903128917/1000000000000 : ℝ)/4 ≤ Real.exp (-5328525227967/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903128917/1000000000000 : ℝ)/4 ≤ Real.exp ((4201/32768 : ℝ)-(794269999199/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4201/32768 : ℝ) (67217/524288 : ℝ) (794269999199/1000000000000 : ℝ) (2054903128917/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1145; no trusted numerical premise.
theorem cover8_leaf1145_exp_radius : (997998752664867621/1000000000000000000 : ℝ) ≤ Real.exp ((-33609/2097152 : ℝ)/8) ∧ Real.exp ((-33609/2097152 : ℝ)/8) ≤ (498999376332433811/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33609/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1145_exp_lower : (184022707541471663/200000000000000000 : ℝ) ≤ Real.exp ((-85256402946079/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256402946079/128000000000000 : ℝ)/8) ≤ (230028384426839579/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256402946079/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1145_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903140177/1000000000000 : ℝ) ≤ 4*Real.exp (67217/524288 : ℝ)*Real.exp (-mu (radius 8 (33609/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903140177/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33609/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1145_exp_radius
  have hrNumeric : (492050856673/500000000000 : ℝ) ≤ Real.exp (-33609/2097152 : ℝ) ∧ Real.exp (-33609/2097152 : ℝ) ≤ (984101713347/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492050856673/500000000000 : ℝ) ≤ (radius 8 (33609/262144 : ℝ)) ∧ (radius 8 (33609/262144 : ℝ)) ≤ (984101713347/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33609/262144 : ℝ)) (492050856673/500000000000 : ℝ) (984101713347/1000000000000 : ℝ) (88802896613/500000000000 : ℝ) (11100362077/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33609/262144 : ℝ)) (492050856673/500000000000 : ℝ) (984101713347/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492050856673/500000000000 : ℝ) (984101713347/1000000000000 : ℝ) (992050856673/1000000000000 : ℝ) (496025428337/500000000000 : ℝ) (12400237607/12500000000 : ℝ) (496009504281/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 1 (992050856673/1000000000000 : ℝ) (496025428337/500000000000 : ℝ) (12400237607/12500000000 : ℝ) (496009504281/500000000000 : ℝ) (124004366577/125000000000 : ℝ) (496017466309/500000000000 : ℝ) (124004366561/125000000000 : ℝ) (992034932491/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 2 (124004366577/125000000000 : ℝ) (496017466309/500000000000 : ℝ) (124004366561/125000000000 : ℝ) (992034932491/1000000000000 : ℝ) (124004366569/125000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 3 (124004366569/125000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 4 (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 5 (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 6 (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33609/262144 : ℝ)) 7 (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33609/262144 : ℝ))) (88802896613/500000000000 : ℝ) (11100362077/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88802896613/500000000000 : ℝ) (11100362077/62500000000 : ℝ) (588802896613/1000000000000 : ℝ) (73600362077/125000000000 : ℝ) (52679127927/125000000000 : ℝ) (6584890991/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 1 (588802896613/1000000000000 : ℝ) (73600362077/125000000000 : ℝ) (52679127927/125000000000 : ℝ) (6584890991/15625000000 : ℝ) (252558980007/500000000000 : ℝ) (25255898001/50000000000 : ℝ) (498137516069/1000000000000 : ℝ) (124534379019/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 2 (252558980007/500000000000 : ℝ) (25255898001/50000000000 : ℝ) (498137516069/1000000000000 : ℝ) (124534379019/250000000000 : ℝ) (501627738041/1000000000000 : ℝ) (7837933407/15625000000 : ℝ) (501615595773/1000000000000 : ℝ) (501615595781/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 3 (501627738041/1000000000000 : ℝ) (7837933407/15625000000 : ℝ) (501615595773/1000000000000 : ℝ) (501615595781/1000000000000 : ℝ) (501621666907/1000000000000 : ℝ) (100324333383/200000000000 : ℝ) (50162166687/100000000000 : ℝ) (250810833439/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 4 (501621666907/1000000000000 : ℝ) (100324333383/200000000000 : ℝ) (50162166687/100000000000 : ℝ) (250810833439/500000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 5 (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 6 (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33609/262144 : ℝ))) 7 (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33609/262144 : ℝ)) hmem 8 (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33609/262144 : ℝ))) hcmem 8 (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33609/262144 : ℝ)) (992034932551/1000000000000 : ℝ) (198406986511/200000000000 : ℝ) (62702708361/125000000000 : ℝ) (501621666897/1000000000000 : ℝ) (794271901049/1000000000000 : ℝ) (198567975267/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1145_exp_lower
  have heNumeric : (2054903140177/1000000000000 : ℝ)/4 ≤ Real.exp (-85256402946079/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903140177/1000000000000 : ℝ)/4 ≤ Real.exp ((67217/524288 : ℝ)-(198567975267/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67217/524288 : ℝ) (33609/262144 : ℝ) (198567975267/250000000000 : ℝ) (2054903140177/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1146; no trusted numerical premise.
theorem cover8_leaf1146_exp_radius : (199599744584437499/200000000000000000 : ℝ) ≤ Real.exp ((-67219/4194304 : ℝ)/8) ∧ Real.exp ((-67219/4194304 : ℝ)/8) ≤ (124749840365273437/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67219/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1146_exp_lower : (920113538340124169/1000000000000000000 : ℝ) ≤ Real.exp ((-8525640224187/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525640224187/12800000000000 : ℝ)/8) ≤ (92011353834012417/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525640224187/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1146_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451575741/500000000000 : ℝ) ≤ 4*Real.exp (33609/262144 : ℝ)*Real.exp (-mu (radius 8 (67219/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451575741/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67219/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1146_exp_radius
  have hrNumeric : (492050739359/500000000000 : ℝ) ≤ Real.exp (-67219/4194304 : ℝ) ∧ Real.exp (-67219/4194304 : ℝ) ≤ (984101478719/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492050739359/500000000000 : ℝ) ≤ (radius 8 (67219/524288 : ℝ)) ∧ (radius 8 (67219/524288 : ℝ)) ≤ (984101478719/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67219/524288 : ℝ)) (492050739359/500000000000 : ℝ) (984101478719/1000000000000 : ℝ) (177607093279/1000000000000 : ℝ) (35521418657/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67219/524288 : ℝ)) (492050739359/500000000000 : ℝ) (984101478719/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492050739359/500000000000 : ℝ) (984101478719/1000000000000 : ℝ) (992050739359/1000000000000 : ℝ) (6200317121/6250000000 : ℝ) (992018890303/1000000000000 : ℝ) (15500295161/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 1 (992050739359/1000000000000 : ℝ) (6200317121/6250000000 : ℝ) (992018890303/1000000000000 : ℝ) (15500295161/15625000000 : ℝ) (992034814831/1000000000000 : ℝ) (62002175927/62500000000 : ℝ) (992034814703/1000000000000 : ℝ) (198406962941/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 2 (992034814831/1000000000000 : ℝ) (62002175927/62500000000 : ℝ) (992034814703/1000000000000 : ℝ) (198406962941/200000000000 : ℝ) (992034814767/1000000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 3 (992034814767/1000000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 4 (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 5 (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 6 (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67219/524288 : ℝ)) 7 (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67219/524288 : ℝ))) (177607093279/1000000000000 : ℝ) (35521418657/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177607093279/1000000000000 : ℝ) (35521418657/200000000000 : ℝ) (588803546639/1000000000000 : ℝ) (588803546643/1000000000000 : ℝ) (421434565833/1000000000000 : ℝ) (421434565841/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 1 (588803546639/1000000000000 : ℝ) (588803546643/1000000000000 : ℝ) (421434565833/1000000000000 : ℝ) (421434565841/1000000000000 : ℝ) (126279764059/250000000000 : ℝ) (252559528121/500000000000 : ℝ) (49813870261/100000000000 : ℝ) (249069351309/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 2 (126279764059/250000000000 : ℝ) (252559528121/500000000000 : ℝ) (49813870261/100000000000 : ℝ) (249069351309/500000000000 : ℝ) (501628879423/1000000000000 : ℝ) (50162887943/100000000000 : ℝ) (62702092187/125000000000 : ℝ) (15675523047/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 3 (501628879423/1000000000000 : ℝ) (50162887943/100000000000 : ℝ) (62702092187/125000000000 : ℝ) (15675523047/31250000000 : ℝ) (501622808459/1000000000000 : ℝ) (501622808467/1000000000000 : ℝ) (250811404211/500000000000 : ℝ) (501622808431/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 4 (501622808459/1000000000000 : ℝ) (501622808467/1000000000000 : ℝ) (250811404211/500000000000 : ℝ) (501622808431/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 5 (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 6 (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67219/524288 : ℝ))) 7 (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67219/524288 : ℝ)) hmem 8 (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67219/524288 : ℝ))) hcmem 8 (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67219/524288 : ℝ)) (496017407383/500000000000 : ℝ) (992034814769/1000000000000 : ℝ) (12540570211/25000000000 : ℝ) (501622808449/1000000000000 : ℝ) (397136901449/500000000000 : ℝ) (158854760583/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1146_exp_lower
  have heNumeric : (1027451575741/500000000000 : ℝ)/4 ≤ Real.exp (-8525640224187/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451575741/500000000000 : ℝ)/4 ≤ Real.exp ((33609/262144 : ℝ)-(158854760583/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33609/262144 : ℝ) (67219/524288 : ℝ) (158854760583/200000000000 : ℝ) (1027451575741/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1147; no trusted numerical premise.
theorem cover8_leaf1147_exp_radius : (199599738635901651/200000000000000000 : ℝ) ≤ Real.exp ((-16805/1048576 : ℝ)/8) ∧ Real.exp ((-16805/1048576 : ℝ)/8) ≤ (31187459161859633/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16805/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1147_exp_lower : (184022707794969053/200000000000000000 : ℝ) ≤ Real.exp ((-17051280307097/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051280307097/25600000000000 : ℝ)/8) ≤ (460056769487422633/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051280307097/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1147_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451581411/500000000000 : ℝ) ≤ 4*Real.exp (67219/524288 : ℝ)*Real.exp (-mu (radius 8 (16805/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451581411/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16805/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1147_exp_radius
  have hrNumeric : (98410124409/100000000000 : ℝ) ≤ Real.exp (-16805/1048576 : ℝ) ∧ Real.exp (-16805/1048576 : ℝ) ≤ (984101244091/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98410124409/100000000000 : ℝ) ≤ (radius 8 (16805/131072 : ℝ)) ∧ (radius 8 (16805/131072 : ℝ)) ≤ (984101244091/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16805/131072 : ℝ)) (98410124409/100000000000 : ℝ) (984101244091/1000000000000 : ℝ) (88804196661/500000000000 : ℝ) (11100524583/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16805/131072 : ℝ)) (98410124409/100000000000 : ℝ) (984101244091/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98410124409/100000000000 : ℝ) (984101244091/1000000000000 : ℝ) (198410124409/200000000000 : ℝ) (496025311023/500000000000 : ℝ) (198403754409/200000000000 : ℝ) (496009386023/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 1 (198410124409/200000000000 : ℝ) (496025311023/500000000000 : ℝ) (198403754409/200000000000 : ℝ) (496009386023/500000000000 : ℝ) (198406939409/200000000000 : ℝ) (496017348523/500000000000 : ℝ) (992034696917/1000000000000 : ℝ) (992034696919/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 2 (198406939409/200000000000 : ℝ) (496017348523/500000000000 : ℝ) (992034696917/1000000000000 : ℝ) (992034696919/1000000000000 : ℝ) (992034696981/1000000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 3 (992034696981/1000000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 4 (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 5 (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 6 (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16805/131072 : ℝ)) 7 (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16805/131072 : ℝ))) (88804196661/500000000000 : ℝ) (11100524583/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88804196661/500000000000 : ℝ) (11100524583/62500000000 : ℝ) (588804196661/1000000000000 : ℝ) (73600524583/125000000000 : ℝ) (52679513529/125000000000 : ℝ) (5267951353/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 1 (588804196661/1000000000000 : ℝ) (73600524583/125000000000 : ℝ) (52679513529/125000000000 : ℝ) (5267951353/12500000000 : ℝ) (252560076223/500000000000 : ℝ) (126280038113/250000000000 : ℝ) (498139889139/1000000000000 : ℝ) (249069944573/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 2 (252560076223/500000000000 : ℝ) (126280038113/250000000000 : ℝ) (498139889139/1000000000000 : ℝ) (249069944573/500000000000 : ℝ) (62703752599/125000000000 : ℝ) (501630020799/1000000000000 : ℝ) (62702234901/125000000000 : ℝ) (100323575843/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 3 (62703752599/125000000000 : ℝ) (501630020799/1000000000000 : ℝ) (62702234901/125000000000 : ℝ) (100323575843/200000000000 : ℝ) (10032479/20000000 : ℝ) (501623950007/1000000000000 : ℝ) (501623949963/1000000000000 : ℝ) (501623949971/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 4 (10032479/20000000 : ℝ) (501623950007/1000000000000 : ℝ) (501623949963/1000000000000 : ℝ) (501623949971/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 5 (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 6 (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16805/131072 : ℝ))) 7 (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16805/131072 : ℝ)) hmem 8 (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16805/131072 : ℝ))) hcmem 8 (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16805/131072 : ℝ)) (49601734849/50000000000 : ℝ) (992034696983/1000000000000 : ℝ) (501623949981/1000000000000 : ℝ) (501623949989/1000000000000 : ℝ) (794275704729/1000000000000 : ℝ) (158855140949/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1147_exp_lower
  have heNumeric : (1027451581411/500000000000 : ℝ)/4 ≤ Real.exp (-17051280307097/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451581411/500000000000 : ℝ)/4 ≤ Real.exp ((67219/524288 : ℝ)-(158855140949/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67219/524288 : ℝ) (16805/131072 : ℝ) (158855140949/200000000000 : ℝ) (1027451581411/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1148; no trusted numerical premise.
theorem cover8_leaf1148_exp_radius : (498999331718414951/500000000000000000 : ℝ) ≤ Real.exp ((-67221/4194304 : ℝ)/8) ∧ Real.exp ((-67221/4194304 : ℝ)/8) ≤ (997998663436829903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67221/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1148_exp_lower : (460056769805760801/500000000000000000 : ℝ) ≤ Real.exp ((-21314100206731/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314100206731/32000000000000 : ℝ)/8) ≤ (920113539611521603/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314100206731/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1148_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903174197/1000000000000 : ℝ) ≤ 4*Real.exp (16805/131072 : ℝ)*Real.exp (-mu (radius 8 (67221/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903174197/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67221/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1148_exp_radius
  have hrNumeric : (492050504731/500000000000 : ℝ) ≤ Real.exp (-67221/4194304 : ℝ) ∧ Real.exp (-67221/4194304 : ℝ) ≤ (984101009463/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492050504731/500000000000 : ℝ) ≤ (radius 8 (67221/524288 : ℝ)) ∧ (radius 8 (67221/524288 : ℝ)) ≤ (984101009463/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67221/524288 : ℝ)) (492050504731/500000000000 : ℝ) (984101009463/1000000000000 : ℝ) (35521938671/200000000000 : ℝ) (88804846681/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67221/524288 : ℝ)) (492050504731/500000000000 : ℝ) (984101009463/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492050504731/500000000000 : ℝ) (984101009463/1000000000000 : ℝ) (992050504731/1000000000000 : ℝ) (248012626183/250000000000 : ℝ) (992018653787/1000000000000 : ℝ) (248004663447/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 1 (992050504731/1000000000000 : ℝ) (248012626183/250000000000 : ℝ) (992018653787/1000000000000 : ℝ) (248004663447/250000000000 : ℝ) (992034579259/1000000000000 : ℝ) (49601728963/50000000000 : ℝ) (992034579131/1000000000000 : ℝ) (992034579133/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 2 (992034579259/1000000000000 : ℝ) (49601728963/50000000000 : ℝ) (992034579131/1000000000000 : ℝ) (992034579133/1000000000000 : ℝ) (198406915839/200000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 3 (198406915839/200000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 4 (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 5 (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 6 (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67221/524288 : ℝ)) 7 (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67221/524288 : ℝ))) (35521938671/200000000000 : ℝ) (88804846681/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35521938671/200000000000 : ℝ) (88804846681/500000000000 : ℝ) (588804846677/1000000000000 : ℝ) (588804846681/1000000000000 : ℝ) (421437650613/1000000000000 : ℝ) (421437650623/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 1 (588804846677/1000000000000 : ℝ) (588804846681/1000000000000 : ℝ) (421437650613/1000000000000 : ℝ) (421437650623/1000000000000 : ℝ) (101024249729/200000000000 : ℝ) (126280312163/250000000000 : ℝ) (498141075653/1000000000000 : ℝ) (498141075661/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 2 (101024249729/200000000000 : ℝ) (126280312163/250000000000 : ℝ) (498141075653/1000000000000 : ℝ) (498141075661/1000000000000 : ℝ) (501631162149/1000000000000 : ℝ) (501631162157/1000000000000 : ℝ) (250809510453/500000000000 : ℝ) (100323804183/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 3 (501631162149/1000000000000 : ℝ) (501631162157/1000000000000 : ℝ) (250809510453/500000000000 : ℝ) (100323804183/200000000000 : ℝ) (501625091527/1000000000000 : ℝ) (31351568221/62500000000 : ℝ) (50162509149/100000000000 : ℝ) (1003250183/2000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 4 (501625091527/1000000000000 : ℝ) (31351568221/62500000000 : ℝ) (50162509149/100000000000 : ℝ) (1003250183/2000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 5 (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 6 (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67221/524288 : ℝ))) 7 (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67221/524288 : ℝ)) hmem 8 (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67221/524288 : ℝ))) hcmem 8 (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67221/524288 : ℝ)) (496017289597/500000000000 : ℝ) (992034579197/1000000000000 : ℝ) (125406272877/250000000000 : ℝ) (250812545759/500000000000 : ℝ) (794277606539/1000000000000 : ℝ) (397138803279/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1148_exp_lower
  have heNumeric : (2054903174197/1000000000000 : ℝ)/4 ≤ Real.exp (-21314100206731/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903174197/1000000000000 : ℝ)/4 ≤ Real.exp ((16805/131072 : ℝ)-(397138803279/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16805/131072 : ℝ) (67221/524288 : ℝ) (397138803279/500000000000 : ℝ) (2054903174197/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1149; no trusted numerical premise.
theorem cover8_leaf1149_exp_radius : (199599726738830487/200000000000000000 : ℝ) ≤ Real.exp ((-33611/2097152 : ℝ)/8) ∧ Real.exp ((-33611/2097152 : ℝ)/8) ≤ (249499658423538109/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33611/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1149_exp_lower : (57507096265656139/62500000000000000 : ℝ) ≤ Real.exp ((-85256400115803/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256400115803/128000000000000 : ℝ)/8) ≤ (36804541610019929/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256400115803/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1149_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451592807/500000000000 : ℝ) ≤ 4*Real.exp (67221/524288 : ℝ)*Real.exp (-mu (radius 8 (33611/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451592807/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33611/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1149_exp_radius
  have hrNumeric : (492050387417/500000000000 : ℝ) ≤ Real.exp (-33611/2097152 : ℝ) ∧ Real.exp (-33611/2097152 : ℝ) ≤ (196820154967/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492050387417/500000000000 : ℝ) ≤ (radius 8 (33611/262144 : ℝ)) ∧ (radius 8 (33611/262144 : ℝ)) ≤ (196820154967/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33611/262144 : ℝ)) (492050387417/500000000000 : ℝ) (196820154967/200000000000 : ℝ) (177610993379/1000000000000 : ℝ) (35522198677/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33611/262144 : ℝ)) (492050387417/500000000000 : ℝ) (196820154967/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492050387417/500000000000 : ℝ) (196820154967/200000000000 : ℝ) (992050387417/1000000000000 : ℝ) (496025193709/500000000000 : ℝ) (992018535529/1000000000000 : ℝ) (99201853553/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 1 (992050387417/1000000000000 : ℝ) (496025193709/500000000000 : ℝ) (992018535529/1000000000000 : ℝ) (99201853553/100000000000 : ℝ) (992034461473/1000000000000 : ℝ) (496017230737/500000000000 : ℝ) (198406892269/200000000000 : ℝ) (992034461347/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 2 (992034461473/1000000000000 : ℝ) (496017230737/500000000000 : ℝ) (198406892269/200000000000 : ℝ) (992034461347/1000000000000 : ℝ) (992034461409/1000000000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 3 (992034461409/1000000000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 4 (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 5 (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 6 (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33611/262144 : ℝ)) 7 (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33611/262144 : ℝ))) (177610993379/1000000000000 : ℝ) (35522198677/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177610993379/1000000000000 : ℝ) (35522198677/200000000000 : ℝ) (588805496689/1000000000000 : ℝ) (588805496693/1000000000000 : ℝ) (421439192979/1000000000000 : ℝ) (421439192987/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 1 (588805496689/1000000000000 : ℝ) (588805496693/1000000000000 : ℝ) (421439192979/1000000000000 : ℝ) (421439192987/1000000000000 : ℝ) (252561172417/500000000000 : ℝ) (12628058621/25000000000 : ℝ) (124535565539/250000000000 : ℝ) (498142262163/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 2 (252561172417/500000000000 : ℝ) (12628058621/25000000000 : ℝ) (124535565539/250000000000 : ℝ) (498142262163/1000000000000 : ℝ) (100326460699/200000000000 : ℝ) (250816151751/500000000000 : ℝ) (250810081297/500000000000 : ℝ) (501620162601/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 3 (100326460699/200000000000 : ℝ) (250816151751/500000000000 : ℝ) (250810081297/500000000000 : ℝ) (501620162601/1000000000000 : ℝ) (125406558261/250000000000 : ℝ) (125406558263/250000000000 : ℝ) (501626233007/1000000000000 : ℝ) (100325246603/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 4 (125406558261/250000000000 : ℝ) (125406558263/250000000000 : ℝ) (501626233007/1000000000000 : ℝ) (100325246603/200000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 5 (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 6 (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33611/262144 : ℝ))) 7 (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33611/262144 : ℝ)) hmem 8 (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33611/262144 : ℝ))) hcmem 8 (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33611/262144 : ℝ)) (31001076919/31250000000 : ℝ) (992034461411/1000000000000 : ℝ) (20065049321/40000000000 : ℝ) (250813116517/500000000000 : ℝ) (794279508333/1000000000000 : ℝ) (794279508351/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1149_exp_lower
  have heNumeric : (1027451592807/500000000000 : ℝ)/4 ≤ Real.exp (-85256400115803/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451592807/500000000000 : ℝ)/4 ≤ Real.exp ((67221/524288 : ℝ)-(794279508351/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67221/524288 : ℝ) (33611/262144 : ℝ) (794279508351/1000000000000 : ℝ) (1027451592807/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1125_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1125_certificate
#check SmaleRate.Proofs.cover8_leaf1126_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1126_certificate
#check SmaleRate.Proofs.cover8_leaf1127_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1127_certificate
#check SmaleRate.Proofs.cover8_leaf1128_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1128_certificate
#check SmaleRate.Proofs.cover8_leaf1129_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1129_certificate
#check SmaleRate.Proofs.cover8_leaf1130_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1130_certificate
#check SmaleRate.Proofs.cover8_leaf1131_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1131_certificate
#check SmaleRate.Proofs.cover8_leaf1132_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1132_certificate
#check SmaleRate.Proofs.cover8_leaf1133_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1133_certificate
#check SmaleRate.Proofs.cover8_leaf1134_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1134_certificate
#check SmaleRate.Proofs.cover8_leaf1135_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1135_certificate
#check SmaleRate.Proofs.cover8_leaf1136_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1136_certificate
#check SmaleRate.Proofs.cover8_leaf1137_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1137_certificate
#check SmaleRate.Proofs.cover8_leaf1138_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1138_certificate
#check SmaleRate.Proofs.cover8_leaf1139_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1139_certificate
#check SmaleRate.Proofs.cover8_leaf1140_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1140_certificate
#check SmaleRate.Proofs.cover8_leaf1141_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1141_certificate
#check SmaleRate.Proofs.cover8_leaf1142_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1142_certificate
#check SmaleRate.Proofs.cover8_leaf1143_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1143_certificate
#check SmaleRate.Proofs.cover8_leaf1144_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1144_certificate
#check SmaleRate.Proofs.cover8_leaf1145_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1145_certificate
#check SmaleRate.Proofs.cover8_leaf1146_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1146_certificate
#check SmaleRate.Proofs.cover8_leaf1147_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1147_certificate
#check SmaleRate.Proofs.cover8_leaf1148_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1148_certificate
#check SmaleRate.Proofs.cover8_leaf1149_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1149_certificate
