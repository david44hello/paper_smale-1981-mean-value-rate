/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0475; no trusted numerical premise.
theorem cover8_leaf0475_exp_radius : (499009875609129133/500000000000000000 : ℝ) ≤ Real.exp ((-4157/262144 : ℝ)/8) ∧ Real.exp ((-4157/262144 : ℝ)/8) ≤ (998019751218258267/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4157/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0475_exp_lower : (11501417824652271/12500000000000000 : ℝ) ≤ Real.exp ((-1705130545937/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705130545937/2560000000000 : ℝ)/8) ≤ (920113425972181681/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705130545937/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0475_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901143859/1000000000000 : ℝ) ≤ 4*Real.exp (33255/262144 : ℝ)*Real.exp (-mu (radius 8 (4157/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901143859/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4157/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0475_exp_radius
  have hrNumeric : (984267374749/1000000000000 : ℝ) ≤ Real.exp (-4157/262144 : ℝ) ∧ Real.exp (-4157/262144 : ℝ) ≤ (3937069499/4000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984267374749/1000000000000 : ℝ) ≤ (radius 8 (4157/32768 : ℝ)) ∧ (radius 8 (4157/32768 : ℝ)) ≤ (3937069499/4000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4157/32768 : ℝ)) (984267374749/1000000000000 : ℝ) (3937069499/4000000000 : ℝ) (35337082507/200000000000 : ℝ) (176685412541/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4157/32768 : ℝ)) (984267374749/1000000000000 : ℝ) (3937069499/4000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984267374749/1000000000000 : ℝ) (3937069499/4000000000 : ℝ) (496066843687/500000000000 : ℝ) (7937069499/8000000000 : ℝ) (496051251069/500000000000 : ℝ) (992102502139/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 1 (496066843687/500000000000 : ℝ) (7937069499/8000000000 : ℝ) (496051251069/500000000000 : ℝ) (992102502139/1000000000000 : ℝ) (248029523689/250000000000 : ℝ) (992118094757/1000000000000 : ℝ) (992118094633/1000000000000 : ℝ) (198423618927/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 2 (248029523689/250000000000 : ℝ) (992118094757/1000000000000 : ℝ) (992118094633/1000000000000 : ℝ) (198423618927/200000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 3 (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 4 (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 5 (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 6 (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4157/32768 : ℝ)) 7 (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4157/32768 : ℝ))) (35337082507/200000000000 : ℝ) (176685412541/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35337082507/200000000000 : ℝ) (176685412541/1000000000000 : ℝ) (588342706267/1000000000000 : ℝ) (588342706271/1000000000000 : ℝ) (840679279/2000000000 : ℝ) (105084909877/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 1 (588342706267/1000000000000 : ℝ) (588342706271/1000000000000 : ℝ) (840679279/2000000000 : ℝ) (105084909877/250000000000 : ℝ) (504341172883/1000000000000 : ℝ) (50434117289/100000000000 : ℝ) (248648225941/500000000000 : ℝ) (497296451889/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 2 (504341172883/1000000000000 : ℝ) (50434117289/100000000000 : ℝ) (248648225941/500000000000 : ℝ) (497296451889/1000000000000 : ℝ) (250409406191/500000000000 : ℝ) (50081881239/100000000000 : ℝ) (50080642549/100000000000 : ℝ) (250403212749/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 3 (250409406191/500000000000 : ℝ) (50081881239/100000000000 : ℝ) (50080642549/100000000000 : ℝ) (250403212749/500000000000 : ℝ) (62601577367/125000000000 : ℝ) (7825197171/15625000000 : ℝ) (500812618897/1000000000000 : ℝ) (250406309453/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 4 (62601577367/125000000000 : ℝ) (7825197171/15625000000 : ℝ) (500812618897/1000000000000 : ℝ) (250406309453/500000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 5 (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 6 (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4157/32768 : ℝ))) 7 (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4157/32768 : ℝ)) hmem 8 (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4157/32768 : ℝ))) hcmem 8 (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4157/32768 : ℝ)) (496059047347/500000000000 : ℝ) (124014761837/125000000000 : ℝ) (125203154729/250000000000 : ℝ) (20032504757/40000000000 : ℝ) (396462188529/500000000000 : ℝ) (31716975083/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0475_exp_lower
  have heNumeric : (2054901143859/1000000000000 : ℝ)/4 ≤ Real.exp (-1705130545937/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901143859/1000000000000 : ℝ)/4 ≤ Real.exp ((33255/262144 : ℝ)-(31716975083/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33255/262144 : ℝ) (4157/32768 : ℝ) (31716975083/40000000000 : ℝ) (2054901143859/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0476; no trusted numerical premise.
theorem cover8_leaf0476_exp_radius : (998019691731647289/1000000000000000000 : ℝ) ≤ Real.exp ((-33257/2097152 : ℝ)/8) ∧ Real.exp ((-33257/2097152 : ℝ)/8) ≤ (99801969173164729/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33257/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0476_exp_lower : (460056712047245379/500000000000000000 : ℝ) ≤ Real.exp ((-5328533086659/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328533086659/8000000000000 : ℝ)/8) ≤ (920113424094490759/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328533086659/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0476_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901110311/1000000000000 : ℝ) ≤ 4*Real.exp (4157/32768 : ℝ)*Real.exp (-mu (radius 8 (33257/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901110311/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33257/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0476_exp_radius
  have hrNumeric : (492133452707/500000000000 : ℝ) ≤ Real.exp (-33257/2097152 : ℝ) ∧ Real.exp (-33257/2097152 : ℝ) ≤ (196853381083/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492133452707/500000000000 : ℝ) ≤ (radius 8 (33257/262144 : ℝ)) ∧ (radius 8 (33257/262144 : ℝ)) ≤ (196853381083/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33257/262144 : ℝ)) (492133452707/500000000000 : ℝ) (196853381083/200000000000 : ℝ) (35337605411/200000000000 : ℝ) (88344013531/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33257/262144 : ℝ)) (492133452707/500000000000 : ℝ) (196853381083/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492133452707/500000000000 : ℝ) (196853381083/200000000000 : ℝ) (992133452707/1000000000000 : ℝ) (248033363177/250000000000 : ℝ) (496051132801/500000000000 : ℝ) (248025566401/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 1 (992133452707/1000000000000 : ℝ) (248033363177/250000000000 : ℝ) (496051132801/500000000000 : ℝ) (248025566401/250000000000 : ℝ) (496058929577/500000000000 : ℝ) (248029464789/250000000000 : ℝ) (992117859031/1000000000000 : ℝ) (496058929517/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 2 (496058929577/500000000000 : ℝ) (248029464789/250000000000 : ℝ) (992117859031/1000000000000 : ℝ) (496058929517/500000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 3 (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 4 (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 5 (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 6 (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33257/262144 : ℝ)) 7 (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33257/262144 : ℝ))) (35337605411/200000000000 : ℝ) (88344013531/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35337605411/200000000000 : ℝ) (88344013531/500000000000 : ℝ) (588344013527/1000000000000 : ℝ) (588344013531/1000000000000 : ℝ) (420342749497/1000000000000 : ℝ) (210171374753/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 1 (588344013527/1000000000000 : ℝ) (588344013531/1000000000000 : ℝ) (420342749497/1000000000000 : ℝ) (210171374753/500000000000 : ℝ) (63042922689/125000000000 : ℝ) (504343381519/1000000000000 : ℝ) (124324711013/250000000000 : ℝ) (24864942203/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 2 (63042922689/125000000000 : ℝ) (504343381519/1000000000000 : ℝ) (124324711013/250000000000 : ℝ) (24864942203/50000000000 : ℝ) (250410556391/500000000000 : ℝ) (50082111279/100000000000 : ℝ) (7825136353/15625000000 : ℝ) (2504043633/5000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 3 (250410556391/500000000000 : ℝ) (50082111279/100000000000 : ℝ) (7825136353/15625000000 : ℝ) (2504043633/5000000000 : ℝ) (500814919687/1000000000000 : ℝ) (100162983939/200000000000 : ℝ) (15650466239/31250000000 : ℝ) (500814919657/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 4 (500814919687/1000000000000 : ℝ) (100162983939/200000000000 : ℝ) (15650466239/31250000000 : ℝ) (500814919657/1000000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 5 (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 6 (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33257/262144 : ℝ))) 7 (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33257/262144 : ℝ)) hmem 8 (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33257/262144 : ℝ))) hcmem 8 (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33257/262144 : ℝ)) (248029464773/250000000000 : ℝ) (198423571819/200000000000 : ℝ) (500814919667/1000000000000 : ℝ) (125203729919/250000000000 : ℝ) (9911602601/12500000000 : ℝ) (396464104049/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0476_exp_lower
  have heNumeric : (2054901110311/1000000000000 : ℝ)/4 ≤ Real.exp (-5328533086659/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901110311/1000000000000 : ℝ)/4 ≤ Real.exp ((4157/32768 : ℝ)-(396464104049/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4157/32768 : ℝ) (33257/262144 : ℝ) (396464104049/500000000000 : ℝ) (2054901110311/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0477; no trusted numerical premise.
theorem cover8_leaf0477_exp_radius : (998019632245039857/1000000000000000000 : ℝ) ≤ Real.exp ((-16629/1048576 : ℝ)/8) ∧ Real.exp ((-16629/1048576 : ℝ)/8) ≤ (499009816122519929/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16629/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0477_exp_lower : (230028355556413983/250000000000000000 : ℝ) ≤ Real.exp ((-42628265733191/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628265733191/64000000000000 : ℝ)/8) ≤ (920113422225655933/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628265733191/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0477_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450538461/500000000000 : ℝ) ≤ 4*Real.exp (33257/262144 : ℝ)*Real.exp (-mu (radius 8 (16629/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450538461/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16629/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0477_exp_radius
  have hrNumeric : (984266436079/1000000000000 : ℝ) ≤ Real.exp (-16629/1048576 : ℝ) ∧ Real.exp (-16629/1048576 : ℝ) ≤ (12303330451/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984266436079/1000000000000 : ℝ) ≤ (radius 8 (16629/131072 : ℝ)) ∧ (radius 8 (16629/131072 : ℝ)) ≤ (12303330451/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16629/131072 : ℝ)) (984266436079/1000000000000 : ℝ) (12303330451/12500000000 : ℝ) (35338128307/200000000000 : ℝ) (88345320771/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16629/131072 : ℝ)) (984266436079/1000000000000 : ℝ) (12303330451/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984266436079/1000000000000 : ℝ) (12303330451/12500000000 : ℝ) (992133218039/1000000000000 : ℝ) (24803330451/25000000000 : ℝ) (992102029067/1000000000000 : ℝ) (248025507267/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 1 (992133218039/1000000000000 : ℝ) (24803330451/25000000000 : ℝ) (992102029067/1000000000000 : ℝ) (248025507267/250000000000 : ℝ) (992117623553/1000000000000 : ℝ) (496058811777/500000000000 : ℝ) (99211762343/100000000000 : ℝ) (124014702929/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 2 (992117623553/1000000000000 : ℝ) (496058811777/500000000000 : ℝ) (99211762343/100000000000 : ℝ) (124014702929/125000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 3 (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 4 (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 5 (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 6 (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16629/131072 : ℝ)) 7 (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16629/131072 : ℝ))) (35338128307/200000000000 : ℝ) (88345320771/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35338128307/200000000000 : ℝ) (88345320771/500000000000 : ℝ) (588345320767/1000000000000 : ℝ) (588345320771/1000000000000 : ℝ) (13135808107/31250000000 : ℝ) (420345859433/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 1 (588345320767/1000000000000 : ℝ) (588345320771/1000000000000 : ℝ) (13135808107/31250000000 : ℝ) (420345859433/1000000000000 : ℝ) (100869118019/200000000000 : ℝ) (252172795051/500000000000 : ℝ) (497301236169/1000000000000 : ℝ) (497301236177/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 2 (100869118019/200000000000 : ℝ) (252172795051/500000000000 : ℝ) (497301236169/1000000000000 : ℝ) (497301236177/1000000000000 : ℝ) (125205853283/250000000000 : ℝ) (25041170657/50000000000 : ℝ) (125202756911/250000000000 : ℝ) (500811027653/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 3 (125205853283/250000000000 : ℝ) (25041170657/50000000000 : ℝ) (125202756911/250000000000 : ℝ) (500811027653/1000000000000 : ℝ) (125204305097/250000000000 : ℝ) (500817220397/1000000000000 : ℝ) (500817220349/1000000000000 : ℝ) (500817220359/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 4 (125204305097/250000000000 : ℝ) (500817220397/1000000000000 : ℝ) (500817220349/1000000000000 : ℝ) (500817220359/1000000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 5 (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 6 (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16629/131072 : ℝ))) 7 (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16629/131072 : ℝ)) hmem 8 (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16629/131072 : ℝ))) hcmem 8 (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16629/131072 : ℝ)) (992117623491/1000000000000 : ℝ) (992117623493/1000000000000 : ℝ) (31301076273/62500000000 : ℝ) (250408610189/500000000000 : ℝ) (31717281561/40000000000 : ℝ) (198233009761/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0477_exp_lower
  have heNumeric : (1027450538461/500000000000 : ℝ)/4 ≤ Real.exp (-42628265733191/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450538461/500000000000 : ℝ)/4 ≤ Real.exp ((33257/262144 : ℝ)-(198233009761/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33257/262144 : ℝ) (16629/131072 : ℝ) (198233009761/250000000000 : ℝ) (1027450538461/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0478; no trusted numerical premise.
theorem cover8_leaf0478_exp_radius : (998019572758435971/1000000000000000000 : ℝ) ≤ Real.exp ((-33259/2097152 : ℝ)/8) ∧ Real.exp ((-33259/2097152 : ℝ)/8) ≤ (249504893189608993/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33259/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0478_exp_lower : (460056710182838601/500000000000000000 : ℝ) ≤ Real.exp ((-21314133384091/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314133384091/32000000000000 : ℝ)/8) ≤ (920113420365677203/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314133384091/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0478_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490104369/100000000000 : ℝ) ≤ 4*Real.exp (16629/131072 : ℝ)*Real.exp (-mu (radius 8 (33259/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490104369/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33259/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0478_exp_radius
  have hrNumeric : (123033245843/125000000000 : ℝ) ≤ Real.exp (-33259/2097152 : ℝ) ∧ Real.exp (-33259/2097152 : ℝ) ≤ (196853193349/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123033245843/125000000000 : ℝ) ≤ (radius 8 (33259/262144 : ℝ)) ∧ (radius 8 (33259/262144 : ℝ)) ≤ (196853193349/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33259/262144 : ℝ)) (123033245843/125000000000 : ℝ) (196853193349/200000000000 : ℝ) (22086656997/125000000000 : ℝ) (88346627991/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33259/262144 : ℝ)) (123033245843/125000000000 : ℝ) (196853193349/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123033245843/125000000000 : ℝ) (196853193349/200000000000 : ℝ) (248033245843/250000000000 : ℝ) (992132983373/1000000000000 : ℝ) (992101792531/1000000000000 : ℝ) (248025448133/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 1 (248033245843/250000000000 : ℝ) (992132983373/1000000000000 : ℝ) (992101792531/1000000000000 : ℝ) (248025448133/250000000000 : ℝ) (992117387951/1000000000000 : ℝ) (992117387953/1000000000000 : ℝ) (248029346957/250000000000 : ℝ) (99211738783/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 2 (992117387951/1000000000000 : ℝ) (992117387953/1000000000000 : ℝ) (248029346957/250000000000 : ℝ) (99211738783/100000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 3 (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 4 (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 5 (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 6 (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33259/262144 : ℝ)) 7 (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33259/262144 : ℝ))) (22086656997/125000000000 : ℝ) (88346627991/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22086656997/125000000000 : ℝ) (88346627991/500000000000 : ℝ) (147086656997/250000000000 : ℝ) (588346627991/1000000000000 : ℝ) (420348969281/1000000000000 : ℝ) (420348969289/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 1 (147086656997/250000000000 : ℝ) (588346627991/1000000000000 : ℝ) (420348969281/1000000000000 : ℝ) (420348969289/1000000000000 : ℝ) (252173899317/500000000000 : ℝ) (6304347483/12500000000 : ℝ) (248651814117/500000000000 : ℝ) (497303628241/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 2 (252173899317/500000000000 : ℝ) (6304347483/12500000000 : ℝ) (248651814117/500000000000 : ℝ) (497303628241/1000000000000 : ℝ) (250412856717/500000000000 : ℝ) (500825713441/1000000000000 : ℝ) (500813328649/1000000000000 : ℝ) (31300833041/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 3 (250412856717/500000000000 : ℝ) (500825713441/1000000000000 : ℝ) (500813328649/1000000000000 : ℝ) (31300833041/62500000000 : ℝ) (500819521041/1000000000000 : ℝ) (500819521049/1000000000000 : ℝ) (500819521003/1000000000000 : ℝ) (500819521011/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 4 (500819521041/1000000000000 : ℝ) (500819521049/1000000000000 : ℝ) (500819521003/1000000000000 : ℝ) (500819521011/1000000000000 : ℝ) (250409760511/500000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 5 (250409760511/500000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 6 (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33259/262144 : ℝ))) 7 (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33259/262144 : ℝ)) hmem 8 (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33259/262144 : ℝ))) hcmem 8 (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33259/262144 : ℝ)) (992117387889/1000000000000 : ℝ) (248029346973/250000000000 : ℝ) (500819521021/1000000000000 : ℝ) (50081952103/100000000000 : ℝ) (158587173979/200000000000 : ℝ) (792935869913/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0478_exp_lower
  have heNumeric : (205490104369/100000000000 : ℝ)/4 ≤ Real.exp (-21314133384091/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490104369/100000000000 : ℝ)/4 ≤ Real.exp ((16629/131072 : ℝ)-(792935869913/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16629/131072 : ℝ) (33259/262144 : ℝ) (792935869913/1000000000000 : ℝ) (205490104369/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0479; no trusted numerical premise.
theorem cover8_leaf0479_exp_radius : (998019513271835631/1000000000000000000 : ℝ) ≤ Real.exp ((-8315/524288 : ℝ)/8) ∧ Real.exp ((-8315/524288 : ℝ)/8) ≤ (62376219579489727/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8315/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0479_exp_lower : (460056709257679833/500000000000000000 : ℝ) ≤ Real.exp ((-42628267797797/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628267797797/64000000000000 : ℝ)/8) ≤ (920113418515359667/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628267797797/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0479_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862626329/125000000000 : ℝ) ≤ 4*Real.exp (33259/262144 : ℝ)*Real.exp (-mu (radius 8 (8315/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (256862626329/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8315/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0479_exp_radius
  have hrNumeric : (98426549741/100000000000 : ℝ) ≤ Real.exp (-8315/524288 : ℝ) ∧ Real.exp (-8315/524288 : ℝ) ≤ (984265497411/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98426549741/100000000000 : ℝ) ≤ (radius 8 (8315/65536 : ℝ)) ∧ (radius 8 (8315/65536 : ℝ)) ≤ (984265497411/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8315/65536 : ℝ)) (98426549741/100000000000 : ℝ) (984265497411/1000000000000 : ℝ) (176695870371/1000000000000 : ℝ) (176695870377/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8315/65536 : ℝ)) (98426549741/100000000000 : ℝ) (984265497411/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98426549741/100000000000 : ℝ) (984265497411/1000000000000 : ℝ) (198426549741/200000000000 : ℝ) (496066374353/500000000000 : ℝ) (248025388999/250000000000 : ℝ) (992101555997/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 1 (198426549741/200000000000 : ℝ) (496066374353/500000000000 : ℝ) (248025388999/250000000000 : ℝ) (992101555997/1000000000000 : ℝ) (19842343047/20000000000 : ℝ) (31003661011/31250000000 : ℝ) (992117152227/1000000000000 : ℝ) (992117152229/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 2 (19842343047/20000000000 : ℝ) (31003661011/31250000000 : ℝ) (992117152227/1000000000000 : ℝ) (992117152229/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 3 (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 4 (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 5 (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 6 (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8315/65536 : ℝ)) 7 (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8315/65536 : ℝ))) (176695870371/1000000000000 : ℝ) (176695870377/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176695870371/1000000000000 : ℝ) (176695870377/1000000000000 : ℝ) (117669587037/200000000000 : ℝ) (588347935189/1000000000000 : ℝ) (420352079061/1000000000000 : ℝ) (420352079069/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 1 (117669587037/200000000000 : ℝ) (588347935189/1000000000000 : ℝ) (420352079061/1000000000000 : ℝ) (420352079069/1000000000000 : ℝ) (504350007123/1000000000000 : ℝ) (504350007129/1000000000000 : ℝ) (497306020239/1000000000000 : ℝ) (248653010123/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 2 (504350007123/1000000000000 : ℝ) (504350007129/1000000000000 : ℝ) (497306020239/1000000000000 : ℝ) (248653010123/500000000000 : ℝ) (500828013681/1000000000000 : ℝ) (62603501711/125000000000 : ℝ) (250407814799/500000000000 : ℝ) (100163125921/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 3 (500828013681/1000000000000 : ℝ) (62603501711/125000000000 : ℝ) (250407814799/500000000000 : ℝ) (100163125921/200000000000 : ℝ) (500821821639/1000000000000 : ℝ) (500821821647/1000000000000 : ℝ) (500821821601/1000000000000 : ℝ) (500821821609/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 4 (500821821639/1000000000000 : ℝ) (500821821647/1000000000000 : ℝ) (500821821601/1000000000000 : ℝ) (500821821609/1000000000000 : ℝ) (25041091081/50000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 5 (25041091081/50000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 6 (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8315/65536 : ℝ))) 7 (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8315/65536 : ℝ)) hmem 8 (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8315/65536 : ℝ))) hcmem 8 (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8315/65536 : ℝ)) (31003661009/31250000000 : ℝ) (992117152291/1000000000000 : ℝ) (500821821619/1000000000000 : ℝ) (125205455407/250000000000 : ℝ) (19823492517/25000000000 : ℝ) (396469850349/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0479_exp_lower
  have heNumeric : (256862626329/125000000000 : ℝ)/4 ≤ Real.exp (-42628267797797/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862626329/125000000000 : ℝ)/4 ≤ Real.exp ((33259/262144 : ℝ)-(396469850349/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33259/262144 : ℝ) (8315/65536 : ℝ) (396469850349/500000000000 : ℝ) (256862626329/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0480; no trusted numerical premise.
theorem cover8_leaf0480_exp_radius : (249504863446309709/250000000000000000 : ℝ) ≤ Real.exp ((-33261/2097152 : ℝ)/8) ∧ Real.exp ((-33261/2097152 : ℝ)/8) ≤ (998019453785238837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33261/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0480_exp_lower : (23002835416850331/25000000000000000 : ℝ) ≤ Real.exp ((-2131413441121/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131413441121/3200000000000 : ℝ)/8) ≤ (920113416674013241/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131413441121/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0480_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900977733/1000000000000 : ℝ) ≤ 4*Real.exp (8315/65536 : ℝ)*Real.exp (-mu (radius 8 (33261/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900977733/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33261/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0480_exp_radius
  have hrNumeric : (246066257019/250000000000 : ℝ) ≤ Real.exp (-33261/2097152 : ℝ) ∧ Real.exp (-33261/2097152 : ℝ) ≤ (984265028077/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246066257019/250000000000 : ℝ) ≤ (radius 8 (33261/262144 : ℝ)) ∧ (radius 8 (33261/262144 : ℝ)) ≤ (984265028077/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33261/262144 : ℝ)) (246066257019/250000000000 : ℝ) (984265028077/1000000000000 : ℝ) (88349242363/500000000000 : ℝ) (44174621183/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33261/262144 : ℝ)) (246066257019/250000000000 : ℝ) (984265028077/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246066257019/250000000000 : ℝ) (984265028077/1000000000000 : ℝ) (496066257019/500000000000 : ℝ) (992132514039/1000000000000 : ℝ) (49605065973/50000000000 : ℝ) (496050659731/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 1 (496066257019/500000000000 : ℝ) (992132514039/1000000000000 : ℝ) (49605065973/50000000000 : ℝ) (496050659731/500000000000 : ℝ) (992116916749/1000000000000 : ℝ) (992116916751/1000000000000 : ℝ) (496058458313/500000000000 : ℝ) (248029229157/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 2 (992116916749/1000000000000 : ℝ) (992116916751/1000000000000 : ℝ) (496058458313/500000000000 : ℝ) (248029229157/250000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 3 (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 4 (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 5 (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 6 (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33261/262144 : ℝ)) 7 (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33261/262144 : ℝ))) (88349242363/500000000000 : ℝ) (44174621183/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88349242363/500000000000 : ℝ) (44174621183/250000000000 : ℝ) (588349242363/1000000000000 : ℝ) (294174621183/500000000000 : ℝ) (42035518877/100000000000 : ℝ) (210177594389/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 1 (588349242363/1000000000000 : ℝ) (294174621183/500000000000 : ℝ) (42035518877/100000000000 : ℝ) (210177594389/500000000000 : ℝ) (252176107783/500000000000 : ℝ) (126088053893/250000000000 : ℝ) (497308412191/1000000000000 : ℝ) (248654206099/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 2 (252176107783/500000000000 : ℝ) (126088053893/250000000000 : ℝ) (497308412191/1000000000000 : ℝ) (248654206099/500000000000 : ℝ) (250415156939/500000000000 : ℝ) (100166062777/200000000000 : ℝ) (500817930497/1000000000000 : ℝ) (100163586101/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 3 (250415156939/500000000000 : ℝ) (100166062777/200000000000 : ℝ) (500817930497/1000000000000 : ℝ) (100163586101/200000000000 : ℝ) (500824122187/1000000000000 : ℝ) (100164824439/200000000000 : ℝ) (500824122149/1000000000000 : ℝ) (500824122157/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 4 (500824122187/1000000000000 : ℝ) (100164824439/200000000000 : ℝ) (500824122149/1000000000000 : ℝ) (500824122157/1000000000000 : ℝ) (62603015271/125000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 5 (62603015271/125000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 6 (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33261/262144 : ℝ))) 7 (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33261/262144 : ℝ)) hmem 8 (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33261/262144 : ℝ))) hcmem 8 (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33261/262144 : ℝ)) (992116916687/1000000000000 : ℝ) (99211691669/100000000000 : ℝ) (500824122167/1000000000000 : ℝ) (7825376909/15625000000 : ℝ) (198235882847/250000000000 : ℝ) (158588706281/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0480_exp_lower
  have heNumeric : (2054900977733/1000000000000 : ℝ)/4 ≤ Real.exp (-2131413441121/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900977733/1000000000000 : ℝ)/4 ≤ Real.exp ((8315/65536 : ℝ)-(158588706281/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8315/65536 : ℝ) (33261/262144 : ℝ) (158588706281/200000000000 : ℝ) (2054900977733/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0481; no trusted numerical premise.
theorem cover8_leaf0481_exp_radius : (998019394298645587/1000000000000000000 : ℝ) ≤ Real.exp ((-16631/1048576 : ℝ)/8) ∧ Real.exp ((-16631/1048576 : ℝ)/8) ≤ (249504848574661397/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16631/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0481_exp_lower : (11501417685516161/12500000000000000 : ℝ) ≤ Real.exp ((-42628269842243/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628269842243/64000000000000 : ℝ)/8) ≤ (920113414841292881/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628269842243/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0481_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900944989/1000000000000 : ℝ) ≤ 4*Real.exp (33261/262144 : ℝ)*Real.exp (-mu (radius 8 (16631/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900944989/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16631/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0481_exp_radius
  have hrNumeric : (492132279371/500000000000 : ℝ) ≤ Real.exp (-16631/1048576 : ℝ) ∧ Real.exp (-16631/1048576 : ℝ) ≤ (984264558743/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492132279371/500000000000 : ℝ) ≤ (radius 8 (16631/131072 : ℝ)) ∧ (radius 8 (16631/131072 : ℝ)) ≤ (984264558743/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16631/131072 : ℝ)) (492132279371/500000000000 : ℝ) (984264558743/1000000000000 : ℝ) (176701099041/1000000000000 : ℝ) (176701099047/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16631/131072 : ℝ)) (492132279371/500000000000 : ℝ) (984264558743/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492132279371/500000000000 : ℝ) (984264558743/1000000000000 : ℝ) (992132279371/1000000000000 : ℝ) (248033069843/250000000000 : ℝ) (39684043317/40000000000 : ℝ) (992101082927/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 1 (992132279371/1000000000000 : ℝ) (248033069843/250000000000 : ℝ) (39684043317/40000000000 : ℝ) (992101082927/1000000000000 : ℝ) (248029170287/250000000000 : ℝ) (19842333623/20000000000 : ℝ) (39684667241/40000000000 : ℝ) (992116681027/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 2 (248029170287/250000000000 : ℝ) (19842333623/20000000000 : ℝ) (39684667241/40000000000 : ℝ) (992116681027/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 3 (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 4 (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 5 (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 6 (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16631/131072 : ℝ)) 7 (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16631/131072 : ℝ))) (176701099041/1000000000000 : ℝ) (176701099047/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176701099041/1000000000000 : ℝ) (176701099047/1000000000000 : ℝ) (7354381869/12500000000 : ℝ) (147087637381/250000000000 : ℝ) (52544787301/125000000000 : ℝ) (26272393651/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 1 (7354381869/12500000000 : ℝ) (147087637381/250000000000 : ℝ) (52544787301/125000000000 : ℝ) (26272393651/62500000000 : ℝ) (126088605991/250000000000 : ℝ) (50435442397/100000000000 : ℝ) (62163850511/125000000000 : ℝ) (3885240657/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 2 (126088605991/250000000000 : ℝ) (50435442397/100000000000 : ℝ) (62163850511/125000000000 : ℝ) (3885240657/7812500000 : ℝ) (250416307013/500000000000 : ℝ) (500832614033/1000000000000 : ℝ) (500820231347/1000000000000 : ℝ) (100164046271/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 3 (250416307013/500000000000 : ℝ) (500832614033/1000000000000 : ℝ) (500820231347/1000000000000 : ℝ) (100164046271/200000000000 : ℝ) (250413211343/500000000000 : ℝ) (250413211347/500000000000 : ℝ) (62603302831/125000000000 : ℝ) (3912706427/7812500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 4 (250413211343/500000000000 : ℝ) (250413211347/500000000000 : ℝ) (62603302831/125000000000 : ℝ) (3912706427/7812500000 : ℝ) (500826422667/1000000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 5 (500826422667/1000000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 6 (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16631/131072 : ℝ))) 7 (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16631/131072 : ℝ)) hmem 8 (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16631/131072 : ℝ))) hcmem 8 (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16631/131072 : ℝ)) (496058340543/500000000000 : ℝ) (992116681089/1000000000000 : ℝ) (250413211333/500000000000 : ℝ) (20033056907/40000000000 : ℝ) (39647368101/50000000000 : ℝ) (792947362037/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0481_exp_lower
  have heNumeric : (2054900944989/1000000000000 : ℝ)/4 ≤ Real.exp (-42628269842243/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900944989/1000000000000 : ℝ)/4 ≤ Real.exp ((33261/262144 : ℝ)-(792947362037/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33261/262144 : ℝ) (16631/131072 : ℝ) (792947362037/1000000000000 : ℝ) (2054900944989/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0482; no trusted numerical premise.
theorem cover8_leaf0482_exp_radius : (249504833703013971/250000000000000000 : ℝ) ≤ Real.exp ((-33263/2097152 : ℝ)/8) ∧ Real.exp ((-33263/2097152 : ℝ)/8) ≤ (199603866962411177/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33263/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0482_exp_lower : (460056706508541787/500000000000000000 : ℝ) ≤ Real.exp ((-4262827085733/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262827085733/6400000000000 : ℝ)/8) ≤ (36804536520683343/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262827085733/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0482_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900912397/1000000000000 : ℝ) ≤ 4*Real.exp (16631/131072 : ℝ)*Real.exp (-mu (radius 8 (33263/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900912397/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33263/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0482_exp_radius
  have hrNumeric : (15379126397/15625000000 : ℝ) ≤ Real.exp (-33263/2097152 : ℝ) ∧ Real.exp (-33263/2097152 : ℝ) ≤ (984264089409/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15379126397/15625000000 : ℝ) ≤ (radius 8 (33263/262144 : ℝ)) ∧ (radius 8 (33263/262144 : ℝ)) ≤ (984264089409/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33263/262144 : ℝ)) (15379126397/15625000000 : ℝ) (984264089409/1000000000000 : ℝ) (44175928329/250000000000 : ℝ) (176703713323/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33263/262144 : ℝ)) (15379126397/15625000000 : ℝ) (984264089409/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15379126397/15625000000 : ℝ) (984264089409/1000000000000 : ℝ) (31004126397/31250000000 : ℝ) (198426408941/200000000000 : ℝ) (99210084639/100000000000 : ℝ) (992100846391/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 1 (31004126397/31250000000 : ℝ) (198426408941/200000000000 : ℝ) (99210084639/100000000000 : ℝ) (992100846391/1000000000000 : ℝ) (992116445547/1000000000000 : ℝ) (248029111387/250000000000 : ℝ) (62007277839/62500000000 : ℝ) (496058222713/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 2 (992116445547/1000000000000 : ℝ) (248029111387/250000000000 : ℝ) (62007277839/62500000000 : ℝ) (496058222713/500000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 3 (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 4 (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 5 (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 6 (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33263/262144 : ℝ)) 7 (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33263/262144 : ℝ))) (44175928329/250000000000 : ℝ) (176703713323/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44175928329/250000000000 : ℝ) (176703713323/1000000000000 : ℝ) (294175928329/500000000000 : ℝ) (294175928331/500000000000 : ℝ) (52545175997/125000000000 : ℝ) (84072281597/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 1 (294175928329/500000000000 : ℝ) (294175928331/500000000000 : ℝ) (52545175997/125000000000 : ℝ) (84072281597/200000000000 : ℝ) (504356632317/1000000000000 : ℝ) (126089158081/250000000000 : ℝ) (497313195933/1000000000000 : ℝ) (497313195941/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 2 (504356632317/1000000000000 : ℝ) (126089158081/250000000000 : ℝ) (497313195933/1000000000000 : ℝ) (497313195941/1000000000000 : ℝ) (4006679313/8000000000 : ℝ) (500834914133/1000000000000 : ℝ) (125205633037/250000000000 : ℝ) (125205633039/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 3 (4006679313/8000000000 : ℝ) (500834914133/1000000000000 : ℝ) (125205633037/250000000000 : ℝ) (125205633039/250000000000 : ℝ) (7825448799/15625000000 : ℝ) (100165744629/200000000000 : ℝ) (250414361549/500000000000 : ℝ) (500828723107/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 4 (7825448799/15625000000 : ℝ) (100165744629/200000000000 : ℝ) (250414361549/500000000000 : ℝ) (500828723107/1000000000000 : ℝ) (500828723117/1000000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 5 (500828723117/1000000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 6 (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33263/262144 : ℝ))) 7 (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33263/262144 : ℝ)) hmem 8 (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33263/262144 : ℝ))) hcmem 8 (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33263/262144 : ℝ)) (198423289097/200000000000 : ℝ) (992116445487/1000000000000 : ℝ) (125207180779/250000000000 : ℝ) (250414361563/500000000000 : ℝ) (774366399/976562500 : ℝ) (158590238519/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0482_exp_lower
  have heNumeric : (2054900912397/1000000000000 : ℝ)/4 ≤ Real.exp (-4262827085733/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900912397/1000000000000 : ℝ)/4 ≤ Real.exp ((16631/131072 : ℝ)-(158590238519/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16631/131072 : ℝ) (33263/262144 : ℝ) (158590238519/200000000000 : ℝ) (2054900912397/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0483; no trusted numerical premise.
theorem cover8_leaf0483_exp_radius : (499009637662734863/500000000000000000 : ℝ) ≤ Real.exp ((-2079/131072 : ℝ)/8) ∧ Real.exp ((-2079/131072 : ℝ)/8) ≤ (998019275325469727/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2079/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0483_exp_lower : (920113411201960391/1000000000000000000 : ℝ) ≤ Real.exp ((-42628271867361/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628271867361/64000000000000 : ℝ)/8) ≤ (115014176400245049/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628271867361/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0483_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900879967/1000000000000 : ℝ) ≤ 4*Real.exp (33263/262144 : ℝ)*Real.exp (-mu (radius 8 (2079/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900879967/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2079/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0483_exp_radius
  have hrNumeric : (492131810037/500000000000 : ℝ) ≤ Real.exp (-2079/131072 : ℝ) ∧ Real.exp (-2079/131072 : ℝ) ≤ (39370544803/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492131810037/500000000000 : ℝ) ≤ (radius 8 (2079/16384 : ℝ)) ∧ (radius 8 (2079/16384 : ℝ)) ≤ (39370544803/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2079/16384 : ℝ)) (492131810037/500000000000 : ℝ) (39370544803/40000000000 : ℝ) (176706327551/1000000000000 : ℝ) (88353163779/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2079/16384 : ℝ)) (492131810037/500000000000 : ℝ) (39370544803/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492131810037/500000000000 : ℝ) (39370544803/40000000000 : ℝ) (992131810037/1000000000000 : ℝ) (496065905019/500000000000 : ℝ) (496050304927/500000000000 : ℝ) (15501572029/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 1 (992131810037/1000000000000 : ℝ) (496065905019/500000000000 : ℝ) (496050304927/500000000000 : ℝ) (15501572029/15625000000 : ℝ) (198423241989/200000000000 : ℝ) (992116209947/1000000000000 : ℝ) (496058104911/500000000000 : ℝ) (39684648393/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 2 (198423241989/200000000000 : ℝ) (992116209947/1000000000000 : ℝ) (496058104911/500000000000 : ℝ) (39684648393/40000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 3 (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 4 (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 5 (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 6 (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2079/16384 : ℝ)) 7 (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2079/16384 : ℝ))) (176706327551/1000000000000 : ℝ) (88353163779/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176706327551/1000000000000 : ℝ) (88353163779/500000000000 : ℝ) (23534126551/40000000000 : ℝ) (588353163779/1000000000000 : ℝ) (420364517473/1000000000000 : ℝ) (420364517483/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 1 (23534126551/40000000000 : ℝ) (588353163779/1000000000000 : ℝ) (420364517473/1000000000000 : ℝ) (420364517483/1000000000000 : ℝ) (31522427539/62500000000 : ℝ) (504358840631/1000000000000 : ℝ) (124328896931/250000000000 : ℝ) (497315587733/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 2 (31522427539/62500000000 : ℝ) (504358840631/1000000000000 : ℝ) (124328896931/250000000000 : ℝ) (497315587733/1000000000000 : ℝ) (250418607087/500000000000 : ℝ) (250418607091/500000000000 : ℝ) (500824832899/1000000000000 : ℝ) (125206208227/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 3 (250418607087/500000000000 : ℝ) (250418607091/500000000000 : ℝ) (500824832899/1000000000000 : ℝ) (125206208227/250000000000 : ℝ) (31301938971/62500000000 : ℝ) (100166204709/200000000000 : ℝ) (250415511749/500000000000 : ℝ) (500831023507/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 4 (31301938971/62500000000 : ℝ) (100166204709/200000000000 : ℝ) (250415511749/500000000000 : ℝ) (500831023507/1000000000000 : ℝ) (500831023517/1000000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 5 (500831023517/1000000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 6 (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2079/16384 : ℝ))) 7 (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2079/16384 : ℝ)) hmem 8 (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2079/16384 : ℝ))) hcmem 8 (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2079/16384 : ℝ)) (992116209883/1000000000000 : ℝ) (496058104943/500000000000 : ℝ) (125207755879/250000000000 : ℝ) (250415511763/500000000000 : ℝ) (158591004611/200000000000 : ℝ) (396477511537/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0483_exp_lower
  have heNumeric : (2054900879967/1000000000000 : ℝ)/4 ≤ Real.exp (-42628271867361/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900879967/1000000000000 : ℝ)/4 ≤ Real.exp ((33263/262144 : ℝ)-(396477511537/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33263/262144 : ℝ) (2079/16384 : ℝ) (396477511537/500000000000 : ℝ) (2054900879967/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0484; no trusted numerical premise.
theorem cover8_leaf0484_exp_radius : (499009607919443557/500000000000000000 : ℝ) ≤ Real.exp ((-33265/2097152 : ℝ)/8) ∧ Real.exp ((-33265/2097152 : ℝ)/8) ≤ (199603843167777423/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33265/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0484_exp_lower : (460056704698249201/500000000000000000 : ℝ) ≤ Real.exp ((-2664267054501/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664267054501/4000000000000 : ℝ)/8) ≤ (920113409396498403/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664267054501/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0484_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490084771/100000000000 : ℝ) ≤ 4*Real.exp (2079/16384 : ℝ)*Real.exp (-mu (radius 8 (33265/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490084771/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33265/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0484_exp_radius
  have hrNumeric : (984263150741/1000000000000 : ℝ) ≤ Real.exp (-33265/2097152 : ℝ) ∧ Real.exp (-33265/2097152 : ℝ) ≤ (492131575371/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984263150741/1000000000000 : ℝ) ≤ (radius 8 (33265/262144 : ℝ)) ∧ (radius 8 (33265/262144 : ℝ)) ≤ (492131575371/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33265/262144 : ℝ)) (984263150741/1000000000000 : ℝ) (492131575371/500000000000 : ℝ) (176708941741/1000000000000 : ℝ) (44177235437/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33265/262144 : ℝ)) (984263150741/1000000000000 : ℝ) (492131575371/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984263150741/1000000000000 : ℝ) (492131575371/500000000000 : ℝ) (99213157537/100000000000 : ℝ) (992131575371/1000000000000 : ℝ) (992100373319/1000000000000 : ℝ) (992100373321/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 1 (99213157537/100000000000 : ℝ) (992131575371/1000000000000 : ℝ) (992100373319/1000000000000 : ℝ) (992100373321/1000000000000 : ℝ) (124014496793/125000000000 : ℝ) (496057987173/500000000000 : ℝ) (992115974221/1000000000000 : ℝ) (62007248389/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 2 (124014496793/125000000000 : ℝ) (496057987173/500000000000 : ℝ) (992115974221/1000000000000 : ℝ) (62007248389/62500000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 3 (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 4 (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 5 (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 6 (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33265/262144 : ℝ)) 7 (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33265/262144 : ℝ))) (176708941741/1000000000000 : ℝ) (44177235437/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176708941741/1000000000000 : ℝ) (44177235437/250000000000 : ℝ) (58835447087/100000000000 : ℝ) (294177235437/500000000000 : ℝ) (210183813447/500000000000 : ℝ) (420367626903/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 1 (58835447087/100000000000 : ℝ) (294177235437/500000000000 : ℝ) (210183813447/500000000000 : ℝ) (420367626903/1000000000000 : ℝ) (252180524441/500000000000 : ℝ) (504361048889/1000000000000 : ℝ) (497317979457/1000000000000 : ℝ) (99463595893/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 2 (252180524441/500000000000 : ℝ) (504361048889/1000000000000 : ℝ) (497317979457/1000000000000 : ℝ) (99463595893/200000000000 : ℝ) (500839514169/1000000000000 : ℝ) (500839514177/1000000000000 : ℝ) (125206783399/250000000000 : ℝ) (100165426721/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 3 (500839514169/1000000000000 : ℝ) (500839514177/1000000000000 : ℝ) (125206783399/250000000000 : ℝ) (100165426721/200000000000 : ℝ) (250416661941/500000000000 : ℝ) (500833323891/1000000000000 : ℝ) (125208330961/250000000000 : ℝ) (500833323853/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 4 (250416661941/500000000000 : ℝ) (500833323891/1000000000000 : ℝ) (125208330961/250000000000 : ℝ) (500833323853/1000000000000 : ℝ) (500833323863/1000000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 5 (500833323863/1000000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 6 (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33265/262144 : ℝ))) 7 (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33265/262144 : ℝ)) hmem 8 (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33265/262144 : ℝ))) hcmem 8 (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33265/262144 : ℝ)) (496057987141/500000000000 : ℝ) (198423194857/200000000000 : ℝ) (250416661931/500000000000 : ℝ) (15651041371/31250000000 : ℝ) (15859177069/20000000000 : ℝ) (792958853469/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0484_exp_lower
  have heNumeric : (205490084771/100000000000 : ℝ)/4 ≤ Real.exp (-2664267054501/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490084771/100000000000 : ℝ)/4 ≤ Real.exp ((2079/16384 : ℝ)-(792958853469/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2079/16384 : ℝ) (33265/262144 : ℝ) (792958853469/1000000000000 : ℝ) (205490084771/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0485; no trusted numerical premise.
theorem cover8_leaf0485_exp_radius : (62376197272019253/62500000000000000 : ℝ) ≤ Real.exp ((-16633/1048576 : ℝ)/8) ∧ Real.exp ((-16633/1048576 : ℝ)/8) ≤ (998019156352308049/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16633/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0485_exp_lower : (460056703799888747/500000000000000000 : ℝ) ≤ Real.exp ((-42628273871807/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628273871807/64000000000000 : ℝ)/8) ≤ (184022681519955499/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628273871807/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0485_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862601951/125000000000 : ℝ) ≤ 4*Real.exp (33265/262144 : ℝ)*Real.exp (-mu (radius 8 (16633/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862601951/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16633/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0485_exp_radius
  have hrNumeric : (15379104397/15625000000 : ℝ) ≤ Real.exp (-16633/1048576 : ℝ) ∧ Real.exp (-16633/1048576 : ℝ) ≤ (984262681409/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15379104397/15625000000 : ℝ) ≤ (radius 8 (16633/131072 : ℝ)) ∧ (radius 8 (16633/131072 : ℝ)) ≤ (984262681409/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16633/131072 : ℝ)) (15379104397/15625000000 : ℝ) (984262681409/1000000000000 : ℝ) (176711555891/1000000000000 : ℝ) (176711555897/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16633/131072 : ℝ)) (15379104397/15625000000 : ℝ) (984262681409/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15379104397/15625000000 : ℝ) (984262681409/1000000000000 : ℝ) (31004104397/31250000000 : ℝ) (198426268141/200000000000 : ℝ) (62006258549/62500000000 : ℝ) (496050068393/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 1 (31004104397/31250000000 : ℝ) (198426268141/200000000000 : ℝ) (62006258549/62500000000 : ℝ) (496050068393/500000000000 : ℝ) (124014467343/125000000000 : ℝ) (496057869373/500000000000 : ℝ) (992115738621/1000000000000 : ℝ) (992115738623/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 2 (124014467343/125000000000 : ℝ) (496057869373/500000000000 : ℝ) (992115738621/1000000000000 : ℝ) (992115738623/1000000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 3 (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 4 (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 5 (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 6 (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16633/131072 : ℝ)) 7 (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16633/131072 : ℝ))) (176711555891/1000000000000 : ℝ) (176711555897/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176711555891/1000000000000 : ℝ) (176711555897/1000000000000 : ℝ) (117671155589/200000000000 : ℝ) (588355777949/1000000000000 : ℝ) (105092684061/250000000000 : ℝ) (105092684063/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 1 (117671155589/200000000000 : ℝ) (588355777949/1000000000000 : ℝ) (105092684061/250000000000 : ℝ) (105092684063/250000000000 : ℝ) (252181628547/500000000000 : ℝ) (504363257101/1000000000000 : ℝ) (497320371137/1000000000000 : ℝ) (62165046393/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 2 (252181628547/500000000000 : ℝ) (504363257101/1000000000000 : ℝ) (497320371137/1000000000000 : ℝ) (62165046393/125000000000 : ℝ) (100168362823/200000000000 : ℝ) (500841814123/1000000000000 : ℝ) (125207358561/250000000000 : ℝ) (125207358563/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 3 (100168362823/200000000000 : ℝ) (500841814123/1000000000000 : ℝ) (125207358561/250000000000 : ℝ) (125207358563/250000000000 : ℝ) (500835624179/1000000000000 : ℝ) (125208906047/250000000000 : ℝ) (500835624141/1000000000000 : ℝ) (10016712483/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 4 (500835624179/1000000000000 : ℝ) (125208906047/250000000000 : ℝ) (500835624141/1000000000000 : ℝ) (10016712483/20000000000 : ℝ) (3130222651/6250000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 5 (3130222651/6250000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 6 (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16633/131072 : ℝ))) 7 (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16633/131072 : ℝ)) hmem 8 (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16633/131072 : ℝ))) hcmem 8 (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16633/131072 : ℝ)) (496057869341/500000000000 : ℝ) (198423147737/200000000000 : ℝ) (500835624159/1000000000000 : ℝ) (500835624169/1000000000000 : ℝ) (99120335471/125000000000 : ℝ) (198240670947/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0485_exp_lower
  have heNumeric : (256862601951/125000000000 : ℝ)/4 ≤ Real.exp (-42628273871807/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862601951/125000000000 : ℝ)/4 ≤ Real.exp ((33265/262144 : ℝ)-(198240670947/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33265/262144 : ℝ) (16633/131072 : ℝ) (198240670947/250000000000 : ℝ) (256862601951/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0486; no trusted numerical premise.
theorem cover8_leaf0486_exp_radius : (998019096865732527/1000000000000000000 : ℝ) ≤ Real.exp ((-33267/2097152 : ℝ)/8) ∧ Real.exp ((-33267/2097152 : ℝ)/8) ≤ (62376193554108283/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33267/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0486_exp_lower : (57507087863251731/62500000000000000 : ℝ) ≤ Real.exp ((-21314137433303/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314137433303/32000000000000 : ℝ)/8) ≤ (920113405812027697/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314137433303/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0486_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725195917/250000000000 : ℝ) ≤ 4*Real.exp (16633/131072 : ℝ)*Real.exp (-mu (radius 8 (33267/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725195917/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33267/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0486_exp_radius
  have hrNumeric : (39370488483/40000000000 : ℝ) ≤ Real.exp (-33267/2097152 : ℝ) ∧ Real.exp (-33267/2097152 : ℝ) ≤ (246065553019/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39370488483/40000000000 : ℝ) ≤ (radius 8 (33267/262144 : ℝ)) ∧ (radius 8 (33267/262144 : ℝ)) ≤ (246065553019/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33267/262144 : ℝ)) (39370488483/40000000000 : ℝ) (246065553019/250000000000 : ℝ) (176714170001/1000000000000 : ℝ) (176714170007/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33267/262144 : ℝ)) (39370488483/40000000000 : ℝ) (246065553019/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39370488483/40000000000 : ℝ) (246065553019/250000000000 : ℝ) (992131106037/1000000000000 : ℝ) (496065553019/500000000000 : ℝ) (992099900249/1000000000000 : ℝ) (3968399601/4000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 1 (992131106037/1000000000000 : ℝ) (496065553019/500000000000 : ℝ) (992099900249/1000000000000 : ℝ) (3968399601/4000000000 : ℝ) (992115503143/1000000000000 : ℝ) (124014437893/125000000000 : ℝ) (49605775151/50000000000 : ℝ) (496057751511/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 2 (992115503143/1000000000000 : ℝ) (124014437893/125000000000 : ℝ) (49605775151/50000000000 : ℝ) (496057751511/500000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 3 (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 4 (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 5 (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 6 (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33267/262144 : ℝ)) 7 (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33267/262144 : ℝ))) (176714170001/1000000000000 : ℝ) (176714170007/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176714170001/1000000000000 : ℝ) (176714170007/1000000000000 : ℝ) (117671417/200000000 : ℝ) (147089271251/250000000000 : ℝ) (105093461381/250000000000 : ℝ) (105093461383/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 1 (117671417/200000000 : ℝ) (147089271251/250000000000 : ℝ) (105093461381/250000000000 : ℝ) (105093461383/250000000000 : ℝ) (252182732631/500000000000 : ℝ) (126091366317/250000000000 : ℝ) (497322762763/1000000000000 : ℝ) (49732276277/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 2 (252182732631/500000000000 : ℝ) (126091366317/250000000000 : ℝ) (497322762763/1000000000000 : ℝ) (49732276277/100000000000 : ℝ) (125211028503/250000000000 : ℝ) (500844114019/1000000000000 : ℝ) (500831734843/1000000000000 : ℝ) (10016634697/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 3 (125211028503/250000000000 : ℝ) (500844114019/1000000000000 : ℝ) (500831734843/1000000000000 : ℝ) (10016634697/20000000000 : ℝ) (500837924427/1000000000000 : ℝ) (100167584887/200000000000 : ℝ) (500837924389/1000000000000 : ℝ) (500837924397/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 4 (500837924427/1000000000000 : ℝ) (100167584887/200000000000 : ℝ) (500837924389/1000000000000 : ℝ) (500837924397/1000000000000 : ℝ) (62604740551/125000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 5 (62604740551/125000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 6 (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33267/262144 : ℝ))) 7 (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33267/262144 : ℝ)) hmem 8 (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33267/262144 : ℝ))) hcmem 8 (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33267/262144 : ℝ)) (992115503081/1000000000000 : ℝ) (992115503083/1000000000000 : ℝ) (500837924407/1000000000000 : ℝ) (7825592569/15625000000 : ℝ) (792966514013/1000000000000 : ℝ) (792966514029/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0486_exp_lower
  have heNumeric : (513725195917/250000000000 : ℝ)/4 ≤ Real.exp (-21314137433303/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725195917/250000000000 : ℝ)/4 ≤ Real.exp ((16633/131072 : ℝ)-(792966514029/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16633/131072 : ℝ) (33267/262144 : ℝ) (792966514029/1000000000000 : ℝ) (513725195917/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0487; no trusted numerical premise.
theorem cover8_leaf0487_exp_radius : (124752379672395069/125000000000000000 : ℝ) ≤ Real.exp ((-8317/524288 : ℝ)/8) ∧ Real.exp ((-8317/524288 : ℝ)/8) ≤ (998019037379160553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8317/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0487_exp_lower : (184022680806534787/200000000000000000 : ℝ) ≤ Real.exp ((-42628275856733/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628275856733/64000000000000 : ℝ)/8) ≤ (57507087752042121/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628275856733/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0487_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900751877/1000000000000 : ℝ) ≤ 4*Real.exp (33267/262144 : ℝ)*Real.exp (-mu (radius 8 (8317/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900751877/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8317/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0487_exp_radius
  have hrNumeric : (492130871371/500000000000 : ℝ) ≤ Real.exp (-8317/524288 : ℝ) ∧ Real.exp (-8317/524288 : ℝ) ≤ (984261742743/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492130871371/500000000000 : ℝ) ≤ (radius 8 (8317/65536 : ℝ)) ∧ (radius 8 (8317/65536 : ℝ)) ≤ (984261742743/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8317/65536 : ℝ)) (492130871371/500000000000 : ℝ) (984261742743/1000000000000 : ℝ) (176716784071/1000000000000 : ℝ) (176716784077/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8317/65536 : ℝ)) (492130871371/500000000000 : ℝ) (984261742743/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492130871371/500000000000 : ℝ) (984261742743/1000000000000 : ℝ) (992130871371/1000000000000 : ℝ) (248032717843/250000000000 : ℝ) (496049831857/500000000000 : ℝ) (198419932743/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 1 (992130871371/1000000000000 : ℝ) (248032717843/250000000000 : ℝ) (496049831857/500000000000 : ℝ) (198419932743/200000000000 : ℝ) (496057633771/500000000000 : ℝ) (124014408443/125000000000 : ℝ) (992115267419/1000000000000 : ℝ) (992115267421/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 2 (496057633771/500000000000 : ℝ) (124014408443/125000000000 : ℝ) (992115267419/1000000000000 : ℝ) (992115267421/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 3 (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 4 (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 5 (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 6 (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8317/65536 : ℝ)) 7 (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8317/65536 : ℝ))) (176716784071/1000000000000 : ℝ) (176716784077/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176716784071/1000000000000 : ℝ) (176716784077/1000000000000 : ℝ) (117671678407/200000000000 : ℝ) (588358392039/1000000000000 : ℝ) (420376954733/1000000000000 : ℝ) (420376954741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 1 (117671678407/200000000000 : ℝ) (588358392039/1000000000000 : ℝ) (420376954733/1000000000000 : ℝ) (420376954741/1000000000000 : ℝ) (63045959173/125000000000 : ℝ) (50436767339/100000000000 : ℝ) (99465030867/200000000000 : ℝ) (497325154343/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 2 (63045959173/125000000000 : ℝ) (50436767339/100000000000 : ℝ) (99465030867/200000000000 : ℝ) (497325154343/1000000000000 : ℝ) (500846413859/1000000000000 : ℝ) (500846413867/1000000000000 : ℝ) (7825531803/15625000000 : ℝ) (2504170177/5000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 3 (500846413859/1000000000000 : ℝ) (500846413867/1000000000000 : ℝ) (7825531803/15625000000 : ℝ) (2504170177/5000000000 : ℝ) (4006721797/8000000000 : ℝ) (250420112317/500000000000 : ℝ) (500840224587/1000000000000 : ℝ) (125210056149/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 4 (4006721797/8000000000 : ℝ) (250420112317/500000000000 : ℝ) (500840224587/1000000000000 : ℝ) (125210056149/250000000000 : ℝ) (250420112303/500000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 5 (250420112303/500000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 6 (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8317/65536 : ℝ))) 7 (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8317/65536 : ℝ)) hmem 8 (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8317/65536 : ℝ))) hcmem 8 (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8317/65536 : ℝ)) (24802881687/25000000000 : ℝ) (992115267483/1000000000000 : ℝ) (100168044921/200000000000 : ℝ) (100168044923/200000000000 : ℝ) (396485172089/500000000000 : ℝ) (792970344197/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0487_exp_lower
  have heNumeric : (2054900751877/1000000000000 : ℝ)/4 ≤ Real.exp (-42628275856733/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900751877/1000000000000 : ℝ)/4 ≤ Real.exp ((33267/262144 : ℝ)-(792970344197/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33267/262144 : ℝ) (8317/65536 : ℝ) (792970344197/1000000000000 : ℝ) (2054900751877/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0488; no trusted numerical premise.
theorem cover8_leaf0488_exp_radius : (998018977892592123/1000000000000000000 : ℝ) ≤ Real.exp ((-33269/2097152 : ℝ)/8) ∧ Real.exp ((-33269/2097152 : ℝ)/8) ≤ (249504744473148031/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33269/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0488_exp_lower : (920113402263211397/1000000000000000000 : ℝ) ≤ Real.exp ((-10657069210339/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657069210339/16000000000000 : ℝ)/8) ≤ (460056701131605699/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657069210339/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0488_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900720263/1000000000000 : ℝ) ≤ 4*Real.exp (8317/65536 : ℝ)*Real.exp (-mu (radius 8 (33269/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900720263/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33269/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0488_exp_radius
  have hrNumeric : (98426127341/100000000000 : ℝ) ≤ Real.exp (-33269/2097152 : ℝ) ∧ Real.exp (-33269/2097152 : ℝ) ≤ (984261273411/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98426127341/100000000000 : ℝ) ≤ (radius 8 (33269/262144 : ℝ)) ∧ (radius 8 (33269/262144 : ℝ)) ≤ (984261273411/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33269/262144 : ℝ)) (98426127341/100000000000 : ℝ) (984261273411/1000000000000 : ℝ) (35343879619/200000000000 : ℝ) (88359699051/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33269/262144 : ℝ)) (98426127341/100000000000 : ℝ) (984261273411/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98426127341/100000000000 : ℝ) (984261273411/1000000000000 : ℝ) (198426127341/200000000000 : ℝ) (496065318353/500000000000 : ℝ) (992099427179/1000000000000 : ℝ) (992099427181/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 1 (198426127341/200000000000 : ℝ) (496065318353/500000000000 : ℝ) (992099427179/1000000000000 : ℝ) (992099427181/1000000000000 : ℝ) (496057515971/500000000000 : ℝ) (124014378993/125000000000 : ℝ) (992115031819/1000000000000 : ℝ) (992115031821/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 2 (496057515971/500000000000 : ℝ) (124014378993/125000000000 : ℝ) (992115031819/1000000000000 : ℝ) (992115031821/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 3 (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 4 (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 5 (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 6 (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33269/262144 : ℝ)) 7 (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33269/262144 : ℝ))) (35343879619/200000000000 : ℝ) (88359699051/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35343879619/200000000000 : ℝ) (88359699051/500000000000 : ℝ) (588359699047/1000000000000 : ℝ) (588359699051/1000000000000 : ℝ) (52547507983/125000000000 : ℝ) (210190031937/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 1 (588359699047/1000000000000 : ℝ) (588359699051/1000000000000 : ℝ) (52547507983/125000000000 : ℝ) (210190031937/500000000000 : ℝ) (100873976291/200000000000 : ℝ) (504369881463/1000000000000 : ℝ) (497327545849/1000000000000 : ℝ) (497327545857/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 2 (100873976291/200000000000 : ℝ) (504369881463/1000000000000 : ℝ) (497327545849/1000000000000 : ℝ) (497327545857/1000000000000 : ℝ) (125212178413/250000000000 : ℝ) (25042435683/50000000000 : ℝ) (250418167943/500000000000 : ℝ) (100167267179/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 3 (125212178413/250000000000 : ℝ) (25042435683/50000000000 : ℝ) (250418167943/500000000000 : ℝ) (100167267179/200000000000 : ℝ) (500842524769/1000000000000 : ℝ) (250421262389/500000000000 : ℝ) (50084252473/100000000000 : ℝ) (25042126237/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 4 (500842524769/1000000000000 : ℝ) (250421262389/500000000000 : ℝ) (50084252473/100000000000 : ℝ) (25042126237/50000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 5 (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 6 (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33269/262144 : ℝ))) 7 (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33269/262144 : ℝ)) hmem 8 (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33269/262144 : ℝ))) hcmem 8 (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33269/262144 : ℝ)) (24802875797/25000000000 : ℝ) (992115031883/1000000000000 : ℝ) (500842524749/1000000000000 : ℝ) (500842524759/1000000000000 : ℝ) (39648708713/50000000000 : ℝ) (792974174279/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0488_exp_lower
  have heNumeric : (2054900720263/1000000000000 : ℝ)/4 ≤ Real.exp (-10657069210339/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900720263/1000000000000 : ℝ)/4 ≤ Real.exp ((8317/65536 : ℝ)-(792974174279/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8317/65536 : ℝ) (33269/262144 : ℝ) (792974174279/1000000000000 : ℝ) (2054900720263/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0489; no trusted numerical premise.
theorem cover8_leaf0489_exp_radius : (24950472960150681/25000000000000000 : ℝ) ≤ Real.exp ((-16635/1048576 : ℝ)/8) ∧ Real.exp ((-16635/1048576 : ℝ)/8) ≤ (998018918406027241/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16635/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0489_exp_lower : (920113400501684841/1000000000000000000 : ℝ) ≤ Real.exp ((-42628277821563/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628277821563/64000000000000 : ℝ)/8) ≤ (460056700250842421/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628277821563/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0489_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490068879/100000000000 : ℝ) ≤ 4*Real.exp (33269/262144 : ℝ)*Real.exp (-mu (radius 8 (16635/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490068879/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16635/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0489_exp_radius
  have hrNumeric : (984260804077/1000000000000 : ℝ) ≤ Real.exp (-16635/1048576 : ℝ) ∧ Real.exp (-16635/1048576 : ℝ) ≤ (492130402039/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984260804077/1000000000000 : ℝ) ≤ (radius 8 (16635/131072 : ℝ)) ∧ (radius 8 (16635/131072 : ℝ)) ≤ (492130402039/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16635/131072 : ℝ)) (984260804077/1000000000000 : ℝ) (492130402039/500000000000 : ℝ) (88361006043/500000000000 : ℝ) (44180503023/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16635/131072 : ℝ)) (984260804077/1000000000000 : ℝ) (492130402039/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984260804077/1000000000000 : ℝ) (492130402039/500000000000 : ℝ) (496065201019/500000000000 : ℝ) (992130402039/1000000000000 : ℝ) (248024797661/250000000000 : ℝ) (198419838129/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 1 (496065201019/500000000000 : ℝ) (992130402039/1000000000000 : ℝ) (248024797661/250000000000 : ℝ) (198419838129/200000000000 : ℝ) (992114796341/1000000000000 : ℝ) (496057398171/500000000000 : ℝ) (496057398109/500000000000 : ℝ) (49605739811/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 2 (992114796341/1000000000000 : ℝ) (496057398171/500000000000 : ℝ) (496057398109/500000000000 : ℝ) (49605739811/50000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 3 (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 4 (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 5 (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 6 (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16635/131072 : ℝ)) 7 (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16635/131072 : ℝ))) (88361006043/500000000000 : ℝ) (44180503023/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88361006043/500000000000 : ℝ) (44180503023/250000000000 : ℝ) (588361006043/1000000000000 : ℝ) (294180503023/500000000000 : ℝ) (420383172933/1000000000000 : ℝ) (210191586471/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 1 (588361006043/1000000000000 : ℝ) (294180503023/500000000000 : ℝ) (420383172933/1000000000000 : ℝ) (210191586471/500000000000 : ℝ) (31523255593/62500000000 : ℝ) (252186044747/500000000000 : ℝ) (99465987463/200000000000 : ℝ) (497329937323/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 2 (31523255593/62500000000 : ℝ) (252186044747/500000000000 : ℝ) (99465987463/200000000000 : ℝ) (497329937323/1000000000000 : ℝ) (500851013401/1000000000000 : ℝ) (500851013409/1000000000000 : ℝ) (500838636337/1000000000000 : ℝ) (100167727269/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 3 (500851013401/1000000000000 : ℝ) (500851013409/1000000000000 : ℝ) (500838636337/1000000000000 : ℝ) (100167727269/200000000000 : ℝ) (500844824869/1000000000000 : ℝ) (500844824877/1000000000000 : ℝ) (50084482483/100000000000 : ℝ) (500844824839/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 4 (500844824869/1000000000000 : ℝ) (500844824877/1000000000000 : ℝ) (50084482483/100000000000 : ℝ) (500844824839/1000000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 5 (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 6 (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16635/131072 : ℝ))) 7 (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16635/131072 : ℝ)) hmem 8 (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16635/131072 : ℝ))) hcmem 8 (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16635/131072 : ℝ)) (992114796279/1000000000000 : ℝ) (992114796281/1000000000000 : ℝ) (500844824849/1000000000000 : ℝ) (250422412429/500000000000 : ℝ) (31719120171/40000000000 : ℝ) (198244501073/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0489_exp_lower
  have heNumeric : (205490068879/100000000000 : ℝ)/4 ≤ Real.exp (-42628277821563/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490068879/100000000000 : ℝ)/4 ≤ Real.exp ((33269/262144 : ℝ)-(198244501073/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33269/262144 : ℝ) (16635/131072 : ℝ) (198244501073/250000000000 : ℝ) (205490068879/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0490; no trusted numerical premise.
theorem cover8_leaf0490_exp_radius : (499009429459732951/500000000000000000 : ℝ) ≤ Real.exp ((-33271/2097152 : ℝ)/8) ∧ Real.exp ((-33271/2097152 : ℝ)/8) ≤ (998018858919465903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33271/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0490_exp_lower : (920113398749819479/1000000000000000000 : ℝ) ≤ Real.exp ((-21314139398197/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314139398197/32000000000000 : ℝ)/8) ≤ (23002834968745487/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314139398197/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0490_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900657491/1000000000000 : ℝ) ≤ 4*Real.exp (16635/131072 : ℝ)*Real.exp (-mu (radius 8 (33271/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900657491/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33271/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0490_exp_radius
  have hrNumeric : (196852066949/200000000000 : ℝ) ≤ Real.exp (-33271/2097152 : ℝ) ∧ Real.exp (-33271/2097152 : ℝ) ≤ (492130167373/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196852066949/200000000000 : ℝ) ≤ (radius 8 (33271/262144 : ℝ)) ∧ (radius 8 (33271/262144 : ℝ)) ≤ (492130167373/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33271/262144 : ℝ)) (196852066949/200000000000 : ℝ) (492130167373/500000000000 : ℝ) (17672462603/100000000000 : ℝ) (176724626037/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33271/262144 : ℝ)) (196852066949/200000000000 : ℝ) (492130167373/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196852066949/200000000000 : ℝ) (492130167373/500000000000 : ℝ) (248032541843/250000000000 : ℝ) (992130167373/1000000000000 : ℝ) (992098954109/1000000000000 : ℝ) (99209895411/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 1 (248032541843/250000000000 : ℝ) (992130167373/1000000000000 : ℝ) (992098954109/1000000000000 : ℝ) (99209895411/100000000000 : ℝ) (49605728037/50000000000 : ℝ) (496057280371/500000000000 : ℝ) (992114560617/1000000000000 : ℝ) (992114560619/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 2 (49605728037/50000000000 : ℝ) (496057280371/500000000000 : ℝ) (992114560617/1000000000000 : ℝ) (992114560619/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 3 (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 4 (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 5 (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 6 (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33271/262144 : ℝ)) 7 (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33271/262144 : ℝ))) (17672462603/100000000000 : ℝ) (176724626037/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17672462603/100000000000 : ℝ) (176724626037/1000000000000 : ℝ) (117672462603/200000000000 : ℝ) (588362313019/1000000000000 : ℝ) (105096570481/250000000000 : ℝ) (420386281933/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 1 (117672462603/200000000000 : ℝ) (588362313019/1000000000000 : ℝ) (105096570481/250000000000 : ℝ) (420386281933/1000000000000 : ℝ) (504374297469/1000000000000 : ℝ) (126093574369/250000000000 : ℝ) (248666164361/500000000000 : ℝ) (49733232873/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 2 (504374297469/1000000000000 : ℝ) (126093574369/250000000000 : ℝ) (248666164361/500000000000 : ℝ) (49733232873/100000000000 : ℝ) (100170662619/200000000000 : ℝ) (500853313103/1000000000000 : ℝ) (500840936733/1000000000000 : ℝ) (500840936741/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 3 (100170662619/200000000000 : ℝ) (500853313103/1000000000000 : ℝ) (500840936733/1000000000000 : ℝ) (500840936741/1000000000000 : ℝ) (250423562457/500000000000 : ℝ) (250423562461/500000000000 : ℝ) (4006776999/8000000000 : ℝ) (125211781221/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 4 (250423562457/500000000000 : ℝ) (250423562461/500000000000 : ℝ) (4006776999/8000000000 : ℝ) (125211781221/250000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 5 (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 6 (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33271/262144 : ℝ))) 7 (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33271/262144 : ℝ)) hmem 8 (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33271/262144 : ℝ))) hcmem 8 (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33271/262144 : ℝ)) (496057280339/500000000000 : ℝ) (992114560681/1000000000000 : ℝ) (250423562447/500000000000 : ℝ) (500847124903/1000000000000 : ℝ) (792981834203/1000000000000 : ℝ) (792981834221/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0490_exp_lower
  have heNumeric : (2054900657491/1000000000000 : ℝ)/4 ≤ Real.exp (-21314139398197/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900657491/1000000000000 : ℝ)/4 ≤ Real.exp ((16635/131072 : ℝ)-(792981834221/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16635/131072 : ℝ) (33271/262144 : ℝ) (792981834221/1000000000000 : ℝ) (2054900657491/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0491; no trusted numerical premise.
theorem cover8_leaf0491_exp_radius : (99801879943290811/100000000000000000 : ℝ) ≤ Real.exp ((-4159/262144 : ℝ)/8) ∧ Real.exp ((-4159/262144 : ℝ)/8) ≤ (998018799432908111/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4159/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0491_exp_lower : (36804535880309213/40000000000000000 : ℝ) ≤ Real.exp ((-8525655953157/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525655953157/12800000000000 : ℝ)/8) ≤ (460056698503865163/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525655953157/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0491_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450313183/500000000000 : ℝ) ≤ 4*Real.exp (33271/262144 : ℝ)*Real.exp (-mu (radius 8 (4159/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450313183/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4159/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0491_exp_radius
  have hrNumeric : (492129932707/500000000000 : ℝ) ≤ Real.exp (-4159/262144 : ℝ) ∧ Real.exp (-4159/262144 : ℝ) ≤ (196851973083/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492129932707/500000000000 : ℝ) ≤ (radius 8 (4159/32768 : ℝ)) ∧ (radius 8 (4159/32768 : ℝ)) ≤ (196851973083/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4159/32768 : ℝ)) (492129932707/500000000000 : ℝ) (196851973083/200000000000 : ℝ) (176727239929/1000000000000 : ℝ) (690340781/3906250000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4159/32768 : ℝ)) (492129932707/500000000000 : ℝ) (196851973083/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492129932707/500000000000 : ℝ) (196851973083/200000000000 : ℝ) (992129932707/1000000000000 : ℝ) (248032483177/250000000000 : ℝ) (39683948703/40000000000 : ℝ) (124012339697/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 1 (992129932707/1000000000000 : ℝ) (248032483177/250000000000 : ℝ) (39683948703/40000000000 : ℝ) (124012339697/125000000000 : ℝ) (992114325141/1000000000000 : ℝ) (496057162571/500000000000 : ℝ) (496057162509/500000000000 : ℝ) (49605716251/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 2 (992114325141/1000000000000 : ℝ) (496057162571/500000000000 : ℝ) (496057162509/500000000000 : ℝ) (49605716251/50000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 3 (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 4 (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 5 (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 6 (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4159/32768 : ℝ)) 7 (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4159/32768 : ℝ))) (176727239929/1000000000000 : ℝ) (690340781/3906250000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176727239929/1000000000000 : ℝ) (690340781/3906250000 : ℝ) (147090904991/250000000000 : ℝ) (4596590781/7812500000 : ℝ) (420389390837/1000000000000 : ℝ) (420389390847/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 1 (147090904991/250000000000 : ℝ) (4596590781/7812500000 : ℝ) (420389390837/1000000000000 : ℝ) (420389390847/1000000000000 : ℝ) (2521882527/5000000000 : ℝ) (7880882897/15625000000 : ℝ) (49733472007/100000000000 : ℝ) (248667360039/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 2 (2521882527/5000000000 : ℝ) (7880882897/15625000000 : ℝ) (49733472007/100000000000 : ℝ) (248667360039/500000000000 : ℝ) (100171122547/200000000000 : ℝ) (500855612743/1000000000000 : ℝ) (250421618537/500000000000 : ℝ) (500843237083/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 3 (100171122547/200000000000 : ℝ) (500855612743/1000000000000 : ℝ) (250421618537/500000000000 : ℝ) (500843237083/1000000000000 : ℝ) (62606178113/125000000000 : ℝ) (500849424913/1000000000000 : ℝ) (250424712433/500000000000 : ℝ) (4006795399/8000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 4 (62606178113/125000000000 : ℝ) (500849424913/1000000000000 : ℝ) (250424712433/500000000000 : ℝ) (4006795399/8000000000 : ℝ) (100169884977/200000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 5 (100169884977/200000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 6 (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4159/32768 : ℝ))) 7 (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4159/32768 : ℝ)) hmem 8 (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4159/32768 : ℝ))) hcmem 8 (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4159/32768 : ℝ)) (992114325079/1000000000000 : ℝ) (992114325081/1000000000000 : ℝ) (125212356221/250000000000 : ℝ) (250424712447/500000000000 : ℝ) (792985664047/1000000000000 : ℝ) (158597132813/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0491_exp_lower
  have heNumeric : (1027450313183/500000000000 : ℝ)/4 ≤ Real.exp (-8525655953157/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450313183/500000000000 : ℝ)/4 ≤ Real.exp ((33271/262144 : ℝ)-(158597132813/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33271/262144 : ℝ) (4159/32768 : ℝ) (158597132813/200000000000 : ℝ) (1027450313183/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0492; no trusted numerical premise.
theorem cover8_leaf0492_exp_radius : (998018739946353863/1000000000000000000 : ℝ) ≤ Real.exp ((-33273/2097152 : ℝ)/8) ∧ Real.exp ((-33273/2097152 : ℝ)/8) ≤ (124752342493294233/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33273/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0492_exp_lower : (92011339527323211/100000000000000000 : ℝ) ≤ Real.exp ((-5328535091369/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328535091369/8000000000000 : ℝ)/8) ≤ (920113395273232111/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328535091369/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0492_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431287211/62500000000 : ℝ) ≤ 4*Real.exp (4159/32768 : ℝ)*Real.exp (-mu (radius 8 (33273/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431287211/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33273/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0492_exp_radius
  have hrNumeric : (492129698041/500000000000 : ℝ) ≤ Real.exp (-33273/2097152 : ℝ) ∧ Real.exp (-33273/2097152 : ℝ) ≤ (984259396083/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492129698041/500000000000 : ℝ) ≤ (radius 8 (33273/262144 : ℝ)) ∧ (radius 8 (33273/262144 : ℝ)) ≤ (984259396083/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33273/262144 : ℝ)) (492129698041/500000000000 : ℝ) (984259396083/1000000000000 : ℝ) (88364926897/500000000000 : ℝ) (176729853801/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33273/262144 : ℝ)) (492129698041/500000000000 : ℝ) (984259396083/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492129698041/500000000000 : ℝ) (984259396083/1000000000000 : ℝ) (992129698041/1000000000000 : ℝ) (496064849021/500000000000 : ℝ) (12401231013/12500000000 : ℝ) (992098481041/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 1 (992129698041/1000000000000 : ℝ) (496064849021/500000000000 : ℝ) (12401231013/12500000000 : ℝ) (992098481041/1000000000000 : ℝ) (49605704477/50000000000 : ℝ) (496057044771/500000000000 : ℝ) (992114089417/1000000000000 : ℝ) (992114089419/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 2 (49605704477/50000000000 : ℝ) (496057044771/500000000000 : ℝ) (992114089417/1000000000000 : ℝ) (992114089419/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 3 (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 4 (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 5 (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 6 (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33273/262144 : ℝ)) 7 (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33273/262144 : ℝ))) (88364926897/500000000000 : ℝ) (176729853801/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88364926897/500000000000 : ℝ) (176729853801/1000000000000 : ℝ) (588364926897/1000000000000 : ℝ) (588364926901/1000000000000 : ℝ) (52549062461/125000000000 : ℝ) (420392499697/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 1 (588364926897/1000000000000 : ℝ) (588364926901/1000000000000 : ℝ) (52549062461/125000000000 : ℝ) (420392499697/1000000000000 : ℝ) (126094678323/250000000000 : ℝ) (504378713299/1000000000000 : ℝ) (497337111371/1000000000000 : ℝ) (497337111379/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 2 (126094678323/250000000000 : ℝ) (504378713299/1000000000000 : ℝ) (497337111371/1000000000000 : ℝ) (497337111379/1000000000000 : ℝ) (500857912331/1000000000000 : ℝ) (500857912339/1000000000000 : ℝ) (125211384343/250000000000 : ℝ) (25042276869/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 3 (500857912331/1000000000000 : ℝ) (500857912339/1000000000000 : ℝ) (125211384343/250000000000 : ℝ) (25042276869/50000000000 : ℝ) (500851724851/1000000000000 : ℝ) (25042586243/50000000000 : ℝ) (500851724813/1000000000000 : ℝ) (250425862411/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 4 (500851724851/1000000000000 : ℝ) (25042586243/50000000000 : ℝ) (500851724813/1000000000000 : ℝ) (250425862411/500000000000 : ℝ) (15651616401/31250000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 5 (15651616401/31250000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 6 (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33273/262144 : ℝ))) 7 (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33273/262144 : ℝ)) hmem 8 (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33273/262144 : ℝ))) hcmem 8 (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33273/262144 : ℝ)) (496057044739/500000000000 : ℝ) (992114089481/1000000000000 : ℝ) (500851724831/1000000000000 : ℝ) (500851724841/1000000000000 : ℝ) (12390460841/15625000000 : ℝ) (792989493843/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0492_exp_lower
  have heNumeric : (128431287211/62500000000 : ℝ)/4 ≤ Real.exp (-5328535091369/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431287211/62500000000 : ℝ)/4 ≤ Real.exp ((4159/32768 : ℝ)-(792989493843/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4159/32768 : ℝ) (33273/262144 : ℝ) (792989493843/1000000000000 : ℝ) (128431287211/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0493; no trusted numerical premise.
theorem cover8_leaf0493_exp_radius : (499009340229901581/500000000000000000 : ℝ) ≤ Real.exp ((-16637/1048576 : ℝ)/8) ∧ Real.exp ((-16637/1048576 : ℝ)/8) ≤ (998018680459803163/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16637/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0493_exp_lower : (184022678709771029/200000000000000000 : ℝ) ≤ Real.exp ((-42628281690487/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628281690487/64000000000000 : ℝ)/8) ≤ (460056696774427573/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628281690487/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0493_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862570571/125000000000 : ℝ) ≤ 4*Real.exp (33273/262144 : ℝ)*Real.exp (-mu (radius 8 (16637/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862570571/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16637/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0493_exp_radius
  have hrNumeric : (984258926751/1000000000000 : ℝ) ≤ Real.exp (-16637/1048576 : ℝ) ∧ Real.exp (-16637/1048576 : ℝ) ≤ (30758091461/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984258926751/1000000000000 : ℝ) ≤ (radius 8 (16637/131072 : ℝ)) ∧ (radius 8 (16637/131072 : ℝ)) ≤ (30758091461/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16637/131072 : ℝ)) (984258926751/1000000000000 : ℝ) (30758091461/31250000000 : ℝ) (88366233807/500000000000 : ℝ) (8836623381/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16637/131072 : ℝ)) (984258926751/1000000000000 : ℝ) (30758091461/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984258926751/1000000000000 : ℝ) (30758091461/31250000000 : ℝ) (7937035707/8000000000 : ℝ) (62008091461/62500000000 : ℝ) (198419648901/200000000000 : ℝ) (992098244507/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 1 (7937035707/8000000000 : ℝ) (62008091461/62500000000 : ℝ) (198419648901/200000000000 : ℝ) (992098244507/1000000000000 : ℝ) (49605692697/50000000000 : ℝ) (496056926971/500000000000 : ℝ) (992113853817/1000000000000 : ℝ) (992113853819/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 2 (49605692697/50000000000 : ℝ) (496056926971/500000000000 : ℝ) (992113853817/1000000000000 : ℝ) (992113853819/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 3 (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 4 (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 5 (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 6 (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16637/131072 : ℝ)) 7 (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16637/131072 : ℝ))) (88366233807/500000000000 : ℝ) (8836623381/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88366233807/500000000000 : ℝ) (8836623381/50000000000 : ℝ) (588366233807/1000000000000 : ℝ) (58836623381/100000000000 : ℝ) (420395608461/1000000000000 : ℝ) (420395608469/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 1 (588366233807/1000000000000 : ℝ) (58836623381/100000000000 : ℝ) (420395608461/1000000000000 : ℝ) (420395608469/1000000000000 : ℝ) (252190460567/500000000000 : ℝ) (25219046057/50000000000 : ℝ) (124334875653/250000000000 : ℝ) (497339502619/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 2 (252190460567/500000000000 : ℝ) (25219046057/50000000000 : ℝ) (124334875653/250000000000 : ℝ) (497339502619/1000000000000 : ℝ) (500860211873/1000000000000 : ℝ) (12521505297/25000000000 : ℝ) (100169567523/200000000000 : ℝ) (250423918811/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 3 (500860211873/1000000000000 : ℝ) (12521505297/25000000000 : ℝ) (100169567523/200000000000 : ℝ) (250423918811/500000000000 : ℝ) (62606753093/125000000000 : ℝ) (500854024751/1000000000000 : ℝ) (100170804941/200000000000 : ℝ) (500854024713/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 4 (62606753093/125000000000 : ℝ) (500854024751/1000000000000 : ℝ) (100170804941/200000000000 : ℝ) (500854024713/1000000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 5 (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 6 (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16637/131072 : ℝ))) 7 (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16637/131072 : ℝ)) hmem 8 (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16637/131072 : ℝ))) hcmem 8 (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16637/131072 : ℝ)) (496056926939/500000000000 : ℝ) (992113853881/1000000000000 : ℝ) (125213506181/250000000000 : ℝ) (125213506183/250000000000 : ℝ) (792993323517/1000000000000 : ℝ) (792993323533/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0493_exp_lower
  have heNumeric : (256862570571/125000000000 : ℝ)/4 ≤ Real.exp (-42628281690487/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862570571/125000000000 : ℝ)/4 ≤ Real.exp ((33273/262144 : ℝ)-(792993323533/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33273/262144 : ℝ) (16637/131072 : ℝ) (792993323533/1000000000000 : ℝ) (256862570571/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0494; no trusted numerical premise.
theorem cover8_leaf0494_exp_radius : (998018620973256007/1000000000000000000 : ℝ) ≤ Real.exp ((-33275/2097152 : ℝ)/8) ∧ Real.exp ((-33275/2097152 : ℝ)/8) ≤ (124752327621657001/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33275/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0494_exp_lower : (230028347958189801/250000000000000000 : ℝ) ≤ Real.exp ((-21314141322707/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314141322707/32000000000000 : ℝ)/8) ≤ (184022678366551841/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314141322707/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0494_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900533907/1000000000000 : ℝ) ≤ 4*Real.exp (16637/131072 : ℝ)*Real.exp (-mu (radius 8 (33275/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900533907/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33275/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0494_exp_radius
  have hrNumeric : (49212922871/50000000000 : ℝ) ≤ Real.exp (-33275/2097152 : ℝ) ∧ Real.exp (-33275/2097152 : ℝ) ≤ (984258457421/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49212922871/50000000000 : ℝ) ≤ (radius 8 (33275/262144 : ℝ)) ∧ (radius 8 (33275/262144 : ℝ)) ≤ (984258457421/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33275/262144 : ℝ)) (49212922871/50000000000 : ℝ) (984258457421/1000000000000 : ℝ) (176735081393/1000000000000 : ℝ) (883675407/5000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33275/262144 : ℝ)) (49212922871/50000000000 : ℝ) (984258457421/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49212922871/50000000000 : ℝ) (984258457421/1000000000000 : ℝ) (99212922871/100000000000 : ℝ) (992129228711/1000000000000 : ℝ) (99209800797/100000000000 : ℝ) (248024501993/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 1 (99212922871/100000000000 : ℝ) (992129228711/1000000000000 : ℝ) (99209800797/100000000000 : ℝ) (248024501993/250000000000 : ℝ) (49605680917/50000000000 : ℝ) (496056809171/500000000000 : ℝ) (992113618217/1000000000000 : ℝ) (992113618219/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 2 (49605680917/50000000000 : ℝ) (496056809171/500000000000 : ℝ) (992113618217/1000000000000 : ℝ) (992113618219/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 3 (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 4 (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 5 (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 6 (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33275/262144 : ℝ)) 7 (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33275/262144 : ℝ))) (176735081393/1000000000000 : ℝ) (883675407/5000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176735081393/1000000000000 : ℝ) (883675407/5000000000 : ℝ) (73545942587/125000000000 : ℝ) (5883675407/10000000000 : ℝ) (420398717163/1000000000000 : ℝ) (420398717173/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 1 (73545942587/125000000000 : ℝ) (5883675407/10000000000 : ℝ) (420398717163/1000000000000 : ℝ) (420398717173/1000000000000 : ℝ) (504383128929/1000000000000 : ℝ) (504383128937/1000000000000 : ℝ) (2486709469/5000000000 : ℝ) (31083868363/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 2 (504383128929/1000000000000 : ℝ) (504383128937/1000000000000 : ℝ) (2486709469/5000000000 : ℝ) (31083868363/62500000000 : ℝ) (125215627841/250000000000 : ℝ) (500862511373/1000000000000 : ℝ) (31303133613/62500000000 : ℝ) (500850137817/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 3 (125215627841/250000000000 : ℝ) (500862511373/1000000000000 : ℝ) (31303133613/62500000000 : ℝ) (500850137817/1000000000000 : ℝ) (250428162293/500000000000 : ℝ) (100171264919/200000000000 : ℝ) (500856324547/1000000000000 : ℝ) (500856324557/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 4 (250428162293/500000000000 : ℝ) (100171264919/200000000000 : ℝ) (500856324547/1000000000000 : ℝ) (500856324557/1000000000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 5 (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 6 (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33275/262144 : ℝ))) 7 (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33275/262144 : ℝ)) hmem 8 (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33275/262144 : ℝ))) hcmem 8 (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33275/262144 : ℝ)) (496056809139/500000000000 : ℝ) (992113618281/1000000000000 : ℝ) (250428162283/500000000000 : ℝ) (15651760143/31250000000 : ℝ) (792997153131/1000000000000 : ℝ) (792997153151/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0494_exp_lower
  have heNumeric : (2054900533907/1000000000000 : ℝ)/4 ≤ Real.exp (-21314141322707/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900533907/1000000000000 : ℝ)/4 ≤ Real.exp ((16637/131072 : ℝ)-(792997153151/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16637/131072 : ℝ) (33275/262144 : ℝ) (792997153151/1000000000000 : ℝ) (2054900533907/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0495; no trusted numerical premise.
theorem cover8_leaf0495_exp_radius : (499009280743356199/500000000000000000 : ℝ) ≤ Real.exp ((-8319/524288 : ℝ)/8) ∧ Real.exp ((-8319/524288 : ℝ)/8) ≤ (998018561486712399/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8319/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0495_exp_lower : (2300283475314661/2500000000000000 : ℝ) ≤ Real.exp ((-42628283595221/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628283595221/64000000000000 : ℝ)/8) ≤ (920113390125864401/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628283595221/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0495_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900503411/1000000000000 : ℝ) ≤ 4*Real.exp (33275/262144 : ℝ)*Real.exp (-mu (radius 8 (8319/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900503411/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8319/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0495_exp_radius
  have hrNumeric : (984257988089/1000000000000 : ℝ) ≤ Real.exp (-8319/524288 : ℝ) ∧ Real.exp (-8319/524288 : ℝ) ≤ (98425798809/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984257988089/1000000000000 : ℝ) ≤ (radius 8 (8319/65536 : ℝ)) ∧ (radius 8 (8319/65536 : ℝ)) ≤ (98425798809/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8319/65536 : ℝ)) (984257988089/1000000000000 : ℝ) (98425798809/100000000000 : ℝ) (176737695133/1000000000000 : ℝ) (176737695139/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8319/65536 : ℝ)) (984257988089/1000000000000 : ℝ) (98425798809/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984257988089/1000000000000 : ℝ) (98425798809/100000000000 : ℝ) (248032248511/250000000000 : ℝ) (198425798809/200000000000 : ℝ) (248024442859/250000000000 : ℝ) (992097771437/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 1 (248032248511/250000000000 : ℝ) (198425798809/200000000000 : ℝ) (248024442859/250000000000 : ℝ) (992097771437/1000000000000 : ℝ) (49605669137/50000000000 : ℝ) (992113382741/1000000000000 : ℝ) (992113382617/1000000000000 : ℝ) (992113382619/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 2 (49605669137/50000000000 : ℝ) (992113382741/1000000000000 : ℝ) (992113382617/1000000000000 : ℝ) (992113382619/1000000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 3 (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 4 (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 5 (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 6 (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8319/65536 : ℝ)) 7 (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8319/65536 : ℝ))) (176737695133/1000000000000 : ℝ) (176737695139/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176737695133/1000000000000 : ℝ) (176737695139/1000000000000 : ℝ) (294184423783/500000000000 : ℝ) (58836884757/100000000000 : ℝ) (105100456449/250000000000 : ℝ) (105100456451/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 1 (294184423783/500000000000 : ℝ) (58836884757/100000000000 : ℝ) (105100456449/250000000000 : ℝ) (105100456451/250000000000 : ℝ) (504385336681/1000000000000 : ℝ) (504385336687/1000000000000 : ℝ) (99468856987/200000000000 : ℝ) (497344284943/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 2 (504385336681/1000000000000 : ℝ) (504385336687/1000000000000 : ℝ) (99468856987/200000000000 : ℝ) (497344284943/1000000000000 : ℝ) (62608101351/125000000000 : ℝ) (100172962163/200000000000 : ℝ) (7825819343/15625000000 : ℝ) (12521310949/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 3 (62608101351/125000000000 : ℝ) (100172962163/200000000000 : ℝ) (7825819343/15625000000 : ℝ) (12521310949/25000000000 : ℝ) (25042931219/50000000000 : ℝ) (125214656097/250000000000 : ℝ) (500858624341/1000000000000 : ℝ) (10017172487/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 4 (25042931219/50000000000 : ℝ) (125214656097/250000000000 : ℝ) (500858624341/1000000000000 : ℝ) (10017172487/20000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 5 (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 6 (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8319/65536 : ℝ))) 7 (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8319/65536 : ℝ)) hmem 8 (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8319/65536 : ℝ))) hcmem 8 (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8319/65536 : ℝ)) (496056691339/500000000000 : ℝ) (24802834567/25000000000 : ℝ) (12521465609/25000000000 : ℝ) (500858624369/1000000000000 : ℝ) (49562561417/62500000000 : ℝ) (793000982689/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0495_exp_lower
  have heNumeric : (2054900503411/1000000000000 : ℝ)/4 ≤ Real.exp (-42628283595221/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900503411/1000000000000 : ℝ)/4 ≤ Real.exp ((33275/262144 : ℝ)-(793000982689/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33275/262144 : ℝ) (8319/65536 : ℝ) (793000982689/1000000000000 : ℝ) (2054900503411/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0496; no trusted numerical premise.
theorem cover8_leaf0496_exp_radius : (499009251000086167/500000000000000000 : ℝ) ≤ Real.exp ((-33277/2097152 : ℝ)/8) ∧ Real.exp ((-33277/2097152 : ℝ)/8) ≤ (199603700400034467/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33277/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0496_exp_lower : (920113388427595663/1000000000000000000 : ℝ) ≤ Real.exp ((-10657071135057/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657071135057/16000000000000 : ℝ)/8) ≤ (57507086776724729/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657071135057/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0496_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900473069/1000000000000 : ℝ) ≤ 4*Real.exp (8319/65536 : ℝ)*Real.exp (-mu (radius 8 (33277/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900473069/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33277/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0496_exp_radius
  have hrNumeric : (492128759379/500000000000 : ℝ) ≤ Real.exp (-33277/2097152 : ℝ) ∧ Real.exp (-33277/2097152 : ℝ) ≤ (984257518759/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492128759379/500000000000 : ℝ) ≤ (radius 8 (33277/262144 : ℝ)) ∧ (radius 8 (33277/262144 : ℝ)) ≤ (984257518759/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33277/262144 : ℝ)) (492128759379/500000000000 : ℝ) (984257518759/1000000000000 : ℝ) (5523134651/31250000000 : ℝ) (176740308839/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33277/262144 : ℝ)) (492128759379/500000000000 : ℝ) (984257518759/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492128759379/500000000000 : ℝ) (984257518759/1000000000000 : ℝ) (992128759379/1000000000000 : ℝ) (49606437969/50000000000 : ℝ) (992097534901/1000000000000 : ℝ) (992097534903/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 1 (992128759379/1000000000000 : ℝ) (49606437969/50000000000 : ℝ) (992097534901/1000000000000 : ℝ) (992097534903/1000000000000 : ℝ) (49605657357/50000000000 : ℝ) (496056573571/500000000000 : ℝ) (992113147017/1000000000000 : ℝ) (992113147019/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 2 (49605657357/50000000000 : ℝ) (496056573571/500000000000 : ℝ) (992113147017/1000000000000 : ℝ) (992113147019/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 3 (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 4 (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 5 (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 6 (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33277/262144 : ℝ)) 7 (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33277/262144 : ℝ))) (5523134651/31250000000 : ℝ) (176740308839/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5523134651/31250000000 : ℝ) (176740308839/1000000000000 : ℝ) (36773134651/62500000000 : ℝ) (29418507721/50000000000 : ℝ) (420404934357/1000000000000 : ℝ) (210202467183/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 1 (36773134651/62500000000 : ℝ) (29418507721/50000000000 : ℝ) (420404934357/1000000000000 : ℝ) (210202467183/500000000000 : ℝ) (252193772193/500000000000 : ℝ) (504387544393/1000000000000 : ℝ) (31084167251/62500000000 : ℝ) (62168334503/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 2 (252193772193/500000000000 : ℝ) (504387544393/1000000000000 : ℝ) (31084167251/62500000000 : ℝ) (62168334503/125000000000 : ℝ) (500867110201/1000000000000 : ℝ) (500867110209/1000000000000 : ℝ) (500854738047/1000000000000 : ℝ) (100170947611/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 3 (500867110201/1000000000000 : ℝ) (500867110209/1000000000000 : ℝ) (500854738047/1000000000000 : ℝ) (100170947611/200000000000 : ℝ) (125215231031/250000000000 : ℝ) (125215231033/250000000000 : ℝ) (100172184817/200000000000 : ℝ) (250430462047/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 4 (125215231031/250000000000 : ℝ) (125215231033/250000000000 : ℝ) (100172184817/200000000000 : ℝ) (250430462047/500000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 5 (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 6 (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33277/262144 : ℝ))) 7 (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33277/262144 : ℝ)) hmem 8 (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33277/262144 : ℝ))) hcmem 8 (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33277/262144 : ℝ)) (496056573539/500000000000 : ℝ) (992113147081/1000000000000 : ℝ) (62607615513/125000000000 : ℝ) (500860924113/1000000000000 : ℝ) (158600962427/200000000000 : ℝ) (99125601519/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0496_exp_lower
  have heNumeric : (2054900473069/1000000000000 : ℝ)/4 ≤ Real.exp (-10657071135057/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900473069/1000000000000 : ℝ)/4 ≤ Real.exp ((8319/65536 : ℝ)-(99125601519/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8319/65536 : ℝ) (33277/262144 : ℝ) (99125601519/125000000000 : ℝ) (2054900473069/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0497; no trusted numerical premise.
theorem cover8_leaf0497_exp_radius : (124752305314204477/125000000000000000 : ℝ) ≤ Real.exp ((-16639/1048576 : ℝ)/8) ∧ Real.exp ((-16639/1048576 : ℝ)/8) ≤ (998018442513635817/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16639/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0497_exp_lower : (920113386738988119/1000000000000000000 : ℝ) ≤ Real.exp ((-42628285479859/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628285479859/64000000000000 : ℝ)/8) ≤ (23002834668474703/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628285479859/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0497_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900442899/1000000000000 : ℝ) ≤ 4*Real.exp (33277/262144 : ℝ)*Real.exp (-mu (radius 8 (16639/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900442899/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16639/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0497_exp_radius
  have hrNumeric : (246064262357/250000000000 : ℝ) ≤ Real.exp (-16639/1048576 : ℝ) ∧ Real.exp (-16639/1048576 : ℝ) ≤ (984257049429/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246064262357/250000000000 : ℝ) ≤ (radius 8 (16639/131072 : ℝ)) ∧ (radius 8 (16639/131072 : ℝ)) ≤ (984257049429/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16639/131072 : ℝ)) (246064262357/250000000000 : ℝ) (984257049429/1000000000000 : ℝ) (176742922487/1000000000000 : ℝ) (176742922493/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16639/131072 : ℝ)) (246064262357/250000000000 : ℝ) (984257049429/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246064262357/250000000000 : ℝ) (984257049429/1000000000000 : ℝ) (496064262357/500000000000 : ℝ) (198425704943/200000000000 : ℝ) (992097298367/1000000000000 : ℝ) (15501520287/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 1 (496064262357/500000000000 : ℝ) (198425704943/200000000000 : ℝ) (992097298367/1000000000000 : ℝ) (15501520287/15625000000 : ℝ) (49605645577/50000000000 : ℝ) (496056455771/500000000000 : ℝ) (992112911417/1000000000000 : ℝ) (992112911419/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 2 (49605645577/50000000000 : ℝ) (496056455771/500000000000 : ℝ) (992112911417/1000000000000 : ℝ) (992112911419/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 3 (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 4 (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 5 (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 6 (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16639/131072 : ℝ)) 7 (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16639/131072 : ℝ))) (176742922487/1000000000000 : ℝ) (176742922493/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176742922487/1000000000000 : ℝ) (176742922493/1000000000000 : ℝ) (588371461243/1000000000000 : ℝ) (588371461247/1000000000000 : ℝ) (210204021421/500000000000 : ℝ) (420408042851/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 1 (588371461243/1000000000000 : ℝ) (588371461247/1000000000000 : ℝ) (210204021421/500000000000 : ℝ) (420408042851/1000000000000 : ℝ) (252194876021/500000000000 : ℝ) (504389752049/1000000000000 : ℝ) (497349067039/1000000000000 : ℝ) (497349067047/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 2 (252194876021/500000000000 : ℝ) (504389752049/1000000000000 : ℝ) (497349067039/1000000000000 : ℝ) (497349067047/1000000000000 : ℝ) (25043470477/50000000000 : ℝ) (125217352387/250000000000 : ℝ) (500857038087/1000000000000 : ℝ) (31303564881/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 3 (25043470477/50000000000 : ℝ) (125217352387/250000000000 : ℝ) (500857038087/1000000000000 : ℝ) (31303564881/62500000000 : ℝ) (500863223813/1000000000000 : ℝ) (250431611911/500000000000 : ℝ) (20034528951/40000000000 : ℝ) (62607902973/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 4 (500863223813/1000000000000 : ℝ) (250431611911/500000000000 : ℝ) (20034528951/40000000000 : ℝ) (62607902973/125000000000 : ℝ) (250431611897/500000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 5 (250431611897/500000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 6 (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16639/131072 : ℝ))) 7 (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16639/131072 : ℝ)) hmem 8 (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16639/131072 : ℝ))) hcmem 8 (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16639/131072 : ℝ)) (496056455739/500000000000 : ℝ) (992112911481/1000000000000 : ℝ) (500863223793/1000000000000 : ℝ) (500863223803/1000000000000 : ℝ) (99126080189/125000000000 : ℝ) (793008641531/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0497_exp_lower
  have heNumeric : (2054900442899/1000000000000 : ℝ)/4 ≤ Real.exp (-42628285479859/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900442899/1000000000000 : ℝ)/4 ≤ Real.exp ((33277/262144 : ℝ)-(793008641531/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33277/262144 : ℝ) (16639/131072 : ℝ) (793008641531/1000000000000 : ℝ) (2054900442899/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0498; no trusted numerical premise.
theorem cover8_leaf0498_exp_radius : (998018383027102843/1000000000000000000 : ℝ) ≤ Real.exp ((-33279/2097152 : ℝ)/8) ∧ Real.exp ((-33279/2097152 : ℝ)/8) ≤ (249504595756775711/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33279/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0498_exp_lower : (920113385058086527/1000000000000000000 : ℝ) ≤ Real.exp ((-21314143207601/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314143207601/32000000000000 : ℝ)/8) ≤ (7188385820766301/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314143207601/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0498_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900412867/1000000000000 : ℝ) ≤ 4*Real.exp (16639/131072 : ℝ)*Real.exp (-mu (radius 8 (33279/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900412867/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33279/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0498_exp_radius
  have hrNumeric : (984256580097/1000000000000 : ℝ) ≤ Real.exp (-33279/2097152 : ℝ) ∧ Real.exp (-33279/2097152 : ℝ) ≤ (492128290049/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984256580097/1000000000000 : ℝ) ≤ (radius 8 (33279/262144 : ℝ)) ∧ (radius 8 (33279/262144 : ℝ)) ≤ (492128290049/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33279/262144 : ℝ)) (984256580097/1000000000000 : ℝ) (492128290049/500000000000 : ℝ) (176745536107/1000000000000 : ℝ) (176745536113/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33279/262144 : ℝ)) (984256580097/1000000000000 : ℝ) (492128290049/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984256580097/1000000000000 : ℝ) (492128290049/500000000000 : ℝ) (3875501133/3906250000 : ℝ) (992128290049/1000000000000 : ℝ) (124012132729/125000000000 : ℝ) (496048530917/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 1 (3875501133/3906250000 : ℝ) (992128290049/1000000000000 : ℝ) (124012132729/125000000000 : ℝ) (496048530917/500000000000 : ℝ) (49605633797/50000000000 : ℝ) (496056337971/500000000000 : ℝ) (992112675817/1000000000000 : ℝ) (992112675819/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 2 (49605633797/50000000000 : ℝ) (496056337971/500000000000 : ℝ) (992112675817/1000000000000 : ℝ) (992112675819/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 3 (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 4 (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 5 (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 6 (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33279/262144 : ℝ)) 7 (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33279/262144 : ℝ))) (176745536107/1000000000000 : ℝ) (176745536113/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176745536107/1000000000000 : ℝ) (176745536113/1000000000000 : ℝ) (588372768053/1000000000000 : ℝ) (588372768057/1000000000000 : ℝ) (420411151263/1000000000000 : ℝ) (420411151271/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 1 (588372768053/1000000000000 : ℝ) (588372768057/1000000000000 : ℝ) (420411151263/1000000000000 : ℝ) (420411151271/1000000000000 : ℝ) (252195979829/500000000000 : ℝ) (31524497479/62500000000 : ℝ) (248675729007/500000000000 : ℝ) (497351458021/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 2 (252195979829/500000000000 : ℝ) (31524497479/62500000000 : ℝ) (248675729007/500000000000 : ℝ) (497351458021/1000000000000 : ℝ) (125217927209/250000000000 : ℝ) (500871708843/1000000000000 : ℝ) (125214834521/250000000000 : ℝ) (125214834523/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 3 (125217927209/250000000000 : ℝ) (500871708843/1000000000000 : ℝ) (125214834521/250000000000 : ℝ) (125214834523/250000000000 : ℝ) (25043276173/50000000000 : ℝ) (125216380867/250000000000 : ℝ) (500865523421/1000000000000 : ℝ) (50086552343/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 4 (25043276173/50000000000 : ℝ) (125216380867/250000000000 : ℝ) (500865523421/1000000000000 : ℝ) (50086552343/100000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 5 (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 6 (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33279/262144 : ℝ))) 7 (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33279/262144 : ℝ)) hmem 8 (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33279/262144 : ℝ))) hcmem 8 (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33279/262144 : ℝ)) (496056337939/500000000000 : ℝ) (992112675881/1000000000000 : ℝ) (6260819043/12500000000 : ℝ) (500865523449/1000000000000 : ℝ) (31720498833/40000000000 : ℝ) (793012470843/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0498_exp_lower
  have heNumeric : (2054900412867/1000000000000 : ℝ)/4 ≤ Real.exp (-21314143207601/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900412867/1000000000000 : ℝ)/4 ≤ Real.exp ((16639/131072 : ℝ)-(793012470843/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16639/131072 : ℝ) (33279/262144 : ℝ) (793012470843/1000000000000 : ℝ) (2054900412867/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0499; no trusted numerical premise.
theorem cover8_leaf0499_exp_radius : (124752290442571677/125000000000000000 : ℝ) ≤ Real.exp ((-65/4096 : ℝ)/8) ∧ Real.exp ((-65/4096 : ℝ)/8) ≤ (998018323540573417/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-65/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0499_exp_lower : (460056691693538079/500000000000000000 : ℝ) ≤ Real.exp ((-42628287345041/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628287345041/64000000000000 : ℝ)/8) ≤ (920113383387076159/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628287345041/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0499_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725095753/250000000000 : ℝ) ≤ 4*Real.exp (33279/262144 : ℝ)*Real.exp (-mu (radius 8 (65/512 : ℝ))) ∧ (20549/10000 : ℝ) < (513725095753/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (65/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0499_exp_radius
  have hrNumeric : (984256110767/1000000000000 : ℝ) ≤ Real.exp (-65/4096 : ℝ) ∧ Real.exp (-65/4096 : ℝ) ≤ (61516006923/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984256110767/1000000000000 : ℝ) ≤ (radius 8 (65/512 : ℝ)) ∧ (radius 8 (65/512 : ℝ)) ≤ (61516006923/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (65/512 : ℝ)) (984256110767/1000000000000 : ℝ) (61516006923/62500000000 : ℝ) (176748149681/1000000000000 : ℝ) (22093518711/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (65/512 : ℝ)) (984256110767/1000000000000 : ℝ) (61516006923/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (65/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984256110767/1000000000000 : ℝ) (61516006923/62500000000 : ℝ) (992128055383/1000000000000 : ℝ) (124016006923/125000000000 : ℝ) (496048412649/500000000000 : ℝ) (992096825299/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (65/512 : ℝ)) 1 (992128055383/1000000000000 : ℝ) (124016006923/125000000000 : ℝ) (496048412649/500000000000 : ℝ) (992096825299/1000000000000 : ℝ) (49605622017/50000000000 : ℝ) (496056220171/500000000000 : ℝ) (992112440217/1000000000000 : ℝ) (992112440219/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (65/512 : ℝ)) 2 (49605622017/50000000000 : ℝ) (496056220171/500000000000 : ℝ) (992112440217/1000000000000 : ℝ) (992112440219/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (65/512 : ℝ)) 3 (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (65/512 : ℝ)) 4 (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (65/512 : ℝ)) 5 (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (65/512 : ℝ)) 6 (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (65/512 : ℝ)) 7 (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (65/512 : ℝ))) (176748149681/1000000000000 : ℝ) (22093518711/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176748149681/1000000000000 : ℝ) (22093518711/125000000000 : ℝ) (14709351871/25000000000 : ℝ) (147093518711/250000000000 : ℝ) (420414259607/1000000000000 : ℝ) (13137945613/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 1 (14709351871/25000000000 : ℝ) (147093518711/250000000000 : ℝ) (420414259607/1000000000000 : ℝ) (13137945613/31250000000 : ℝ) (504394167223/1000000000000 : ℝ) (50439416723/100000000000 : ℝ) (49735384893/100000000000 : ℝ) (248676924469/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 2 (504394167223/1000000000000 : ℝ) (50439416723/100000000000 : ℝ) (49735384893/100000000000 : ℝ) (248676924469/500000000000 : ℝ) (125218502019/250000000000 : ℝ) (125218502021/250000000000 : ℝ) (250430819013/500000000000 : ℝ) (250430819017/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 3 (125218502019/250000000000 : ℝ) (125218502021/250000000000 : ℝ) (250430819013/500000000000 : ℝ) (250430819017/500000000000 : ℝ) (500867823051/1000000000000 : ℝ) (500867823059/1000000000000 : ℝ) (125216955753/250000000000 : ℝ) (500867823021/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 4 (500867823051/1000000000000 : ℝ) (500867823059/1000000000000 : ℝ) (125216955753/250000000000 : ℝ) (500867823021/1000000000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 5 (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 6 (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (65/512 : ℝ))) 7 (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (65/512 : ℝ)) hmem 8 (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (65/512 : ℝ))) hcmem 8 (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (65/512 : ℝ)) (496056220139/500000000000 : ℝ) (992112440281/1000000000000 : ℝ) (500867823031/1000000000000 : ℝ) (1565211947/3125000000 : ℝ) (793016300051/1000000000000 : ℝ) (793016300069/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0499_exp_lower
  have heNumeric : (513725095753/250000000000 : ℝ)/4 ≤ Real.exp (-42628287345041/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725095753/250000000000 : ℝ)/4 ≤ Real.exp ((33279/262144 : ℝ)-(793016300069/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33279/262144 : ℝ) (65/512 : ℝ) (793016300069/1000000000000 : ℝ) (513725095753/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0475_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0475_certificate
#check SmaleRate.Proofs.cover8_leaf0476_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0476_certificate
#check SmaleRate.Proofs.cover8_leaf0477_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0477_certificate
#check SmaleRate.Proofs.cover8_leaf0478_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0478_certificate
#check SmaleRate.Proofs.cover8_leaf0479_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0479_certificate
#check SmaleRate.Proofs.cover8_leaf0480_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0480_certificate
#check SmaleRate.Proofs.cover8_leaf0481_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0481_certificate
#check SmaleRate.Proofs.cover8_leaf0482_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0482_certificate
#check SmaleRate.Proofs.cover8_leaf0483_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0483_certificate
#check SmaleRate.Proofs.cover8_leaf0484_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0484_certificate
#check SmaleRate.Proofs.cover8_leaf0485_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0485_certificate
#check SmaleRate.Proofs.cover8_leaf0486_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0486_certificate
#check SmaleRate.Proofs.cover8_leaf0487_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0487_certificate
#check SmaleRate.Proofs.cover8_leaf0488_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0488_certificate
#check SmaleRate.Proofs.cover8_leaf0489_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0489_certificate
#check SmaleRate.Proofs.cover8_leaf0490_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0490_certificate
#check SmaleRate.Proofs.cover8_leaf0491_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0491_certificate
#check SmaleRate.Proofs.cover8_leaf0492_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0492_certificate
#check SmaleRate.Proofs.cover8_leaf0493_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0493_certificate
#check SmaleRate.Proofs.cover8_leaf0494_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0494_certificate
#check SmaleRate.Proofs.cover8_leaf0495_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0495_certificate
#check SmaleRate.Proofs.cover8_leaf0496_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0496_certificate
#check SmaleRate.Proofs.cover8_leaf0497_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0497_certificate
#check SmaleRate.Proofs.cover8_leaf0498_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0498_certificate
#check SmaleRate.Proofs.cover8_leaf0499_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0499_certificate
