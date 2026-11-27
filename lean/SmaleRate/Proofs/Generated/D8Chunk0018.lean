/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0450; no trusted numerical premise.
theorem cover8_leaf0450_exp_radius : (499010619192342523/500000000000000000 : ℝ) ≤ Real.exp ((-33231/2097152 : ℝ)/8) ∧ Real.exp ((-33231/2097152 : ℝ)/8) ≤ (998021238384685047/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33231/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0450_exp_lower : (115014184479822073/125000000000000000 : ℝ) ≤ Real.exp ((-21314117950057/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314117950057/32000000000000 : ℝ)/8) ≤ (184022695167715317/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314117950057/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0450_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902034797/1000000000000 : ℝ) ≤ 4*Real.exp (16615/131072 : ℝ)*Real.exp (-mu (radius 8 (33231/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902034797/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33231/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0450_exp_radius
  have hrNumeric : (4921395541/5000000000 : ℝ) ≤ Real.exp (-33231/2097152 : ℝ) ∧ Real.exp (-33231/2097152 : ℝ) ≤ (984279108201/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (4921395541/5000000000 : ℝ) ≤ (radius 8 (33231/262144 : ℝ)) ∧ (radius 8 (33231/262144 : ℝ)) ≤ (984279108201/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33231/262144 : ℝ)) (4921395541/5000000000 : ℝ) (984279108201/1000000000000 : ℝ) (4415500903/25000000000 : ℝ) (88310018063/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33231/262144 : ℝ)) (4921395541/5000000000 : ℝ) (984279108201/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (4921395541/5000000000 : ℝ) (984279108201/1000000000000 : ℝ) (9921395541/10000000000 : ℝ) (992139554101/1000000000000 : ℝ) (992108415547/1000000000000 : ℝ) (248027103887/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 1 (9921395541/10000000000 : ℝ) (992139554101/1000000000000 : ℝ) (992108415547/1000000000000 : ℝ) (248027103887/250000000000 : ℝ) (992123984823/1000000000000 : ℝ) (39684959393/40000000000 : ℝ) (992123984701/1000000000000 : ℝ) (992123984703/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 2 (992123984823/1000000000000 : ℝ) (39684959393/40000000000 : ℝ) (992123984701/1000000000000 : ℝ) (992123984703/1000000000000 : ℝ) (496061992381/500000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 3 (496061992381/500000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 4 (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 5 (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 6 (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33231/262144 : ℝ)) 7 (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33231/262144 : ℝ))) (4415500903/25000000000 : ℝ) (88310018063/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4415500903/25000000000 : ℝ) (88310018063/500000000000 : ℝ) (29415500903/50000000000 : ℝ) (588310018063/1000000000000 : ℝ) (210130933063/500000000000 : ℝ) (210130933067/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 1 (29415500903/50000000000 : ℝ) (588310018063/1000000000000 : ℝ) (210130933063/500000000000 : ℝ) (210130933067/500000000000 : ℝ) (504285942093/1000000000000 : ℝ) (504285942099/1000000000000 : ℝ) (99447325967/200000000000 : ℝ) (248618314921/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 2 (504285942093/1000000000000 : ℝ) (504285942099/1000000000000 : ℝ) (99447325967/200000000000 : ℝ) (248618314921/500000000000 : ℝ) (125190321491/250000000000 : ℝ) (500761285971/1000000000000 : ℝ) (100149776299/200000000000 : ℝ) (500748881503/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 3 (125190321491/250000000000 : ℝ) (500761285971/1000000000000 : ℝ) (100149776299/200000000000 : ℝ) (500748881503/1000000000000 : ℝ) (500755083729/1000000000000 : ℝ) (500755083737/1000000000000 : ℝ) (500755083691/1000000000000 : ℝ) (500755083699/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 4 (500755083729/1000000000000 : ℝ) (500755083737/1000000000000 : ℝ) (500755083691/1000000000000 : ℝ) (500755083699/1000000000000 : ℝ) (50075508371/100000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 5 (50075508371/100000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 6 (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33231/262144 : ℝ))) 7 (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33231/262144 : ℝ)) hmem 8 (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33231/262144 : ℝ))) hcmem 8 (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33231/262144 : ℝ)) (992123984761/1000000000000 : ℝ) (248030996191/250000000000 : ℝ) (500755083709/1000000000000 : ℝ) (250377541859/500000000000 : ℝ) (396414288029/500000000000 : ℝ) (198207144019/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0450_exp_lower
  have heNumeric : (2054902034797/1000000000000 : ℝ)/4 ≤ Real.exp (-21314117950057/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902034797/1000000000000 : ℝ)/4 ≤ Real.exp ((16615/131072 : ℝ)-(198207144019/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16615/131072 : ℝ) (33231/262144 : ℝ) (198207144019/250000000000 : ℝ) (2054902034797/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0451; no trusted numerical premise.
theorem cover8_leaf0451_exp_radius : (499010589448992713/500000000000000000 : ℝ) ≤ Real.exp ((-2077/131072 : ℝ)/8) ∧ Real.exp ((-2077/131072 : ℝ)/8) ≤ (998021178897985427/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2077/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0451_exp_lower : (230028368434180729/250000000000000000 : ℝ) ≤ Real.exp ((-42628237069697/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628237069697/64000000000000 : ℝ)/8) ≤ (920113473736722917/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628237069697/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0451_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725499311/250000000000 : ℝ) ≤ 4*Real.exp (33231/262144 : ℝ)*Real.exp (-mu (radius 8 (2077/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513725499311/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2077/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0451_exp_radius
  have hrNumeric : (49213931943/50000000000 : ℝ) ≤ Real.exp (-2077/131072 : ℝ) ∧ Real.exp (-2077/131072 : ℝ) ≤ (984278638861/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49213931943/50000000000 : ℝ) ≤ (radius 8 (2077/16384 : ℝ)) ∧ (radius 8 (2077/16384 : ℝ)) ≤ (984278638861/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2077/16384 : ℝ)) (49213931943/50000000000 : ℝ) (984278638861/1000000000000 : ℝ) (176622651667/1000000000000 : ℝ) (176622651673/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2077/16384 : ℝ)) (49213931943/50000000000 : ℝ) (984278638861/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49213931943/50000000000 : ℝ) (984278638861/1000000000000 : ℝ) (99213931943/100000000000 : ℝ) (992139319431/1000000000000 : ℝ) (99210817901/100000000000 : ℝ) (248027044753/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 1 (99213931943/100000000000 : ℝ) (992139319431/1000000000000 : ℝ) (99210817901/100000000000 : ℝ) (248027044753/250000000000 : ℝ) (49606187461/50000000000 : ℝ) (496061874611/500000000000 : ℝ) (992123749097/1000000000000 : ℝ) (9921237491/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 2 (49606187461/50000000000 : ℝ) (496061874611/500000000000 : ℝ) (992123749097/1000000000000 : ℝ) (9921237491/10000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 3 (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 4 (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 5 (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 6 (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2077/16384 : ℝ)) 7 (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2077/16384 : ℝ))) (176622651667/1000000000000 : ℝ) (176622651673/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176622651667/1000000000000 : ℝ) (176622651673/1000000000000 : ℝ) (588311325833/1000000000000 : ℝ) (588311325837/1000000000000 : ℝ) (420264977921/1000000000000 : ℝ) (420264977929/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 1 (588311325833/1000000000000 : ℝ) (588311325837/1000000000000 : ℝ) (420264977921/1000000000000 : ℝ) (420264977929/1000000000000 : ℝ) (504288151877/1000000000000 : ℝ) (504288151883/1000000000000 : ℝ) (497239023369/1000000000000 : ℝ) (497239023377/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 2 (504288151877/1000000000000 : ℝ) (504288151883/1000000000000 : ℝ) (497239023369/1000000000000 : ℝ) (497239023377/1000000000000 : ℝ) (500763587623/1000000000000 : ℝ) (50076358763/100000000000 : ℝ) (250375591929/500000000000 : ℝ) (250375591933/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 3 (500763587623/1000000000000 : ℝ) (50076358763/100000000000 : ℝ) (250375591929/500000000000 : ℝ) (250375591933/500000000000 : ℝ) (25037869287/50000000000 : ℝ) (125189346437/250000000000 : ℝ) (250378692851/500000000000 : ℝ) (50075738571/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 4 (25037869287/50000000000 : ℝ) (125189346437/250000000000 : ℝ) (250378692851/500000000000 : ℝ) (50075738571/100000000000 : ℝ) (500757385721/1000000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 5 (500757385721/1000000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 6 (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2077/16384 : ℝ))) 7 (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2077/16384 : ℝ)) hmem 8 (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2077/16384 : ℝ))) hcmem 8 (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2077/16384 : ℝ)) (496061874579/500000000000 : ℝ) (992123749161/1000000000000 : ℝ) (12518934643/25000000000 : ℝ) (500757385729/1000000000000 : ℝ) (792832409031/1000000000000 : ℝ) (99104051131/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0451_exp_lower
  have heNumeric : (513725499311/250000000000 : ℝ)/4 ≤ Real.exp (-42628237069697/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725499311/250000000000 : ℝ)/4 ≤ Real.exp ((33231/262144 : ℝ)-(99104051131/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33231/262144 : ℝ) (2077/16384 : ℝ) (99104051131/125000000000 : ℝ) (513725499311/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0452; no trusted numerical premise.
theorem cover8_leaf0452_exp_radius : (998021119411289353/1000000000000000000 : ℝ) ≤ Real.exp ((-33233/2097152 : ℝ)/8) ∧ Real.exp ((-33233/2097152 : ℝ)/8) ≤ (499010559705644677/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33233/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0452_exp_lower : (230028367910615047/250000000000000000 : ℝ) ≤ Real.exp ((-2664264889691/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664264889691/4000000000000 : ℝ)/8) ≤ (920113471642460189/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664264889691/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0452_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901959827/1000000000000 : ℝ) ≤ 4*Real.exp (2077/16384 : ℝ)*Real.exp (-mu (radius 8 (33233/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901959827/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33233/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0452_exp_radius
  have hrNumeric : (984278169519/1000000000000 : ℝ) ≤ Real.exp (-33233/2097152 : ℝ) ∧ Real.exp (-33233/2097152 : ℝ) ≤ (12303477119/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984278169519/1000000000000 : ℝ) ≤ (radius 8 (33233/262144 : ℝ)) ∧ (radius 8 (33233/262144 : ℝ)) ≤ (12303477119/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33233/262144 : ℝ)) (984278169519/1000000000000 : ℝ) (12303477119/12500000000 : ℝ) (176625267179/1000000000000 : ℝ) (88312633593/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33233/262144 : ℝ)) (984278169519/1000000000000 : ℝ) (12303477119/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984278169519/1000000000000 : ℝ) (12303477119/12500000000 : ℝ) (992139084759/1000000000000 : ℝ) (24803477119/25000000000 : ℝ) (992107942473/1000000000000 : ℝ) (39684317699/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 1 (992139084759/1000000000000 : ℝ) (24803477119/25000000000 : ℝ) (992107942473/1000000000000 : ℝ) (39684317699/40000000000 : ℝ) (62007719601/62500000000 : ℝ) (496061756809/500000000000 : ℝ) (992123513493/1000000000000 : ℝ) (124015439187/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 2 (62007719601/62500000000 : ℝ) (496061756809/500000000000 : ℝ) (992123513493/1000000000000 : ℝ) (124015439187/125000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 3 (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 4 (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 5 (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 6 (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33233/262144 : ℝ)) 7 (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33233/262144 : ℝ))) (176625267179/1000000000000 : ℝ) (88312633593/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176625267179/1000000000000 : ℝ) (88312633593/500000000000 : ℝ) (588312633589/1000000000000 : ℝ) (588312633593/1000000000000 : ℝ) (420268089651/1000000000000 : ℝ) (21013404483/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 1 (588312633589/1000000000000 : ℝ) (588312633593/1000000000000 : ℝ) (420268089651/1000000000000 : ℝ) (21013404483/50000000000 : ℝ) (25214518081/50000000000 : ℝ) (504290361627/1000000000000 : ℝ) (99448283371/200000000000 : ℝ) (497241416863/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 2 (25214518081/50000000000 : ℝ) (504290361627/1000000000000 : ℝ) (99448283371/200000000000 : ℝ) (497241416863/1000000000000 : ℝ) (500765889237/1000000000000 : ℝ) (100153177849/200000000000 : ℝ) (15648546443/31250000000 : ℝ) (100150697237/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 3 (500765889237/1000000000000 : ℝ) (100153177849/200000000000 : ℝ) (15648546443/31250000000 : ℝ) (100150697237/200000000000 : ℝ) (250379843853/500000000000 : ℝ) (100151937543/200000000000 : ℝ) (125189921917/250000000000 : ℝ) (500759687677/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 4 (250379843853/500000000000 : ℝ) (100151937543/200000000000 : ℝ) (125189921917/250000000000 : ℝ) (500759687677/1000000000000 : ℝ) (500759687687/1000000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 5 (500759687687/1000000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 6 (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33233/262144 : ℝ))) 7 (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33233/262144 : ℝ)) hmem 8 (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33233/262144 : ℝ))) hcmem 8 (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33233/262144 : ℝ)) (496061756777/500000000000 : ℝ) (992123513557/1000000000000 : ℝ) (250379843843/500000000000 : ℝ) (31297480481/62500000000 : ℝ) (158567248387/200000000000 : ℝ) (396418120977/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0452_exp_lower
  have heNumeric : (2054901959827/1000000000000 : ℝ)/4 ≤ Real.exp (-2664264889691/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901959827/1000000000000 : ℝ)/4 ≤ Real.exp ((2077/16384 : ℝ)-(396418120977/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2077/16384 : ℝ) (33233/262144 : ℝ) (396418120977/500000000000 : ℝ) (2054901959827/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0453; no trusted numerical premise.
theorem cover8_leaf0453_exp_radius : (39920842396983873/40000000000000000 : ℝ) ≤ Real.exp ((-16617/1048576 : ℝ)/8) ∧ Real.exp ((-16617/1048576 : ℝ)/8) ≤ (499010529962298413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16617/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0453_exp_lower : (460056734779044343/500000000000000000 : ℝ) ≤ Real.exp ((-42628239394911/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628239394911/64000000000000 : ℝ)/8) ≤ (920113469558088687/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628239394911/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0453_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901922587/1000000000000 : ℝ) ≤ 4*Real.exp (33233/262144 : ℝ)*Real.exp (-mu (radius 8 (16617/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901922587/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16617/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0453_exp_radius
  have hrNumeric : (984277700179/1000000000000 : ℝ) ≤ Real.exp (-16617/1048576 : ℝ) ∧ Real.exp (-16617/1048576 : ℝ) ≤ (49213885009/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984277700179/1000000000000 : ℝ) ≤ (radius 8 (16617/131072 : ℝ)) ∧ (radius 8 (16617/131072 : ℝ)) ≤ (49213885009/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16617/131072 : ℝ)) (984277700179/1000000000000 : ℝ) (49213885009/50000000000 : ℝ) (176627882647/1000000000000 : ℝ) (176627882653/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16617/131072 : ℝ)) (984277700179/1000000000000 : ℝ) (49213885009/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984277700179/1000000000000 : ℝ) (49213885009/50000000000 : ℝ) (992138850089/1000000000000 : ℝ) (99213885009/100000000000 : ℝ) (62006731621/62500000000 : ℝ) (496053852969/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 1 (992138850089/1000000000000 : ℝ) (99213885009/100000000000 : ℝ) (62006731621/62500000000 : ℝ) (496053852969/500000000000 : ℝ) (248030819503/250000000000 : ℝ) (496061639007/500000000000 : ℝ) (99212327789/100000000000 : ℝ) (248030819473/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 2 (248030819503/250000000000 : ℝ) (496061639007/500000000000 : ℝ) (99212327789/100000000000 : ℝ) (248030819473/250000000000 : ℝ) (992123277951/1000000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 3 (992123277951/1000000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 4 (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 5 (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 6 (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16617/131072 : ℝ)) 7 (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16617/131072 : ℝ))) (176627882647/1000000000000 : ℝ) (176627882653/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176627882647/1000000000000 : ℝ) (176627882653/1000000000000 : ℝ) (588313941323/1000000000000 : ℝ) (588313941327/1000000000000 : ℝ) (84054240261/200000000000 : ℝ) (420271201313/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 1 (588313941323/1000000000000 : ℝ) (588313941327/1000000000000 : ℝ) (84054240261/200000000000 : ℝ) (420271201313/1000000000000 : ℝ) (252146285657/500000000000 : ℝ) (12607314283/25000000000 : ℝ) (248621905141/500000000000 : ℝ) (497243810289/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 2 (252146285657/500000000000 : ℝ) (12607314283/25000000000 : ℝ) (248621905141/500000000000 : ℝ) (497243810289/1000000000000 : ℝ) (250384095399/500000000000 : ℝ) (100153638161/200000000000 : ℝ) (12518894711/25000000000 : ℝ) (15648618389/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 3 (250384095399/500000000000 : ℝ) (100153638161/200000000000 : ℝ) (12518894711/25000000000 : ℝ) (15648618389/31250000000 : ℝ) (500761989619/1000000000000 : ℝ) (500761989627/1000000000000 : ℝ) (25038099479/50000000000 : ℝ) (500761989589/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 4 (500761989619/1000000000000 : ℝ) (500761989627/1000000000000 : ℝ) (25038099479/50000000000 : ℝ) (500761989589/1000000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 5 (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 6 (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16617/131072 : ℝ))) 7 (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16617/131072 : ℝ)) hmem 8 (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16617/131072 : ℝ))) hcmem 8 (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16617/131072 : ℝ)) (19842465559/20000000000 : ℝ) (992123277953/1000000000000 : ℝ) (500761989599/1000000000000 : ℝ) (62595248701/125000000000 : ℝ) (792840074757/1000000000000 : ℝ) (396420037387/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0453_exp_lower
  have heNumeric : (2054901922587/1000000000000 : ℝ)/4 ≤ Real.exp (-42628239394911/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901922587/1000000000000 : ℝ)/4 ≤ Real.exp ((33233/262144 : ℝ)-(396420037387/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33233/262144 : ℝ) (16617/131072 : ℝ) (396420037387/500000000000 : ℝ) (2054901922587/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0454; no trusted numerical premise.
theorem cover8_leaf0454_exp_radius : (499010500218953921/500000000000000000 : ℝ) ≤ Real.exp ((-33235/2097152 : ℝ)/8) ∧ Real.exp ((-33235/2097152 : ℝ)/8) ≤ (998021000437907843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33235/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0454_exp_lower : (5750709171766083/6250000000000000 : ℝ) ≤ Real.exp ((-21314120274919/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314120274919/32000000000000 : ℝ)/8) ≤ (920113467482573281/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314120274919/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0454_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980377101/200000000000 : ℝ) ≤ 4*Real.exp (16617/131072 : ℝ)*Real.exp (-mu (radius 8 (33235/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980377101/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33235/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0454_exp_radius
  have hrNumeric : (984277230839/1000000000000 : ℝ) ≤ Real.exp (-33235/2097152 : ℝ) ∧ Real.exp (-33235/2097152 : ℝ) ≤ (24606930771/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984277230839/1000000000000 : ℝ) ≤ (radius 8 (33235/262144 : ℝ)) ∧ (radius 8 (33235/262144 : ℝ)) ≤ (24606930771/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33235/262144 : ℝ)) (984277230839/1000000000000 : ℝ) (24606930771/25000000000 : ℝ) (88315249037/500000000000 : ℝ) (1103940613/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33235/262144 : ℝ)) (984277230839/1000000000000 : ℝ) (24606930771/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984277230839/1000000000000 : ℝ) (24606930771/25000000000 : ℝ) (992138615419/1000000000000 : ℝ) (49606930771/50000000000 : ℝ) (992107469399/1000000000000 : ℝ) (992107469401/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 1 (992138615419/1000000000000 : ℝ) (49606930771/50000000000 : ℝ) (992107469399/1000000000000 : ℝ) (992107469401/1000000000000 : ℝ) (992123042409/1000000000000 : ℝ) (992123042411/1000000000000 : ℝ) (496061521143/500000000000 : ℝ) (992123042289/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 2 (992123042409/1000000000000 : ℝ) (992123042411/1000000000000 : ℝ) (496061521143/500000000000 : ℝ) (992123042289/1000000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 3 (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 4 (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 5 (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 6 (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33235/262144 : ℝ)) 7 (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33235/262144 : ℝ))) (88315249037/500000000000 : ℝ) (1103940613/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88315249037/500000000000 : ℝ) (1103940613/6250000000 : ℝ) (588315249037/1000000000000 : ℝ) (7353940613/12500000000 : ℝ) (52534289111/125000000000 : ℝ) (6566786139/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 1 (588315249037/1000000000000 : ℝ) (7353940613/12500000000 : ℝ) (52534289111/125000000000 : ℝ) (6566786139/15625000000 : ℝ) (252147390481/500000000000 : ℝ) (63036847621/125000000000 : ℝ) (62155775457/125000000000 : ℝ) (497246203663/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 2 (252147390481/500000000000 : ℝ) (63036847621/125000000000 : ℝ) (62155775457/125000000000 : ℝ) (497246203663/1000000000000 : ℝ) (500770492309/1000000000000 : ℝ) (125192623079/250000000000 : ℝ) (100151618131/200000000000 : ℝ) (250379045331/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 3 (500770492309/1000000000000 : ℝ) (125192623079/250000000000 : ℝ) (100151618131/200000000000 : ℝ) (250379045331/500000000000 : ℝ) (250382145741/500000000000 : ℝ) (500764291489/1000000000000 : ℝ) (500764291443/1000000000000 : ℝ) (500764291451/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 4 (250382145741/500000000000 : ℝ) (500764291489/1000000000000 : ℝ) (500764291443/1000000000000 : ℝ) (500764291451/1000000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 5 (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 6 (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33235/262144 : ℝ))) 7 (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33235/262144 : ℝ)) hmem 8 (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33235/262144 : ℝ))) hcmem 8 (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33235/262144 : ℝ)) (992123042347/1000000000000 : ℝ) (19842460847/20000000000 : ℝ) (250382145731/500000000000 : ℝ) (50076429147/100000000000 : ℝ) (792843907501/1000000000000 : ℝ) (792843907517/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0454_exp_lower
  have heNumeric : (410980377101/200000000000 : ℝ)/4 ≤ Real.exp (-21314120274919/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980377101/200000000000 : ℝ)/4 ≤ Real.exp ((16617/131072 : ℝ)-(792843907517/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16617/131072 : ℝ) (33235/262144 : ℝ) (792843907517/1000000000000 : ℝ) (410980377101/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0455; no trusted numerical premise.
theorem cover8_leaf0455_exp_radius : (499010470475611203/500000000000000000 : ℝ) ≤ Real.exp ((-8309/524288 : ℝ)/8) ∧ Real.exp ((-8309/524288 : ℝ)/8) ≤ (998020940951222407/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8309/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0455_exp_lower : (230028366353949739/250000000000000000 : ℝ) ≤ Real.exp ((-42628241699901/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628241699901/64000000000000 : ℝ)/8) ≤ (920113465415798957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628241699901/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0455_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901848579/1000000000000 : ℝ) ≤ 4*Real.exp (33235/262144 : ℝ)*Real.exp (-mu (radius 8 (8309/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901848579/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8309/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0455_exp_radius
  have hrNumeric : (984276761499/1000000000000 : ℝ) ≤ Real.exp (-8309/524288 : ℝ) ∧ Real.exp (-8309/524288 : ℝ) ≤ (1968553523/2000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984276761499/1000000000000 : ℝ) ≤ (radius 8 (8309/65536 : ℝ)) ∧ (radius 8 (8309/65536 : ℝ)) ≤ (1968553523/2000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8309/65536 : ℝ)) (984276761499/1000000000000 : ℝ) (1968553523/2000000000 : ℝ) (176633113461/1000000000000 : ℝ) (176633113467/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8309/65536 : ℝ)) (984276761499/1000000000000 : ℝ) (1968553523/2000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984276761499/1000000000000 : ℝ) (1968553523/2000000000 : ℝ) (992138380749/1000000000000 : ℝ) (3968553523/4000000000 : ℝ) (496053616431/500000000000 : ℝ) (31003351027/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 1 (992138380749/1000000000000 : ℝ) (3968553523/4000000000 : ℝ) (496053616431/500000000000 : ℝ) (31003351027/31250000000 : ℝ) (198424561361/200000000000 : ℝ) (992122806807/1000000000000 : ℝ) (992122806683/1000000000000 : ℝ) (198424561337/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 2 (198424561361/200000000000 : ℝ) (992122806807/1000000000000 : ℝ) (992122806683/1000000000000 : ℝ) (198424561337/200000000000 : ℝ) (124015350843/125000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 3 (124015350843/125000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 4 (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 5 (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 6 (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8309/65536 : ℝ)) 7 (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8309/65536 : ℝ))) (176633113461/1000000000000 : ℝ) (176633113467/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176633113461/1000000000000 : ℝ) (176633113467/1000000000000 : ℝ) (58831655673/100000000000 : ℝ) (294158278367/500000000000 : ℝ) (1050693561/2500000000 : ℝ) (52534678051/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 1 (58831655673/100000000000 : ℝ) (294158278367/500000000000 : ℝ) (1050693561/2500000000 : ℝ) (52534678051/125000000000 : ℝ) (100859398113/200000000000 : ℝ) (504296990571/1000000000000 : ℝ) (19889943879/40000000000 : ℝ) (497248596983/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 2 (100859398113/200000000000 : ℝ) (504296990571/1000000000000 : ℝ) (19889943879/40000000000 : ℝ) (497248596983/1000000000000 : ℝ) (50077279377/100000000000 : ℝ) (500772793777/1000000000000 : ℝ) (500760392819/1000000000000 : ℝ) (500760392827/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 3 (50077279377/100000000000 : ℝ) (500772793777/1000000000000 : ℝ) (500760392819/1000000000000 : ℝ) (500760392827/1000000000000 : ℝ) (250383296647/500000000000 : ℝ) (250383296651/500000000000 : ℝ) (62595824157/125000000000 : ℝ) (31297912079/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 4 (250383296647/500000000000 : ℝ) (250383296651/500000000000 : ℝ) (62595824157/125000000000 : ℝ) (31297912079/62500000000 : ℝ) (20030663731/40000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 5 (20030663731/40000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 6 (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8309/65536 : ℝ))) 7 (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8309/65536 : ℝ)) hmem 8 (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8309/65536 : ℝ))) hcmem 8 (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8309/65536 : ℝ)) (992122806743/1000000000000 : ℝ) (496061403373/500000000000 : ℝ) (250383296637/500000000000 : ℝ) (500766593283/1000000000000 : ℝ) (396423870083/500000000000 : ℝ) (99105967523/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0455_exp_lower
  have heNumeric : (2054901848579/1000000000000 : ℝ)/4 ≤ Real.exp (-42628241699901/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901848579/1000000000000 : ℝ)/4 ≤ Real.exp ((33235/262144 : ℝ)-(99105967523/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33235/262144 : ℝ) (8309/65536 : ℝ) (99105967523/125000000000 : ℝ) (2054901848579/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0456; no trusted numerical premise.
theorem cover8_leaf0456_exp_radius : (199604176292908103/200000000000000000 : ℝ) ≤ Real.exp ((-33237/2097152 : ℝ)/8) ∧ Real.exp ((-33237/2097152 : ℝ)/8) ≤ (249505220366135129/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33237/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0456_exp_lower : (920113463357650701/1000000000000000000 : ℝ) ≤ Real.exp ((-10657060711291/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657060711291/16000000000000 : ℝ)/8) ≤ (460056731678825351/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657060711291/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0456_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901811807/1000000000000 : ℝ) ≤ 4*Real.exp (8309/65536 : ℝ)*Real.exp (-mu (radius 8 (33237/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901811807/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33237/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0456_exp_radius
  have hrNumeric : (984276292159/1000000000000 : ℝ) ≤ Real.exp (-33237/2097152 : ℝ) ∧ Real.exp (-33237/2097152 : ℝ) ≤ (3075863413/3125000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984276292159/1000000000000 : ℝ) ≤ (radius 8 (33237/262144 : ℝ)) ∧ (radius 8 (33237/262144 : ℝ)) ≤ (3075863413/3125000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33237/262144 : ℝ)) (984276292159/1000000000000 : ℝ) (3075863413/3125000000 : ℝ) (22079466101/125000000000 : ℝ) (35327145763/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33237/262144 : ℝ)) (984276292159/1000000000000 : ℝ) (3075863413/3125000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984276292159/1000000000000 : ℝ) (3075863413/3125000000 : ℝ) (992138146079/1000000000000 : ℝ) (6200863413/6250000000 : ℝ) (496053498163/500000000000 : ℝ) (992106996327/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 1 (992138146079/1000000000000 : ℝ) (6200863413/6250000000 : ℝ) (496053498163/500000000000 : ℝ) (992106996327/1000000000000 : ℝ) (496061285601/500000000000 : ℝ) (248030642801/250000000000 : ℝ) (24803064277/25000000000 : ℝ) (496061285541/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 2 (496061285601/500000000000 : ℝ) (248030642801/250000000000 : ℝ) (24803064277/25000000000 : ℝ) (496061285541/500000000000 : ℝ) (992122571141/1000000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 3 (992122571141/1000000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 4 (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 5 (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 6 (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33237/262144 : ℝ)) 7 (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33237/262144 : ℝ))) (22079466101/125000000000 : ℝ) (35327145763/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22079466101/125000000000 : ℝ) (35327145763/200000000000 : ℝ) (147079466101/250000000000 : ℝ) (73539733051/125000000000 : ℝ) (210140267921/500000000000 : ℝ) (420280535851/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 1 (147079466101/250000000000 : ℝ) (73539733051/125000000000 : ℝ) (210140267921/500000000000 : ℝ) (420280535851/1000000000000 : ℝ) (504299200123/1000000000000 : ℝ) (50429920013/100000000000 : ℝ) (248625495121/500000000000 : ℝ) (1989003961/4000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 2 (504299200123/1000000000000 : ℝ) (50429920013/100000000000 : ℝ) (248625495121/500000000000 : ℝ) (1989003961/4000000000 : ℝ) (250387547591/500000000000 : ℝ) (50077509519/100000000000 : ℝ) (100152538987/200000000000 : ℝ) (15648834217/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 3 (250387547591/500000000000 : ℝ) (50077509519/100000000000 : ℝ) (100152538987/200000000000 : ℝ) (15648834217/31250000000 : ℝ) (250384447529/500000000000 : ℝ) (500768895067/1000000000000 : ℝ) (25038444751/50000000000 : ℝ) (500768895029/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 4 (250384447529/500000000000 : ℝ) (500768895067/1000000000000 : ℝ) (25038444751/50000000000 : ℝ) (500768895029/1000000000000 : ℝ) (500768895039/1000000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 5 (500768895039/1000000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 6 (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33237/262144 : ℝ))) 7 (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33237/262144 : ℝ)) hmem 8 (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33237/262144 : ℝ))) hcmem 8 (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33237/262144 : ℝ)) (49606128557/50000000000 : ℝ) (992122571143/1000000000000 : ℝ) (250384447519/500000000000 : ℝ) (62596111881/125000000000 : ℝ) (792851572757/1000000000000 : ℝ) (99106446597/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0456_exp_lower
  have heNumeric : (2054901811807/1000000000000 : ℝ)/4 ≤ Real.exp (-10657060711291/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901811807/1000000000000 : ℝ)/4 ≤ Real.exp ((8309/65536 : ℝ)-(99106446597/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8309/65536 : ℝ) (33237/262144 : ℝ) (99106446597/125000000000 : ℝ) (2054901811807/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0457; no trusted numerical premise.
theorem cover8_leaf0457_exp_radius : (998020821977862169/1000000000000000000 : ℝ) ≤ Real.exp ((-16619/1048576 : ℝ)/8) ∧ Real.exp ((-16619/1048576 : ℝ)/8) ≤ (99802082197786217/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16619/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0457_exp_lower : (920113461309393671/1000000000000000000 : ℝ) ≤ Real.exp ((-42628243984923/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628243984923/64000000000000 : ℝ)/8) ≤ (115014182663674209/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628243984923/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0457_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901775211/1000000000000 : ℝ) ≤ 4*Real.exp (33237/262144 : ℝ)*Real.exp (-mu (radius 8 (16619/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901775211/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16619/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0457_exp_radius
  have hrNumeric : (49213791141/50000000000 : ℝ) ≤ Real.exp (-16619/1048576 : ℝ) ∧ Real.exp (-16619/1048576 : ℝ) ≤ (984275822821/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49213791141/50000000000 : ℝ) ≤ (radius 8 (16619/131072 : ℝ)) ∧ (radius 8 (16619/131072 : ℝ)) ≤ (984275822821/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16619/131072 : ℝ)) (49213791141/50000000000 : ℝ) (984275822821/1000000000000 : ℝ) (17663834411/100000000000 : ℝ) (44159586029/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16619/131072 : ℝ)) (49213791141/50000000000 : ℝ) (984275822821/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49213791141/50000000000 : ℝ) (984275822821/1000000000000 : ℝ) (99213791141/100000000000 : ℝ) (992137911411/1000000000000 : ℝ) (992106759789/1000000000000 : ℝ) (99210675979/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 1 (99213791141/100000000000 : ℝ) (992137911411/1000000000000 : ℝ) (992106759789/1000000000000 : ℝ) (99210675979/100000000000 : ℝ) (992122335599/1000000000000 : ℝ) (992122335601/1000000000000 : ℝ) (992122335477/1000000000000 : ℝ) (992122335479/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 2 (992122335599/1000000000000 : ℝ) (992122335601/1000000000000 : ℝ) (992122335477/1000000000000 : ℝ) (992122335479/1000000000000 : ℝ) (496061167769/500000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 3 (496061167769/500000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 4 (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 5 (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 6 (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16619/131072 : ℝ)) 7 (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16619/131072 : ℝ))) (17663834411/100000000000 : ℝ) (44159586029/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17663834411/100000000000 : ℝ) (44159586029/250000000000 : ℝ) (117663834411/200000000000 : ℝ) (294159586029/500000000000 : ℝ) (420283647207/1000000000000 : ℝ) (84056729443/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 1 (117663834411/200000000000 : ℝ) (294159586029/500000000000 : ℝ) (420283647207/1000000000000 : ℝ) (84056729443/200000000000 : ℝ) (504301409631/1000000000000 : ℝ) (504301409637/1000000000000 : ℝ) (9945067669/20000000000 : ℝ) (497253383457/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 2 (504301409631/1000000000000 : ℝ) (504301409637/1000000000000 : ℝ) (9945067669/20000000000 : ℝ) (497253383457/1000000000000 : ℝ) (25038869827/50000000000 : ℝ) (500777396547/1000000000000 : ℝ) (500764996997/1000000000000 : ℝ) (125191249251/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 3 (25038869827/50000000000 : ℝ) (500777396547/1000000000000 : ℝ) (500764996997/1000000000000 : ℝ) (125191249251/250000000000 : ℝ) (15649099899/31250000000 : ℝ) (62596399597/125000000000 : ℝ) (50077119673/100000000000 : ℝ) (250385598369/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 4 (15649099899/31250000000 : ℝ) (62596399597/125000000000 : ℝ) (50077119673/100000000000 : ℝ) (250385598369/500000000000 : ℝ) (500771196749/1000000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 5 (500771196749/1000000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 6 (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16619/131072 : ℝ))) 7 (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16619/131072 : ℝ)) hmem 8 (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16619/131072 : ℝ))) hcmem 8 (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16619/131072 : ℝ)) (992122335537/1000000000000 : ℝ) (49606116777/50000000000 : ℝ) (125192799187/250000000000 : ℝ) (500771196757/1000000000000 : ℝ) (49553462829/62500000000 : ℝ) (396427702641/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0457_exp_lower
  have heNumeric : (2054901775211/1000000000000 : ℝ)/4 ≤ Real.exp (-42628243984923/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901775211/1000000000000 : ℝ)/4 ≤ Real.exp ((33237/262144 : ℝ)-(396427702641/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33237/262144 : ℝ) (16619/131072 : ℝ) (396427702641/500000000000 : ℝ) (2054901775211/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0458; no trusted numerical premise.
theorem cover8_leaf0458_exp_radius : (99802076249118737/100000000000000000 : ℝ) ≤ Real.exp ((-33239/2097152 : ℝ)/8) ∧ Real.exp ((-33239/2097152 : ℝ)/8) ≤ (998020762491187371/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33239/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0458_exp_lower : (920113459269992737/1000000000000000000 : ℝ) ≤ Real.exp ((-21314122559877/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122559877/32000000000000 : ℝ)/8) ≤ (460056729634996369/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122559877/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0458_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196069551/40000000000 : ℝ) ≤ 4*Real.exp (16619/131072 : ℝ)*Real.exp (-mu (radius 8 (33239/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (82196069551/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33239/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0458_exp_radius
  have hrNumeric : (984275353481/1000000000000 : ℝ) ≤ Real.exp (-33239/2097152 : ℝ) ∧ Real.exp (-33239/2097152 : ℝ) ≤ (492137676741/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984275353481/1000000000000 : ℝ) ≤ (radius 8 (33239/262144 : ℝ)) ∧ (radius 8 (33239/262144 : ℝ)) ≤ (492137676741/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33239/262144 : ℝ)) (984275353481/1000000000000 : ℝ) (492137676741/500000000000 : ℝ) (44160239843/250000000000 : ℝ) (88320479689/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33239/262144 : ℝ)) (984275353481/1000000000000 : ℝ) (492137676741/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984275353481/1000000000000 : ℝ) (492137676741/500000000000 : ℝ) (49606883837/50000000000 : ℝ) (992137676741/1000000000000 : ℝ) (248026630813/250000000000 : ℝ) (496053261627/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 1 (49606883837/50000000000 : ℝ) (992137676741/1000000000000 : ℝ) (248026630813/250000000000 : ℝ) (496053261627/500000000000 : ℝ) (248030524999/250000000000 : ℝ) (496061049999/500000000000 : ℝ) (992122099873/1000000000000 : ℝ) (248030524969/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 2 (248030524999/250000000000 : ℝ) (496061049999/500000000000 : ℝ) (992122099873/1000000000000 : ℝ) (248030524969/250000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 3 (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 4 (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 5 (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 6 (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33239/262144 : ℝ)) 7 (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33239/262144 : ℝ))) (44160239843/250000000000 : ℝ) (88320479689/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44160239843/250000000000 : ℝ) (88320479689/500000000000 : ℝ) (294160239843/500000000000 : ℝ) (588320479689/1000000000000 : ℝ) (420286758501/1000000000000 : ℝ) (420286758509/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 1 (294160239843/500000000000 : ℝ) (588320479689/1000000000000 : ℝ) (420286758501/1000000000000 : ℝ) (420286758509/1000000000000 : ℝ) (504303619093/1000000000000 : ℝ) (504303619099/1000000000000 : ℝ) (124313944151/250000000000 : ℝ) (497255776611/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 2 (504303619093/1000000000000 : ℝ) (504303619099/1000000000000 : ℝ) (124313944151/250000000000 : ℝ) (497255776611/1000000000000 : ℝ) (62597462231/125000000000 : ℝ) (100155939571/200000000000 : ℝ) (7824489047/15625000000 : ℝ) (62595912377/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 3 (62597462231/125000000000 : ℝ) (100155939571/200000000000 : ℝ) (7824489047/15625000000 : ℝ) (62595912377/125000000000 : ℝ) (125193374607/250000000000 : ℝ) (125193374609/250000000000 : ℝ) (500773498389/1000000000000 : ℝ) (250386749199/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 4 (125193374607/250000000000 : ℝ) (125193374609/250000000000 : ℝ) (500773498389/1000000000000 : ℝ) (250386749199/500000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 5 (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 6 (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33239/262144 : ℝ))) 7 (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33239/262144 : ℝ)) hmem 8 (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33239/262144 : ℝ))) hcmem 8 (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33239/262144 : ℝ)) (496061049967/500000000000 : ℝ) (992122099937/1000000000000 : ℝ) (62596687301/125000000000 : ℝ) (500773498417/1000000000000 : ℝ) (396429618847/500000000000 : ℝ) (792859237711/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0458_exp_lower
  have heNumeric : (82196069551/40000000000 : ℝ)/4 ≤ Real.exp (-21314122559877/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196069551/40000000000 : ℝ)/4 ≤ Real.exp ((16619/131072 : ℝ)-(792859237711/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16619/131072 : ℝ) (33239/262144 : ℝ) (792859237711/1000000000000 : ℝ) (82196069551/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0459; no trusted numerical premise.
theorem cover8_leaf0459_exp_radius : (249505175751129029/250000000000000000 : ℝ) ≤ Real.exp ((-4155/262144 : ℝ)/8) ∧ Real.exp ((-4155/262144 : ℝ)/8) ≤ (998020703004516117/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4155/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0459_exp_lower : (920113457239217871/1000000000000000000 : ℝ) ≤ Real.exp ((-8525649249957/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525649249957/12800000000000 : ℝ)/8) ≤ (57507091077451117/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525649249957/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0459_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725425623/250000000000 : ℝ) ≤ 4*Real.exp (33239/262144 : ℝ)*Real.exp (-mu (radius 8 (4155/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725425623/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4155/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0459_exp_radius
  have hrNumeric : (492137442071/500000000000 : ℝ) ≤ Real.exp (-4155/262144 : ℝ) ∧ Real.exp (-4155/262144 : ℝ) ≤ (984274884143/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492137442071/500000000000 : ℝ) ≤ (radius 8 (4155/32768 : ℝ)) ∧ (radius 8 (4155/32768 : ℝ)) ≤ (984274884143/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4155/32768 : ℝ)) (492137442071/500000000000 : ℝ) (984274884143/1000000000000 : ℝ) (176643574593/1000000000000 : ℝ) (883217873/5000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4155/32768 : ℝ)) (492137442071/500000000000 : ℝ) (984274884143/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492137442071/500000000000 : ℝ) (984274884143/1000000000000 : ℝ) (992137442071/1000000000000 : ℝ) (124017180259/125000000000 : ℝ) (248026571679/250000000000 : ℝ) (992106286717/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 1 (992137442071/1000000000000 : ℝ) (124017180259/125000000000 : ℝ) (248026571679/250000000000 : ℝ) (992106286717/1000000000000 : ℝ) (992121864393/1000000000000 : ℝ) (198424372879/200000000000 : ℝ) (992121864271/1000000000000 : ℝ) (992121864273/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 2 (992121864393/1000000000000 : ℝ) (198424372879/200000000000 : ℝ) (992121864271/1000000000000 : ℝ) (992121864273/1000000000000 : ℝ) (248030466083/250000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 3 (248030466083/250000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 4 (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 5 (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 6 (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4155/32768 : ℝ)) 7 (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4155/32768 : ℝ))) (176643574593/1000000000000 : ℝ) (883217873/5000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176643574593/1000000000000 : ℝ) (883217873/5000000000 : ℝ) (18385055853/31250000000 : ℝ) (5883217873/10000000000 : ℝ) (105072467431/250000000000 : ℝ) (420289869733/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 1 (18385055853/31250000000 : ℝ) (5883217873/10000000000 : ℝ) (105072467431/250000000000 : ℝ) (420289869733/1000000000000 : ℝ) (50430582851/100000000000 : ℝ) (504305828517/1000000000000 : ℝ) (99451633941/200000000000 : ℝ) (497258169713/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 2 (50430582851/100000000000 : ℝ) (504305828517/1000000000000 : ℝ) (99451633941/200000000000 : ℝ) (497258169713/1000000000000 : ℝ) (500781999107/1000000000000 : ℝ) (100156399823/200000000000 : ℝ) (50076960097/100000000000 : ℝ) (500769600979/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 3 (500781999107/1000000000000 : ℝ) (100156399823/200000000000 : ℝ) (50076960097/100000000000 : ℝ) (500769600979/1000000000000 : ℝ) (250387900019/500000000000 : ℝ) (500775800047/1000000000000 : ℝ) (2503879/5000000 : ℝ) (500775800009/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 4 (250387900019/500000000000 : ℝ) (500775800047/1000000000000 : ℝ) (2503879/5000000 : ℝ) (500775800009/1000000000000 : ℝ) (500775800019/1000000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 5 (500775800019/1000000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 6 (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4155/32768 : ℝ))) 7 (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4155/32768 : ℝ)) hmem 8 (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4155/32768 : ℝ))) hcmem 8 (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4155/32768 : ℝ)) (992121864331/1000000000000 : ℝ) (496060932167/500000000000 : ℝ) (250387900009/500000000000 : ℝ) (125193950007/250000000000 : ℝ) (396431535023/500000000000 : ℝ) (158572614013/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0459_exp_lower
  have heNumeric : (513725425623/250000000000 : ℝ)/4 ≤ Real.exp (-8525649249957/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725425623/250000000000 : ℝ)/4 ≤ Real.exp ((33239/262144 : ℝ)-(158572614013/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33239/262144 : ℝ) (4155/32768 : ℝ) (158572614013/200000000000 : ℝ) (513725425623/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0460; no trusted numerical premise.
theorem cover8_leaf0460_exp_radius : (124752580439731051/125000000000000000 : ℝ) ≤ Real.exp ((-33241/2097152 : ℝ)/8) ∧ Real.exp ((-33241/2097152 : ℝ)/8) ≤ (998020643517848409/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33241/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0460_exp_lower : (920113455217184087/1000000000000000000 : ℝ) ≤ Real.exp ((-5328530921869/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328530921869/8000000000000 : ℝ)/8) ≤ (115014181902148011/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328530921869/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0460_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980333273/200000000000 : ℝ) ≤ 4*Real.exp (4155/32768 : ℝ)*Real.exp (-mu (radius 8 (33241/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980333273/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33241/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0460_exp_radius
  have hrNumeric : (984274414803/1000000000000 : ℝ) ≤ Real.exp (-33241/2097152 : ℝ) ∧ Real.exp (-33241/2097152 : ℝ) ≤ (246068603701/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984274414803/1000000000000 : ℝ) ≤ (radius 8 (33241/262144 : ℝ)) ∧ (radius 8 (33241/262144 : ℝ)) ≤ (246068603701/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33241/262144 : ℝ)) (984274414803/1000000000000 : ℝ) (246068603701/250000000000 : ℝ) (7065847591/40000000000 : ℝ) (88323094891/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33241/262144 : ℝ)) (984274414803/1000000000000 : ℝ) (246068603701/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984274414803/1000000000000 : ℝ) (246068603701/250000000000 : ℝ) (992137207401/1000000000000 : ℝ) (496068603701/500000000000 : ℝ) (992106050179/1000000000000 : ℝ) (992106050181/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 1 (992137207401/1000000000000 : ℝ) (496068603701/500000000000 : ℝ) (992106050179/1000000000000 : ℝ) (992106050181/1000000000000 : ℝ) (99212162879/100000000000 : ℝ) (124015203599/125000000000 : ℝ) (992121628667/1000000000000 : ℝ) (99212162867/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 2 (99212162879/100000000000 : ℝ) (124015203599/125000000000 : ℝ) (992121628667/1000000000000 : ℝ) (99212162867/100000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 3 (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 4 (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 5 (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 6 (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33241/262144 : ℝ)) 7 (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33241/262144 : ℝ))) (7065847591/40000000000 : ℝ) (88323094891/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7065847591/40000000000 : ℝ) (88323094891/500000000000 : ℝ) (588323094887/1000000000000 : ℝ) (588323094891/1000000000000 : ℝ) (420292980877/1000000000000 : ℝ) (210146490443/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 1 (588323094887/1000000000000 : ℝ) (588323094891/1000000000000 : ℝ) (420292980877/1000000000000 : ℝ) (210146490443/500000000000 : ℝ) (252154018941/500000000000 : ℝ) (504308037889/1000000000000 : ℝ) (7769696293/15625000000 : ℝ) (12431514069/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 2 (252154018941/500000000000 : ℝ) (504308037889/1000000000000 : ℝ) (7769696293/15625000000 : ℝ) (12431514069/25000000000 : ℝ) (500784300317/1000000000000 : ℝ) (20031372013/40000000000 : ℝ) (500771902883/1000000000000 : ℝ) (125192975723/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 3 (500784300317/1000000000000 : ℝ) (20031372013/40000000000 : ℝ) (500771902883/1000000000000 : ℝ) (125192975723/250000000000 : ℝ) (625972627/1250000000 : ℝ) (500778101609/1000000000000 : ℝ) (500778101561/1000000000000 : ℝ) (500778101571/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 4 (625972627/1250000000 : ℝ) (500778101609/1000000000000 : ℝ) (500778101561/1000000000000 : ℝ) (500778101571/1000000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 5 (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 6 (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33241/262144 : ℝ))) 7 (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33241/262144 : ℝ)) hmem 8 (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33241/262144 : ℝ))) hcmem 8 (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33241/262144 : ℝ)) (124015203591/125000000000 : ℝ) (992121628731/1000000000000 : ℝ) (25038905079/50000000000 : ℝ) (50077810159/100000000000 : ℝ) (198216725581/250000000000 : ℝ) (792866902343/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0460_exp_lower
  have heNumeric : (410980333273/200000000000 : ℝ)/4 ≤ Real.exp (-5328530921869/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980333273/200000000000 : ℝ)/4 ≤ Real.exp ((4155/32768 : ℝ)-(792866902343/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4155/32768 : ℝ) (33241/262144 : ℝ) (792866902343/1000000000000 : ℝ) (410980333273/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0461; no trusted numerical premise.
theorem cover8_leaf0461_exp_radius : (199604116806236849/200000000000000000 : ℝ) ≤ Real.exp ((-16621/1048576 : ℝ)/8) ∧ Real.exp ((-16621/1048576 : ℝ)/8) ≤ (499010292015592123/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16621/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0461_exp_lower : (920113453205041527/1000000000000000000 : ℝ) ≤ Real.exp ((-8525649698923/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525649698923/12800000000000 : ℝ)/8) ≤ (115014181650630191/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525649698923/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0461_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980326083/200000000000 : ℝ) ≤ 4*Real.exp (33241/262144 : ℝ)*Real.exp (-mu (radius 8 (16621/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980326083/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16621/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0461_exp_radius
  have hrNumeric : (196854789093/200000000000 : ℝ) ≤ Real.exp (-16621/1048576 : ℝ) ∧ Real.exp (-16621/1048576 : ℝ) ≤ (492136972733/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196854789093/200000000000 : ℝ) ≤ (radius 8 (16621/131072 : ℝ)) ∧ (radius 8 (16621/131072 : ℝ)) ≤ (492136972733/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16621/131072 : ℝ)) (196854789093/200000000000 : ℝ) (492136972733/500000000000 : ℝ) (176648804911/1000000000000 : ℝ) (88324402459/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16621/131072 : ℝ)) (196854789093/200000000000 : ℝ) (492136972733/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196854789093/200000000000 : ℝ) (492136972733/500000000000 : ℝ) (248034243183/250000000000 : ℝ) (992136972733/1000000000000 : ℝ) (992105813643/1000000000000 : ℝ) (248026453411/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 1 (248034243183/250000000000 : ℝ) (992136972733/1000000000000 : ℝ) (992105813643/1000000000000 : ℝ) (248026453411/250000000000 : ℝ) (992121393187/1000000000000 : ℝ) (992121393189/1000000000000 : ℝ) (198424278613/200000000000 : ℝ) (992121393067/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 2 (992121393187/1000000000000 : ℝ) (992121393189/1000000000000 : ℝ) (198424278613/200000000000 : ℝ) (992121393067/1000000000000 : ℝ) (496060696563/500000000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 3 (496060696563/500000000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 4 (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 5 (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 6 (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16621/131072 : ℝ)) 7 (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16621/131072 : ℝ))) (176648804911/1000000000000 : ℝ) (88324402459/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176648804911/1000000000000 : ℝ) (88324402459/500000000000 : ℝ) (117664880491/200000000000 : ℝ) (588324402459/1000000000000 : ℝ) (420296091953/1000000000000 : ℝ) (210148045981/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 1 (117664880491/200000000000 : ℝ) (588324402459/1000000000000 : ℝ) (420296091953/1000000000000 : ℝ) (210148045981/500000000000 : ℝ) (126077561801/250000000000 : ℝ) (504310247211/1000000000000 : ℝ) (497262955741/1000000000000 : ℝ) (497262955749/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 2 (126077561801/250000000000 : ℝ) (504310247211/1000000000000 : ℝ) (497262955741/1000000000000 : ℝ) (497262955749/1000000000000 : ℝ) (978098831/1953125000 : ℝ) (12519665037/25000000000 : ℝ) (250387102371/500000000000 : ℝ) (2003096819/4000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 3 (978098831/1953125000 : ℝ) (12519665037/25000000000 : ℝ) (250387102371/500000000000 : ℝ) (2003096819/4000000000 : ℝ) (500780403107/1000000000000 : ℝ) (100156080623/200000000000 : ℝ) (125195100767/250000000000 : ℝ) (500780403077/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 4 (500780403107/1000000000000 : ℝ) (100156080623/200000000000 : ℝ) (125195100767/250000000000 : ℝ) (500780403077/1000000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 5 (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 6 (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16621/131072 : ℝ))) 7 (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16621/131072 : ℝ)) hmem 8 (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16621/131072 : ℝ))) hcmem 8 (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16621/131072 : ℝ)) (1587394229/1600000000 : ℝ) (124015174141/125000000000 : ℝ) (500780403087/1000000000000 : ℝ) (62597550387/125000000000 : ℝ) (792870734517/1000000000000 : ℝ) (158574146907/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0461_exp_lower
  have heNumeric : (410980326083/200000000000 : ℝ)/4 ≤ Real.exp (-8525649698923/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980326083/200000000000 : ℝ)/4 ≤ Real.exp ((33241/262144 : ℝ)-(158574146907/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33241/262144 : ℝ) (16621/131072 : ℝ) (158574146907/200000000000 : ℝ) (410980326083/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0462; no trusted numerical premise.
theorem cover8_leaf0462_exp_radius : (249505131136130907/250000000000000000 : ℝ) ≤ Real.exp ((-33243/2097152 : ℝ)/8) ∧ Real.exp ((-33243/2097152 : ℝ)/8) ≤ (998020524544523629/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33243/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0462_exp_lower : (920113451200604923/1000000000000000000 : ℝ) ≤ Real.exp ((-4262824960999/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262824960999/6400000000000 : ℝ)/8) ≤ (230028362800151231/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262824960999/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0462_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901594603/1000000000000 : ℝ) ≤ 4*Real.exp (16621/131072 : ℝ)*Real.exp (-mu (radius 8 (33243/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901594603/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33243/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0462_exp_radius
  have hrNumeric : (492136738063/500000000000 : ℝ) ≤ Real.exp (-33243/2097152 : ℝ) ∧ Real.exp (-33243/2097152 : ℝ) ≤ (984273476127/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492136738063/500000000000 : ℝ) ≤ (radius 8 (33243/262144 : ℝ)) ∧ (radius 8 (33243/262144 : ℝ)) ≤ (984273476127/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33243/262144 : ℝ)) (492136738063/500000000000 : ℝ) (984273476127/1000000000000 : ℝ) (176651420013/1000000000000 : ℝ) (8832571001/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33243/262144 : ℝ)) (492136738063/500000000000 : ℝ) (984273476127/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492136738063/500000000000 : ℝ) (984273476127/1000000000000 : ℝ) (992136738063/1000000000000 : ℝ) (62008546129/62500000000 : ℝ) (496052788553/500000000000 : ℝ) (248026394277/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 1 (992136738063/1000000000000 : ℝ) (62008546129/62500000000 : ℝ) (496052788553/500000000000 : ℝ) (248026394277/250000000000 : ℝ) (62007572349/62500000000 : ℝ) (496060578793/500000000000 : ℝ) (496060578731/500000000000 : ℝ) (124015144683/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 2 (62007572349/62500000000 : ℝ) (496060578793/500000000000 : ℝ) (496060578731/500000000000 : ℝ) (124015144683/125000000000 : ℝ) (992121157523/1000000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 3 (992121157523/1000000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 4 (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 5 (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 6 (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33243/262144 : ℝ)) 7 (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33243/262144 : ℝ))) (176651420013/1000000000000 : ℝ) (8832571001/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176651420013/1000000000000 : ℝ) (8832571001/50000000000 : ℝ) (294162855003/500000000000 : ℝ) (58832571001/100000000000 : ℝ) (105074800741/250000000000 : ℝ) (210149601487/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 1 (294162855003/500000000000 : ℝ) (58832571001/100000000000 : ℝ) (105074800741/250000000000 : ℝ) (210149601487/500000000000 : ℝ) (100862491297/200000000000 : ℝ) (126078114123/250000000000 : ℝ) (12431633717/25000000000 : ℝ) (497265348689/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 2 (100862491297/200000000000 : ℝ) (126078114123/250000000000 : ℝ) (12431633717/25000000000 : ℝ) (497265348689/1000000000000 : ℝ) (250394451291/500000000000 : ℝ) (500788902591/1000000000000 : ℝ) (100155301311/200000000000 : ℝ) (125194126641/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 3 (250394451291/500000000000 : ℝ) (500788902591/1000000000000 : ℝ) (100155301311/200000000000 : ℝ) (125194126641/250000000000 : ℝ) (62597838071/125000000000 : ℝ) (250391352289/500000000000 : ℝ) (50078270453/100000000000 : ℝ) (25039135227/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 4 (62597838071/125000000000 : ℝ) (250391352289/500000000000 : ℝ) (50078270453/100000000000 : ℝ) (25039135227/50000000000 : ℝ) (500782704549/1000000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 5 (500782704549/1000000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 6 (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33243/262144 : ℝ))) 7 (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33243/262144 : ℝ)) hmem 8 (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33243/262144 : ℝ))) hcmem 8 (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33243/262144 : ℝ)) (496060578761/500000000000 : ℝ) (39684846301/40000000000 : ℝ) (125195676137/250000000000 : ℝ) (500782704559/1000000000000 : ℝ) (792874566639/1000000000000 : ℝ) (39643728333/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0462_exp_lower
  have heNumeric : (2054901594603/1000000000000 : ℝ)/4 ≤ Real.exp (-4262824960999/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901594603/1000000000000 : ℝ)/4 ≤ Real.exp ((16621/131072 : ℝ)-(39643728333/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16621/131072 : ℝ) (33243/262144 : ℝ) (39643728333/50000000000 : ℝ) (2054901594603/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0463; no trusted numerical premise.
theorem cover8_leaf0463_exp_radius : (998020465057866557/1000000000000000000 : ℝ) ≤ Real.exp ((-8311/524288 : ℝ)/8) ∧ Real.exp ((-8311/524288 : ℝ)/8) ≤ (499010232528933279/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8311/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0463_exp_lower : (92011344920628957/100000000000000000 : ℝ) ≤ Real.exp ((-42628250719733/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250719733/64000000000000 : ℝ)/8) ≤ (920113449206289571/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250719733/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0463_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901558971/1000000000000 : ℝ) ≤ 4*Real.exp (33243/262144 : ℝ)*Real.exp (-mu (radius 8 (8311/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901558971/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8311/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0463_exp_radius
  have hrNumeric : (246068251697/250000000000 : ℝ) ≤ Real.exp (-8311/524288 : ℝ) ∧ Real.exp (-8311/524288 : ℝ) ≤ (984273006789/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246068251697/250000000000 : ℝ) ≤ (radius 8 (8311/65536 : ℝ)) ∧ (radius 8 (8311/65536 : ℝ)) ≤ (984273006789/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8311/65536 : ℝ)) (246068251697/250000000000 : ℝ) (984273006789/1000000000000 : ℝ) (17665403507/100000000000 : ℝ) (44163508769/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8311/65536 : ℝ)) (246068251697/250000000000 : ℝ) (984273006789/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246068251697/250000000000 : ℝ) (984273006789/1000000000000 : ℝ) (496068251697/500000000000 : ℝ) (198427300679/200000000000 : ℝ) (99210534057/100000000000 : ℝ) (992105340571/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 1 (496068251697/500000000000 : ℝ) (198427300679/200000000000 : ℝ) (99210534057/100000000000 : ℝ) (992105340571/1000000000000 : ℝ) (496060460991/500000000000 : ℝ) (992120921983/1000000000000 : ℝ) (992120921859/1000000000000 : ℝ) (992120921861/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 2 (496060460991/500000000000 : ℝ) (992120921983/1000000000000 : ℝ) (992120921859/1000000000000 : ℝ) (992120921861/1000000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 3 (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 4 (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 5 (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 6 (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8311/65536 : ℝ)) 7 (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8311/65536 : ℝ))) (17665403507/100000000000 : ℝ) (44163508769/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17665403507/100000000000 : ℝ) (44163508769/250000000000 : ℝ) (117665403507/200000000000 : ℝ) (294163508769/500000000000 : ℝ) (4203023139/10000000000 : ℝ) (105075578477/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 1 (117665403507/200000000000 : ℝ) (294163508769/500000000000 : ℝ) (4203023139/10000000000 : ℝ) (105075578477/250000000000 : ℝ) (504314665717/1000000000000 : ℝ) (504314665723/1000000000000 : ℝ) (497267741563/1000000000000 : ℝ) (49726774157/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 2 (504314665717/1000000000000 : ℝ) (504314665723/1000000000000 : ℝ) (497267741563/1000000000000 : ℝ) (49726774157/100000000000 : ℝ) (12519780091/25000000000 : ℝ) (500791203647/1000000000000 : ℝ) (100155761663/200000000000 : ℝ) (500778808323/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 3 (12519780091/25000000000 : ℝ) (500791203647/1000000000000 : ℝ) (100155761663/200000000000 : ℝ) (500778808323/1000000000000 : ℝ) (500785005977/1000000000000 : ℝ) (100157001197/200000000000 : ℝ) (500785005939/1000000000000 : ℝ) (500785005947/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 4 (500785005977/1000000000000 : ℝ) (100157001197/200000000000 : ℝ) (500785005939/1000000000000 : ℝ) (500785005947/1000000000000 : ℝ) (250392502979/500000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 5 (250392502979/500000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 6 (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8311/65536 : ℝ))) 7 (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8311/65536 : ℝ)) hmem 8 (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8311/65536 : ℝ))) hcmem 8 (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8311/65536 : ℝ)) (3100377881/3125000000 : ℝ) (496060460961/500000000000 : ℝ) (500785005957/1000000000000 : ℝ) (250392502983/500000000000 : ℝ) (19821959967/25000000000 : ℝ) (792878398697/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0463_exp_lower
  have heNumeric : (2054901558971/1000000000000 : ℝ)/4 ≤ Real.exp (-42628250719733/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901558971/1000000000000 : ℝ)/4 ≤ Real.exp ((33243/262144 : ℝ)-(792878398697/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33243/262144 : ℝ) (8311/65536 : ℝ) (792878398697/1000000000000 : ℝ) (2054901558971/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0464; no trusted numerical premise.
theorem cover8_leaf0464_exp_radius : (124752550696401629/125000000000000000 : ℝ) ≤ Real.exp ((-33245/2097152 : ℝ)/8) ∧ Real.exp ((-33245/2097152 : ℝ)/8) ≤ (998020405571213033/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33245/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0464_exp_lower : (230028361805035057/250000000000000000 : ℝ) ≤ Real.exp ((-10657062956233/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062956233/16000000000000 : ℝ)/8) ≤ (920113447220140229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062956233/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0464_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450761743/500000000000 : ℝ) ≤ 4*Real.exp (8311/65536 : ℝ)*Real.exp (-mu (radius 8 (33245/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450761743/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33245/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0464_exp_radius
  have hrNumeric : (19685450749/20000000000 : ℝ) ≤ Real.exp (-33245/2097152 : ℝ) ∧ Real.exp (-33245/2097152 : ℝ) ≤ (984272537451/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19685450749/20000000000 : ℝ) ≤ (radius 8 (33245/262144 : ℝ)) ∧ (radius 8 (33245/262144 : ℝ)) ≤ (984272537451/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33245/262144 : ℝ)) (19685450749/20000000000 : ℝ) (984272537451/1000000000000 : ℝ) (88328325043/500000000000 : ℝ) (176656650093/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33245/262144 : ℝ)) (19685450749/20000000000 : ℝ) (984272537451/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19685450749/20000000000 : ℝ) (984272537451/1000000000000 : ℝ) (39685450749/40000000000 : ℝ) (496068134363/500000000000 : ℝ) (992105104033/1000000000000 : ℝ) (198421020807/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 1 (39685450749/40000000000 : ℝ) (496068134363/500000000000 : ℝ) (992105104033/1000000000000 : ℝ) (198421020807/200000000000 : ℝ) (992120686379/1000000000000 : ℝ) (992120686381/1000000000000 : ℝ) (62007542891/62500000000 : ℝ) (992120686259/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 2 (992120686379/1000000000000 : ℝ) (992120686381/1000000000000 : ℝ) (62007542891/62500000000 : ℝ) (992120686259/1000000000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 3 (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 4 (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 5 (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 6 (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33245/262144 : ℝ)) 7 (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33245/262144 : ℝ))) (88328325043/500000000000 : ℝ) (176656650093/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88328325043/500000000000 : ℝ) (176656650093/1000000000000 : ℝ) (588328325043/1000000000000 : ℝ) (588328325047/1000000000000 : ℝ) (420305424763/1000000000000 : ℝ) (420305424773/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 1 (588328325043/1000000000000 : ℝ) (588328325047/1000000000000 : ℝ) (420305424763/1000000000000 : ℝ) (420305424773/1000000000000 : ℝ) (504316874903/1000000000000 : ℝ) (50431687491/100000000000 : ℝ) (497270134391/1000000000000 : ℝ) (497270134399/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 2 (504316874903/1000000000000 : ℝ) (50431687491/100000000000 : ℝ) (497270134391/1000000000000 : ℝ) (497270134399/1000000000000 : ℝ) (500793504647/1000000000000 : ℝ) (100158700931/200000000000 : ℝ) (20031244401/40000000000 : ℝ) (250390555017/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 3 (500793504647/1000000000000 : ℝ) (100158700931/200000000000 : ℝ) (20031244401/40000000000 : ℝ) (250390555017/500000000000 : ℝ) (62598413417/125000000000 : ℝ) (100157461469/200000000000 : ℝ) (500787307297/1000000000000 : ℝ) (500787307307/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 4 (62598413417/125000000000 : ℝ) (100157461469/200000000000 : ℝ) (500787307297/1000000000000 : ℝ) (500787307307/1000000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 5 (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 6 (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33245/262144 : ℝ))) 7 (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33245/262144 : ℝ)) hmem 8 (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33245/262144 : ℝ))) hcmem 8 (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33245/262144 : ℝ)) (992120686317/1000000000000 : ℝ) (12401508579/12500000000 : ℝ) (125196826829/250000000000 : ℝ) (250393653663/500000000000 : ℝ) (198220557661/250000000000 : ℝ) (792882230663/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0464_exp_lower
  have heNumeric : (1027450761743/500000000000 : ℝ)/4 ≤ Real.exp (-10657062956233/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450761743/500000000000 : ℝ)/4 ≤ Real.exp ((8311/65536 : ℝ)-(792882230663/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8311/65536 : ℝ) (33245/262144 : ℝ) (792882230663/1000000000000 : ℝ) (1027450761743/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0465; no trusted numerical premise.
theorem cover8_leaf0465_exp_radius : (249505086521140763/250000000000000000 : ℝ) ≤ Real.exp ((-16623/1048576 : ℝ)/8) ∧ Real.exp ((-16623/1048576 : ℝ)/8) ≤ (998020346084563053/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16623/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0465_exp_lower : (920113445244227153/1000000000000000000 : ℝ) ≤ Real.exp ((-8525650584887/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525650584887/12800000000000 : ℝ)/8) ≤ (460056722622113577/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525650584887/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0465_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901488183/1000000000000 : ℝ) ≤ 4*Real.exp (33245/262144 : ℝ)*Real.exp (-mu (radius 8 (16623/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901488183/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16623/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0465_exp_radius
  have hrNumeric : (984272068113/1000000000000 : ℝ) ≤ Real.exp (-16623/1048576 : ℝ) ∧ Real.exp (-16623/1048576 : ℝ) ≤ (492136034057/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984272068113/1000000000000 : ℝ) ≤ (radius 8 (16623/131072 : ℝ)) ∧ (radius 8 (16623/131072 : ℝ)) ≤ (492136034057/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16623/131072 : ℝ)) (984272068113/1000000000000 : ℝ) (492136034057/500000000000 : ℝ) (176659265057/1000000000000 : ℝ) (176659265063/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16623/131072 : ℝ)) (984272068113/1000000000000 : ℝ) (492136034057/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984272068113/1000000000000 : ℝ) (492136034057/500000000000 : ℝ) (124017004257/125000000000 : ℝ) (992136034057/1000000000000 : ℝ) (992104867497/1000000000000 : ℝ) (992104867499/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 1 (124017004257/125000000000 : ℝ) (992136034057/1000000000000 : ℝ) (992104867497/1000000000000 : ℝ) (992104867499/1000000000000 : ℝ) (124015056347/125000000000 : ℝ) (496060225389/500000000000 : ℝ) (496060225327/500000000000 : ℝ) (31003764083/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 2 (124015056347/125000000000 : ℝ) (496060225389/500000000000 : ℝ) (496060225327/500000000000 : ℝ) (31003764083/31250000000 : ℝ) (198424090143/200000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 3 (198424090143/200000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 4 (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 5 (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 6 (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16623/131072 : ℝ)) 7 (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16623/131072 : ℝ))) (176659265057/1000000000000 : ℝ) (176659265063/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176659265057/1000000000000 : ℝ) (176659265063/1000000000000 : ℝ) (36770602033/62500000000 : ℝ) (147082408133/250000000000 : ℝ) (8406170711/20000000000 : ℝ) (420308535559/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 1 (36770602033/62500000000 : ℝ) (147082408133/250000000000 : ℝ) (8406170711/20000000000 : ℝ) (420308535559/1000000000000 : ℝ) (504319084039/1000000000000 : ℝ) (252159542023/500000000000 : ℝ) (12431813179/25000000000 : ℝ) (7769883237/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 2 (504319084039/1000000000000 : ℝ) (252159542023/500000000000 : ℝ) (12431813179/25000000000 : ℝ) (7769883237/15625000000 : ℝ) (500795805599/1000000000000 : ℝ) (500795805607/1000000000000 : ℝ) (500783411681/1000000000000 : ℝ) (500783411689/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 3 (500795805599/1000000000000 : ℝ) (500795805607/1000000000000 : ℝ) (500783411681/1000000000000 : ℝ) (500783411689/1000000000000 : ℝ) (1564967527/3125000000 : ℝ) (62598701081/125000000000 : ℝ) (500789608601/1000000000000 : ℝ) (50078960861/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 4 (1564967527/3125000000 : ℝ) (62598701081/125000000000 : ℝ) (500789608601/1000000000000 : ℝ) (50078960861/100000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 5 (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 6 (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16623/131072 : ℝ))) 7 (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16623/131072 : ℝ)) hmem 8 (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16623/131072 : ℝ))) hcmem 8 (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16623/131072 : ℝ)) (496060225357/500000000000 : ℝ) (992120450717/1000000000000 : ℝ) (25039480431/50000000000 : ℝ) (500789608629/1000000000000 : ℝ) (396443031261/500000000000 : ℝ) (39644303127/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0465_exp_lower
  have heNumeric : (2054901488183/1000000000000 : ℝ)/4 ≤ Real.exp (-8525650584887/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901488183/1000000000000 : ℝ)/4 ≤ Real.exp ((33245/262144 : ℝ)-(39644303127/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33245/262144 : ℝ) (16623/131072 : ℝ) (39644303127/50000000000 : ℝ) (2054901488183/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0466; no trusted numerical premise.
theorem cover8_leaf0466_exp_radius : (499010143298958309/500000000000000000 : ℝ) ≤ Real.exp ((-33247/2097152 : ℝ)/8) ∧ Real.exp ((-33247/2097152 : ℝ)/8) ≤ (998020286597916619/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33247/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0466_exp_lower : (14376772551187813/15625000000000000 : ℝ) ≤ Real.exp ((-852565080393/1280000000000 : ℝ)/8) ∧ Real.exp ((-852565080393/1280000000000 : ℝ)/8) ≤ (920113443276020033/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-852565080393/1280000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0466_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450726509/500000000000 : ℝ) ≤ 4*Real.exp (16623/131072 : ℝ)*Real.exp (-mu (radius 8 (33247/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450726509/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33247/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0466_exp_radius
  have hrNumeric : (39370863951/40000000000 : ℝ) ≤ Real.exp (-33247/2097152 : ℝ) ∧ Real.exp (-33247/2097152 : ℝ) ≤ (123033949847/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39370863951/40000000000 : ℝ) ≤ (radius 8 (33247/262144 : ℝ)) ∧ (radius 8 (33247/262144 : ℝ)) ≤ (123033949847/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33247/262144 : ℝ)) (39370863951/40000000000 : ℝ) (123033949847/125000000000 : ℝ) (176661879993/1000000000000 : ℝ) (4416547/25000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33247/262144 : ℝ)) (39370863951/40000000000 : ℝ) (123033949847/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39370863951/40000000000 : ℝ) (123033949847/125000000000 : ℝ) (992135799387/1000000000000 : ℝ) (248033949847/250000000000 : ℝ) (992104630961/1000000000000 : ℝ) (496052315481/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 1 (992135799387/1000000000000 : ℝ) (248033949847/250000000000 : ℝ) (992104630961/1000000000000 : ℝ) (496052315481/500000000000 : ℝ) (496060107587/500000000000 : ℝ) (39684808607/40000000000 : ℝ) (992120215051/1000000000000 : ℝ) (992120215053/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 2 (496060107587/500000000000 : ℝ) (39684808607/40000000000 : ℝ) (992120215051/1000000000000 : ℝ) (992120215053/1000000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 3 (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 4 (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 5 (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 6 (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33247/262144 : ℝ)) 7 (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33247/262144 : ℝ))) (176661879993/1000000000000 : ℝ) (4416547/25000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176661879993/1000000000000 : ℝ) (4416547/25000000 : ℝ) (147082734999/250000000000 : ℝ) (29416547/50000000 : ℝ) (420311646273/1000000000000 : ℝ) (210155823141/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 1 (147082734999/250000000000 : ℝ) (29416547/50000000 : ℝ) (420311646273/1000000000000 : ℝ) (210155823141/500000000000 : ℝ) (252160646567/500000000000 : ℝ) (504321293141/1000000000000 : ℝ) (497274919881/1000000000000 : ℝ) (497274919889/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 2 (252160646567/500000000000 : ℝ) (504321293141/1000000000000 : ℝ) (497274919881/1000000000000 : ℝ) (497274919889/1000000000000 : ℝ) (500798106507/1000000000000 : ℝ) (100159621303/200000000000 : ℝ) (125196428323/250000000000 : ℝ) (5007857133/10000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 3 (500798106507/1000000000000 : ℝ) (100159621303/200000000000 : ℝ) (125196428323/250000000000 : ℝ) (5007857133/10000000000 : ℝ) (500791909899/1000000000000 : ℝ) (125197977477/250000000000 : ℝ) (500791909861/1000000000000 : ℝ) (50079190987/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 4 (500791909899/1000000000000 : ℝ) (125197977477/250000000000 : ℝ) (500791909861/1000000000000 : ℝ) (50079190987/100000000000 : ℝ) (12519797747/25000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 5 (12519797747/25000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 6 (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33247/262144 : ℝ))) 7 (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33247/262144 : ℝ)) hmem 8 (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33247/262144 : ℝ))) hcmem 8 (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33247/262144 : ℝ)) (124015026889/125000000000 : ℝ) (496060107557/500000000000 : ℝ) (500791909879/1000000000000 : ℝ) (500791909889/1000000000000 : ℝ) (198222473583/250000000000 : ℝ) (15857797887/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0466_exp_lower
  have heNumeric : (1027450726509/500000000000 : ℝ)/4 ≤ Real.exp (-852565080393/1280000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450726509/500000000000 : ℝ)/4 ≤ Real.exp ((16623/131072 : ℝ)-(15857797887/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16623/131072 : ℝ) (33247/262144 : ℝ) (15857797887/20000000000 : ℝ) (1027450726509/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0467; no trusted numerical premise.
theorem cover8_leaf0467_exp_radius : (998020227111273729/1000000000000000000 : ℝ) ≤ Real.exp ((-1039/65536 : ℝ)/8) ∧ Real.exp ((-1039/65536 : ℝ)/8) ≤ (99802022711127373/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1039/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0467_exp_lower : (920113441317359093/1000000000000000000 : ℝ) ≤ Real.exp ((-42628255109553/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628255109553/64000000000000 : ℝ)/8) ≤ (460056720658679547/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628255109553/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0467_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862677253/125000000000 : ℝ) ≤ 4*Real.exp (33247/262144 : ℝ)*Real.exp (-mu (radius 8 (1039/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256862677253/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1039/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0467_exp_radius
  have hrNumeric : (492135564719/500000000000 : ℝ) ≤ Real.exp (-1039/65536 : ℝ) ∧ Real.exp (-1039/65536 : ℝ) ≤ (984271129439/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492135564719/500000000000 : ℝ) ≤ (radius 8 (1039/8192 : ℝ)) ∧ (radius 8 (1039/8192 : ℝ)) ≤ (984271129439/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1039/8192 : ℝ)) (492135564719/500000000000 : ℝ) (984271129439/1000000000000 : ℝ) (44166123721/250000000000 : ℝ) (176664494891/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1039/8192 : ℝ)) (492135564719/500000000000 : ℝ) (984271129439/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492135564719/500000000000 : ℝ) (984271129439/1000000000000 : ℝ) (992135564719/1000000000000 : ℝ) (12401694559/12500000000 : ℝ) (39684175777/40000000000 : ℝ) (496052197213/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 1 (992135564719/1000000000000 : ℝ) (12401694559/12500000000 : ℝ) (39684175777/40000000000 : ℝ) (496052197213/500000000000 : ℝ) (248029994893/250000000000 : ℝ) (992119979573/1000000000000 : ℝ) (992119979449/1000000000000 : ℝ) (992119979451/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 2 (248029994893/250000000000 : ℝ) (992119979573/1000000000000 : ℝ) (992119979449/1000000000000 : ℝ) (992119979451/1000000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 3 (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 4 (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 5 (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 6 (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1039/8192 : ℝ)) 7 (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1039/8192 : ℝ))) (44166123721/250000000000 : ℝ) (176664494891/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44166123721/250000000000 : ℝ) (176664494891/1000000000000 : ℝ) (294166123721/500000000000 : ℝ) (294166123723/500000000000 : ℝ) (420314756919/1000000000000 : ℝ) (6567418077/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 1 (294166123721/500000000000 : ℝ) (294166123723/500000000000 : ℝ) (420314756919/1000000000000 : ℝ) (6567418077/15625000000 : ℝ) (25216175109/50000000000 : ℝ) (504323502187/1000000000000 : ℝ) (15539916017/31250000000 : ℝ) (62159664069/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 2 (25216175109/50000000000 : ℝ) (504323502187/1000000000000 : ℝ) (15539916017/31250000000 : ℝ) (62159664069/125000000000 : ℝ) (250400203681/500000000000 : ℝ) (50080040737/100000000000 : ℝ) (500788014849/1000000000000 : ℝ) (500788014857/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 3 (250400203681/500000000000 : ℝ) (50080040737/100000000000 : ℝ) (500788014849/1000000000000 : ℝ) (500788014857/1000000000000 : ℝ) (100158842221/200000000000 : ℝ) (250397105557/500000000000 : ℝ) (500794211067/1000000000000 : ℝ) (125198552769/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 4 (100158842221/200000000000 : ℝ) (250397105557/500000000000 : ℝ) (500794211067/1000000000000 : ℝ) (125198552769/250000000000 : ℝ) (250397105543/500000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 5 (250397105543/500000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 6 (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1039/8192 : ℝ))) 7 (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1039/8192 : ℝ)) hmem 8 (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1039/8192 : ℝ))) hcmem 8 (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1039/8192 : ℝ)) (99211997951/100000000000 : ℝ) (124014997439/125000000000 : ℝ) (100158842217/200000000000 : ℝ) (100158842219/200000000000 : ℝ) (396446863029/500000000000 : ℝ) (792893726077/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0467_exp_lower
  have heNumeric : (256862677253/125000000000 : ℝ)/4 ≤ Real.exp (-42628255109553/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862677253/125000000000 : ℝ)/4 ≤ Real.exp ((33247/262144 : ℝ)-(792893726077/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33247/262144 : ℝ) (1039/8192 : ℝ) (792893726077/1000000000000 : ℝ) (256862677253/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0468; no trusted numerical premise.
theorem cover8_leaf0468_exp_radius : (499010083812317193/500000000000000000 : ℝ) ≤ Real.exp ((-33249/2097152 : ℝ)/8) ∧ Real.exp ((-33249/2097152 : ℝ)/8) ≤ (998020167624634387/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33249/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0468_exp_lower : (920113439367784277/1000000000000000000 : ℝ) ≤ Real.exp ((-53285320243/80000000000 : ℝ)/8) ∧ Real.exp ((-53285320243/80000000000 : ℝ)/8) ≤ (460056719683892139/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-53285320243/80000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0468_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862672899/125000000000 : ℝ) ≤ 4*Real.exp (1039/8192 : ℝ)*Real.exp (-mu (radius 8 (33249/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862672899/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33249/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0468_exp_radius
  have hrNumeric : (984270660101/1000000000000 : ℝ) ≤ Real.exp (-33249/2097152 : ℝ) ∧ Real.exp (-33249/2097152 : ℝ) ≤ (492135330051/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984270660101/1000000000000 : ℝ) ≤ (radius 8 (33249/262144 : ℝ)) ∧ (radius 8 (33249/262144 : ℝ)) ≤ (492135330051/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33249/262144 : ℝ)) (984270660101/1000000000000 : ℝ) (492135330051/500000000000 : ℝ) (35333421947/200000000000 : ℝ) (88333554871/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33249/262144 : ℝ)) (984270660101/1000000000000 : ℝ) (492135330051/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984270660101/1000000000000 : ℝ) (492135330051/500000000000 : ℝ) (19842706601/20000000000 : ℝ) (992135330051/1000000000000 : ℝ) (992104157889/1000000000000 : ℝ) (99210415789/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 1 (19842706601/20000000000 : ℝ) (992135330051/1000000000000 : ℝ) (992104157889/1000000000000 : ℝ) (99210415789/100000000000 : ℝ) (992119743969/1000000000000 : ℝ) (992119743971/1000000000000 : ℝ) (992119743847/1000000000000 : ℝ) (992119743849/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 2 (992119743969/1000000000000 : ℝ) (992119743971/1000000000000 : ℝ) (992119743847/1000000000000 : ℝ) (992119743849/1000000000000 : ℝ) (248029935977/250000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 3 (248029935977/250000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 4 (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 5 (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 6 (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33249/262144 : ℝ)) 7 (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33249/262144 : ℝ))) (35333421947/200000000000 : ℝ) (88333554871/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35333421947/200000000000 : ℝ) (88333554871/500000000000 : ℝ) (588333554867/1000000000000 : ℝ) (588333554871/1000000000000 : ℝ) (210158933747/500000000000 : ℝ) (420317867503/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 1 (588333554867/1000000000000 : ℝ) (588333554871/1000000000000 : ℝ) (210158933747/500000000000 : ℝ) (420317867503/1000000000000 : ℝ) (25216285559/50000000000 : ℝ) (504325711187/1000000000000 : ℝ) (7769995393/15625000000 : ℝ) (12431992629/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 2 (25216285559/50000000000 : ℝ) (504325711187/1000000000000 : ℝ) (7769995393/15625000000 : ℝ) (12431992629/25000000000 : ℝ) (250401354083/500000000000 : ℝ) (250401354087/500000000000 : ℝ) (125197579089/250000000000 : ℝ) (125197579091/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 3 (250401354083/500000000000 : ℝ) (250401354087/500000000000 : ℝ) (125197579089/250000000000 : ℝ) (125197579091/250000000000 : ℝ) (500796512261/1000000000000 : ℝ) (500796512269/1000000000000 : ℝ) (250398256111/500000000000 : ℝ) (500796512231/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 4 (500796512261/1000000000000 : ℝ) (500796512269/1000000000000 : ℝ) (250398256111/500000000000 : ℝ) (500796512231/1000000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 5 (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 6 (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33249/262144 : ℝ))) 7 (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33249/262144 : ℝ)) hmem 8 (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33249/262144 : ℝ))) hcmem 8 (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33249/262144 : ℝ)) (992119743907/1000000000000 : ℝ) (99211974391/100000000000 : ℝ) (500796512241/1000000000000 : ℝ) (2003186049/4000000000 : ℝ) (792897557707/1000000000000 : ℝ) (31715902309/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0468_exp_lower
  have heNumeric : (256862672899/125000000000 : ℝ)/4 ≤ Real.exp (-53285320243/80000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862672899/125000000000 : ℝ)/4 ≤ Real.exp ((1039/8192 : ℝ)-(31715902309/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1039/8192 : ℝ) (33249/262144 : ℝ) (31715902309/40000000000 : ℝ) (256862672899/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0469; no trusted numerical premise.
theorem cover8_leaf0469_exp_radius : (998020108137998589/1000000000000000000 : ℝ) ≤ Real.exp ((-16625/1048576 : ℝ)/8) ∧ Real.exp ((-16625/1048576 : ℝ)/8) ≤ (99802010813799859/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16625/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0469_exp_lower : (184022687485505123/200000000000000000 : ℝ) ≤ Real.exp ((-42628257274063/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628257274063/64000000000000 : ℝ)/8) ≤ (57507089839220351/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628257274063/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0469_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450674263/500000000000 : ℝ) ≤ 4*Real.exp (33249/262144 : ℝ)*Real.exp (-mu (radius 8 (16625/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450674263/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16625/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0469_exp_radius
  have hrNumeric : (196854038153/200000000000 : ℝ) ≤ Real.exp (-16625/1048576 : ℝ) ∧ Real.exp (-16625/1048576 : ℝ) ≤ (492135095383/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196854038153/200000000000 : ℝ) ≤ (radius 8 (16625/131072 : ℝ)) ∧ (radius 8 (16625/131072 : ℝ)) ≤ (492135095383/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16625/131072 : ℝ)) (196854038153/200000000000 : ℝ) (492135095383/500000000000 : ℝ) (176669724541/1000000000000 : ℝ) (176669724547/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16625/131072 : ℝ)) (196854038153/200000000000 : ℝ) (492135095383/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196854038153/200000000000 : ℝ) (492135095383/500000000000 : ℝ) (496067547691/500000000000 : ℝ) (992135095383/1000000000000 : ℝ) (992103921353/1000000000000 : ℝ) (198420784271/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 1 (496067547691/500000000000 : ℝ) (992135095383/1000000000000 : ℝ) (992103921353/1000000000000 : ℝ) (198420784271/200000000000 : ℝ) (992119508367/1000000000000 : ℝ) (992119508369/1000000000000 : ℝ) (198423901649/200000000000 : ℝ) (992119508247/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 2 (992119508367/1000000000000 : ℝ) (992119508369/1000000000000 : ℝ) (198423901649/200000000000 : ℝ) (992119508247/1000000000000 : ℝ) (496059754153/500000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 3 (496059754153/500000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 4 (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 5 (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 6 (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16625/131072 : ℝ)) 7 (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16625/131072 : ℝ))) (176669724541/1000000000000 : ℝ) (176669724547/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176669724541/1000000000000 : ℝ) (176669724547/1000000000000 : ℝ) (58833486227/100000000000 : ℝ) (294167431137/500000000000 : ℝ) (420320977993/1000000000000 : ℝ) (420320978001/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 1 (58833486227/100000000000 : ℝ) (294167431137/500000000000 : ℝ) (420320977993/1000000000000 : ℝ) (420320978001/1000000000000 : ℝ) (504327920131/1000000000000 : ℝ) (252163960069/500000000000 : ℝ) (497282097703/1000000000000 : ℝ) (497282097711/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 2 (504327920131/1000000000000 : ℝ) (252163960069/500000000000 : ℝ) (497282097703/1000000000000 : ℝ) (497282097711/1000000000000 : ℝ) (500805008917/1000000000000 : ℝ) (20032200357/40000000000 : ℝ) (500792617809/1000000000000 : ℝ) (250396308909/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 3 (500805008917/1000000000000 : ℝ) (20032200357/40000000000 : ℝ) (500792617809/1000000000000 : ℝ) (250396308909/500000000000 : ℝ) (500798813363/1000000000000 : ℝ) (125199703343/250000000000 : ℝ) (125199703331/250000000000 : ℝ) (250399406667/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 4 (500798813363/1000000000000 : ℝ) (125199703343/250000000000 : ℝ) (125199703331/250000000000 : ℝ) (250399406667/500000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 5 (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 6 (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16625/131072 : ℝ))) 7 (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16625/131072 : ℝ)) hmem 8 (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16625/131072 : ℝ))) hcmem 8 (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16625/131072 : ℝ)) (198423901661/200000000000 : ℝ) (248029877077/250000000000 : ℝ) (500798813343/1000000000000 : ℝ) (500798813353/1000000000000 : ℝ) (792901389273/1000000000000 : ℝ) (198225347323/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0469_exp_lower
  have heNumeric : (1027450674263/500000000000 : ℝ)/4 ≤ Real.exp (-42628257274063/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450674263/500000000000 : ℝ)/4 ≤ Real.exp ((33249/262144 : ℝ)-(198225347323/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33249/262144 : ℝ) (16625/131072 : ℝ) (198225347323/250000000000 : ℝ) (1027450674263/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0470; no trusted numerical premise.
theorem cover8_leaf0470_exp_radius : (499010024325683169/500000000000000000 : ℝ) ≤ Real.exp ((-33251/2097152 : ℝ)/8) ∧ Real.exp ((-33251/2097152 : ℝ)/8) ≤ (998020048651366339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33251/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0470_exp_lower : (57507089718478937/62500000000000000 : ℝ) ≤ Real.exp ((-21314129174527/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314129174527/32000000000000 : ℝ)/8) ≤ (920113435495662993/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314129174527/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0470_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490131401/100000000000 : ℝ) ≤ 4*Real.exp (16625/131072 : ℝ)*Real.exp (-mu (radius 8 (33251/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490131401/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33251/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0470_exp_radius
  have hrNumeric : (246067430357/250000000000 : ℝ) ≤ Real.exp (-33251/2097152 : ℝ) ∧ Real.exp (-33251/2097152 : ℝ) ≤ (984269721429/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246067430357/250000000000 : ℝ) ≤ (radius 8 (33251/262144 : ℝ)) ∧ (radius 8 (33251/262144 : ℝ)) ≤ (984269721429/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33251/262144 : ℝ)) (246067430357/250000000000 : ℝ) (984269721429/1000000000000 : ℝ) (11042021207/62500000000 : ℝ) (88336169659/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33251/262144 : ℝ)) (246067430357/250000000000 : ℝ) (984269721429/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246067430357/250000000000 : ℝ) (984269721429/1000000000000 : ℝ) (496067430357/500000000000 : ℝ) (198426972143/200000000000 : ℝ) (992103684817/1000000000000 : ℝ) (496051842409/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 1 (496067430357/500000000000 : ℝ) (198426972143/200000000000 : ℝ) (992103684817/1000000000000 : ℝ) (496051842409/500000000000 : ℝ) (198423854553/200000000000 : ℝ) (992119272767/1000000000000 : ℝ) (992119272643/1000000000000 : ℝ) (198423854529/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 2 (198423854553/200000000000 : ℝ) (992119272767/1000000000000 : ℝ) (992119272643/1000000000000 : ℝ) (198423854529/200000000000 : ℝ) (3875465909/3906250000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 3 (3875465909/3906250000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 4 (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 5 (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 6 (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33251/262144 : ℝ)) 7 (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33251/262144 : ℝ))) (11042021207/62500000000 : ℝ) (88336169659/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11042021207/62500000000 : ℝ) (88336169659/500000000000 : ℝ) (73542021207/125000000000 : ℝ) (588336169659/1000000000000 : ℝ) (420324088427/1000000000000 : ℝ) (84064817687/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 1 (73542021207/125000000000 : ℝ) (588336169659/1000000000000 : ℝ) (420324088427/1000000000000 : ℝ) (84064817687/200000000000 : ℝ) (504330129041/1000000000000 : ℝ) (504330129047/1000000000000 : ℝ) (99456898041/200000000000 : ℝ) (124321122553/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 2 (504330129041/1000000000000 : ℝ) (504330129047/1000000000000 : ℝ) (99456898041/200000000000 : ℝ) (124321122553/250000000000 : ℝ) (500807309623/1000000000000 : ℝ) (50080730963/100000000000 : ℝ) (250397459609/500000000000 : ℝ) (250397459613/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 3 (500807309623/1000000000000 : ℝ) (50080730963/100000000000 : ℝ) (250397459609/500000000000 : ℝ) (250397459613/500000000000 : ℝ) (25040055721/50000000000 : ℝ) (125200278607/250000000000 : ℝ) (250400557191/500000000000 : ℝ) (50080111439/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 4 (25040055721/50000000000 : ℝ) (125200278607/250000000000 : ℝ) (250400557191/500000000000 : ℝ) (50080111439/100000000000 : ℝ) (500801114401/1000000000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 5 (500801114401/1000000000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 6 (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33251/262144 : ℝ))) 7 (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33251/262144 : ℝ)) hmem 8 (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33251/262144 : ℝ))) hcmem 8 (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33251/262144 : ℝ)) (992119272703/1000000000000 : ℝ) (496059636353/500000000000 : ℝ) (626001393/1250000000 : ℝ) (500801114409/1000000000000 : ℝ) (792905220769/1000000000000 : ℝ) (396452610393/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0470_exp_lower
  have heNumeric : (205490131401/100000000000 : ℝ)/4 ≤ Real.exp (-21314129174527/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490131401/100000000000 : ℝ)/4 ≤ Real.exp ((16625/131072 : ℝ)-(396452610393/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16625/131072 : ℝ) (33251/262144 : ℝ) (396452610393/500000000000 : ℝ) (205490131401/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0471; no trusted numerical premise.
theorem cover8_leaf0471_exp_radius : (31188124661398051/31250000000000000 : ℝ) ≤ Real.exp ((-8313/524288 : ℝ)/8) ∧ Real.exp ((-8313/524288 : ℝ)/8) ≤ (998019989164737633/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8313/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0471_exp_lower : (920113433573116521/1000000000000000000 : ℝ) ≤ Real.exp ((-42628259418861/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628259418861/64000000000000 : ℝ)/8) ≤ (460056716786558261/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628259418861/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0471_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901279661/1000000000000 : ℝ) ≤ 4*Real.exp (33251/262144 : ℝ)*Real.exp (-mu (radius 8 (8313/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901279661/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8313/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0471_exp_radius
  have hrNumeric : (246067313023/250000000000 : ℝ) ≤ Real.exp (-8313/524288 : ℝ) ∧ Real.exp (-8313/524288 : ℝ) ≤ (984269252093/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246067313023/250000000000 : ℝ) ≤ (radius 8 (8313/65536 : ℝ)) ∧ (radius 8 (8313/65536 : ℝ)) ≤ (984269252093/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8313/65536 : ℝ)) (246067313023/250000000000 : ℝ) (984269252093/1000000000000 : ℝ) (176674954037/1000000000000 : ℝ) (44168738511/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8313/65536 : ℝ)) (246067313023/250000000000 : ℝ) (984269252093/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246067313023/250000000000 : ℝ) (984269252093/1000000000000 : ℝ) (496067313023/500000000000 : ℝ) (992134626047/1000000000000 : ℝ) (992103448281/1000000000000 : ℝ) (496051724141/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 1 (496067313023/500000000000 : ℝ) (992134626047/1000000000000 : ℝ) (992103448281/1000000000000 : ℝ) (496051724141/500000000000 : ℝ) (992119037163/1000000000000 : ℝ) (198423807433/200000000000 : ℝ) (992119037041/1000000000000 : ℝ) (992119037043/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 2 (992119037163/1000000000000 : ℝ) (198423807433/200000000000 : ℝ) (992119037041/1000000000000 : ℝ) (992119037043/1000000000000 : ℝ) (496059518551/500000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 3 (496059518551/500000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 4 (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 5 (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 6 (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8313/65536 : ℝ)) 7 (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8313/65536 : ℝ))) (176674954037/1000000000000 : ℝ) (44168738511/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176674954037/1000000000000 : ℝ) (44168738511/250000000000 : ℝ) (294168738509/500000000000 : ℝ) (294168738511/500000000000 : ℝ) (420327198783/1000000000000 : ℝ) (52540899849/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 1 (294168738509/500000000000 : ℝ) (294168738511/500000000000 : ℝ) (420327198783/1000000000000 : ℝ) (52540899849/125000000000 : ℝ) (5043323379/10000000000 : ℝ) (504332337907/1000000000000 : ℝ) (62160860331/125000000000 : ℝ) (15540215083/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 2 (5043323379/10000000000 : ℝ) (504332337907/1000000000000 : ℝ) (62160860331/125000000000 : ℝ) (15540215083/31250000000 : ℝ) (250404805137/500000000000 : ℝ) (250404805141/500000000000 : ℝ) (125199305143/250000000000 : ℝ) (25039861029/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 3 (250404805137/500000000000 : ℝ) (250404805141/500000000000 : ℝ) (125199305143/250000000000 : ℝ) (25039861029/50000000000 : ℝ) (500803415423/1000000000000 : ℝ) (500803415431/1000000000000 : ℝ) (62600426923/125000000000 : ℝ) (500803415393/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 4 (500803415423/1000000000000 : ℝ) (500803415431/1000000000000 : ℝ) (62600426923/125000000000 : ℝ) (500803415393/1000000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 5 (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 6 (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8313/65536 : ℝ))) 7 (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8313/65536 : ℝ)) hmem 8 (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8313/65536 : ℝ))) hcmem 8 (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8313/65536 : ℝ)) (992119037101/1000000000000 : ℝ) (62007439819/62500000000 : ℝ) (500803415403/1000000000000 : ℝ) (125200853853/250000000000 : ℝ) (792909052181/1000000000000 : ℝ) (792909052199/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0471_exp_lower
  have heNumeric : (2054901279661/1000000000000 : ℝ)/4 ≤ Real.exp (-42628259418861/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901279661/1000000000000 : ℝ)/4 ≤ Real.exp ((33251/262144 : ℝ)-(792909052199/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33251/262144 : ℝ) (8313/65536 : ℝ) (792909052199/1000000000000 : ℝ) (2054901279661/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0472; no trusted numerical premise.
theorem cover8_leaf0472_exp_radius : (124752491209764059/125000000000000000 : ℝ) ≤ Real.exp ((-33253/2097152 : ℝ)/8) ∧ Real.exp ((-33253/2097152 : ℝ)/8) ≤ (998019929678112473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33253/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0472_exp_lower : (460056715829713073/500000000000000000 : ℝ) ≤ Real.exp ((-2131413024187/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131413024187/3200000000000 : ℝ)/8) ≤ (920113431659426147/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131413024187/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0472_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490124547/100000000000 : ℝ) ≤ 4*Real.exp (8313/65536 : ℝ)*Real.exp (-mu (radius 8 (33253/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490124547/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33253/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0472_exp_radius
  have hrNumeric : (246067195689/250000000000 : ℝ) ≤ Real.exp (-33253/2097152 : ℝ) ∧ Real.exp (-33253/2097152 : ℝ) ≤ (984268782757/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246067195689/250000000000 : ℝ) ≤ (radius 8 (33253/262144 : ℝ)) ∧ (radius 8 (33253/262144 : ℝ)) ≤ (984268782757/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33253/262144 : ℝ)) (246067195689/250000000000 : ℝ) (984268782757/1000000000000 : ℝ) (176677568723/1000000000000 : ℝ) (17667756873/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33253/262144 : ℝ)) (246067195689/250000000000 : ℝ) (984268782757/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246067195689/250000000000 : ℝ) (984268782757/1000000000000 : ℝ) (496067195689/500000000000 : ℝ) (992134391379/1000000000000 : ℝ) (198420642349/200000000000 : ℝ) (992103211747/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 1 (496067195689/500000000000 : ℝ) (992134391379/1000000000000 : ℝ) (198420642349/200000000000 : ℝ) (992103211747/1000000000000 : ℝ) (992118801561/1000000000000 : ℝ) (992118801563/1000000000000 : ℝ) (992118801439/1000000000000 : ℝ) (992118801441/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 2 (992118801561/1000000000000 : ℝ) (992118801563/1000000000000 : ℝ) (992118801439/1000000000000 : ℝ) (992118801441/1000000000000 : ℝ) (1984237603/2000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 3 (1984237603/2000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 4 (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 5 (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 6 (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33253/262144 : ℝ)) 7 (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33253/262144 : ℝ))) (176677568723/1000000000000 : ℝ) (17667756873/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176677568723/1000000000000 : ℝ) (17667756873/100000000000 : ℝ) (588338784361/1000000000000 : ℝ) (117667756873/200000000000 : ℝ) (42033030907/100000000000 : ℝ) (420330309079/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 1 (588338784361/1000000000000 : ℝ) (117667756873/200000000000 : ℝ) (42033030907/100000000000 : ℝ) (420330309079/1000000000000 : ℝ) (100866909343/200000000000 : ℝ) (252167273361/500000000000 : ℝ) (248644637519/500000000000 : ℝ) (248644637523/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 2 (100866909343/200000000000 : ℝ) (252167273361/500000000000 : ℝ) (248644637519/500000000000 : ℝ) (248644637523/500000000000 : ℝ) (125202977719/250000000000 : ℝ) (125202977721/250000000000 : ℝ) (500799521877/1000000000000 : ℝ) (100159904377/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 3 (125202977719/250000000000 : ℝ) (125202977721/250000000000 : ℝ) (500799521877/1000000000000 : ℝ) (100159904377/200000000000 : ℝ) (62600714547/125000000000 : ℝ) (100161143277/200000000000 : ℝ) (250402858169/500000000000 : ℝ) (500805716347/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 4 (62600714547/125000000000 : ℝ) (100161143277/200000000000 : ℝ) (250402858169/500000000000 : ℝ) (500805716347/1000000000000 : ℝ) (500805716357/1000000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 5 (500805716357/1000000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 6 (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33253/262144 : ℝ))) 7 (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33253/262144 : ℝ)) hmem 8 (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33253/262144 : ℝ))) hcmem 8 (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33253/262144 : ℝ)) (992118801499/1000000000000 : ℝ) (496059400751/500000000000 : ℝ) (125201429089/250000000000 : ℝ) (250402858183/500000000000 : ℝ) (198228220879/250000000000 : ℝ) (158582576707/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0472_exp_lower
  have heNumeric : (205490124547/100000000000 : ℝ)/4 ≤ Real.exp (-2131413024187/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490124547/100000000000 : ℝ)/4 ≤ Real.exp ((8313/65536 : ℝ)-(158582576707/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8313/65536 : ℝ) (33253/262144 : ℝ) (158582576707/200000000000 : ℝ) (205490124547/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0473; no trusted numerical premise.
theorem cover8_leaf0473_exp_radius : (499009935095745429/500000000000000000 : ℝ) ≤ Real.exp ((-16627/1048576 : ℝ)/8) ∧ Real.exp ((-16627/1048576 : ℝ)/8) ≤ (998019870191490859/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16627/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0473_exp_lower : (460056714877295933/500000000000000000 : ℝ) ≤ Real.exp ((-42628261543691/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628261543691/64000000000000 : ℝ)/8) ≤ (920113429754591867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628261543691/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0473_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901211437/1000000000000 : ℝ) ≤ 4*Real.exp (33253/262144 : ℝ)*Real.exp (-mu (radius 8 (16627/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901211437/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16627/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0473_exp_radius
  have hrNumeric : (49213415671/50000000000 : ℝ) ≤ Real.exp (-16627/1048576 : ℝ) ∧ Real.exp (-16627/1048576 : ℝ) ≤ (984268313421/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49213415671/50000000000 : ℝ) ≤ (radius 8 (16627/131072 : ℝ)) ∧ (radius 8 (16627/131072 : ℝ)) ≤ (984268313421/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16627/131072 : ℝ)) (49213415671/50000000000 : ℝ) (984268313421/1000000000000 : ℝ) (176680183369/1000000000000 : ℝ) (1413441467/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16627/131072 : ℝ)) (49213415671/50000000000 : ℝ) (984268313421/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49213415671/50000000000 : ℝ) (984268313421/1000000000000 : ℝ) (99213415671/100000000000 : ℝ) (992134156711/1000000000000 : ℝ) (992102975209/1000000000000 : ℝ) (992102975211/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 1 (99213415671/100000000000 : ℝ) (992134156711/1000000000000 : ℝ) (992102975209/1000000000000 : ℝ) (992102975211/1000000000000 : ℝ) (992118565959/1000000000000 : ℝ) (992118565961/1000000000000 : ℝ) (248029641459/250000000000 : ℝ) (992118565839/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 2 (992118565959/1000000000000 : ℝ) (992118565961/1000000000000 : ℝ) (248029641459/250000000000 : ℝ) (992118565839/1000000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 3 (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 4 (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 5 (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 6 (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16627/131072 : ℝ)) 7 (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16627/131072 : ℝ))) (176680183369/1000000000000 : ℝ) (1413441467/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176680183369/1000000000000 : ℝ) (1413441467/8000000000 : ℝ) (147085022921/250000000000 : ℝ) (73542511461/125000000000 : ℝ) (210166709643/500000000000 : ℝ) (210166709647/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 1 (147085022921/250000000000 : ℝ) (73542511461/125000000000 : ℝ) (210166709643/500000000000 : ℝ) (210166709647/500000000000 : ℝ) (100867351097/200000000000 : ℝ) (504336755491/1000000000000 : ℝ) (248645833687/500000000000 : ℝ) (248645833691/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 2 (100867351097/200000000000 : ℝ) (504336755491/1000000000000 : ℝ) (248645833687/500000000000 : ℝ) (248645833691/500000000000 : ℝ) (500814211429/1000000000000 : ℝ) (500814211437/1000000000000 : ℝ) (125200455783/250000000000 : ℝ) (25040091157/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 3 (500814211429/1000000000000 : ℝ) (500814211437/1000000000000 : ℝ) (125200455783/250000000000 : ℝ) (25040091157/50000000000 : ℝ) (782512527/1562500000 : ℝ) (500808017289/1000000000000 : ℝ) (250404008621/500000000000 : ℝ) (500808017251/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 4 (782512527/1562500000 : ℝ) (500808017289/1000000000000 : ℝ) (250404008621/500000000000 : ℝ) (500808017251/1000000000000 : ℝ) (500808017261/1000000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 5 (500808017261/1000000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 6 (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16627/131072 : ℝ))) 7 (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16627/131072 : ℝ)) hmem 8 (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16627/131072 : ℝ))) hcmem 8 (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16627/131072 : ℝ)) (992118565897/1000000000000 : ℝ) (9921185659/10000000000 : ℝ) (25040400863/50000000000 : ℝ) (50080801727/100000000000 : ℝ) (31716668591/40000000000 : ℝ) (396458357397/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0473_exp_lower
  have heNumeric : (2054901211437/1000000000000 : ℝ)/4 ≤ Real.exp (-42628261543691/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901211437/1000000000000 : ℝ)/4 ≤ Real.exp ((33253/262144 : ℝ)-(396458357397/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33253/262144 : ℝ) (16627/131072 : ℝ) (396458357397/500000000000 : ℝ) (2054901211437/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0474; no trusted numerical premise.
theorem cover8_leaf0474_exp_radius : (998019810704872789/1000000000000000000 : ℝ) ≤ Real.exp ((-33255/2097152 : ℝ)/8) ∧ Real.exp ((-33255/2097152 : ℝ)/8) ≤ (99801981070487279/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33255/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0474_exp_lower : (460056713929191827/500000000000000000 : ℝ) ≤ Real.exp ((-21314131299421/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314131299421/32000000000000 : ℝ)/8) ≤ (184022685571676731/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314131299421/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0474_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901177559/1000000000000 : ℝ) ≤ 4*Real.exp (16627/131072 : ℝ)*Real.exp (-mu (radius 8 (33255/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901177559/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33255/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0474_exp_radius
  have hrNumeric : (246066961021/250000000000 : ℝ) ≤ Real.exp (-33255/2097152 : ℝ) ∧ Real.exp (-33255/2097152 : ℝ) ≤ (196853568817/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246066961021/250000000000 : ℝ) ≤ (radius 8 (33255/262144 : ℝ)) ∧ (radius 8 (33255/262144 : ℝ)) ≤ (196853568817/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33255/262144 : ℝ)) (246066961021/250000000000 : ℝ) (196853568817/200000000000 : ℝ) (88341398987/500000000000 : ℝ) (176682797981/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33255/262144 : ℝ)) (246066961021/250000000000 : ℝ) (196853568817/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246066961021/250000000000 : ℝ) (196853568817/200000000000 : ℝ) (496066961021/500000000000 : ℝ) (992133922043/1000000000000 : ℝ) (992102738673/1000000000000 : ℝ) (39684109547/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 1 (496066961021/500000000000 : ℝ) (992133922043/1000000000000 : ℝ) (992102738673/1000000000000 : ℝ) (39684109547/40000000000 : ℝ) (992118330357/1000000000000 : ℝ) (992118330359/1000000000000 : ℝ) (496059165117/500000000000 : ℝ) (992118330237/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 2 (992118330357/1000000000000 : ℝ) (992118330359/1000000000000 : ℝ) (496059165117/500000000000 : ℝ) (992118330237/1000000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 3 (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 4 (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 5 (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 6 (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33255/262144 : ℝ)) 7 (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33255/262144 : ℝ))) (88341398987/500000000000 : ℝ) (176682797981/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88341398987/500000000000 : ℝ) (176682797981/1000000000000 : ℝ) (588341398987/1000000000000 : ℝ) (588341398991/1000000000000 : ℝ) (42033652943/100000000000 : ℝ) (2627103309/6250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 1 (588341398987/1000000000000 : ℝ) (588341398991/1000000000000 : ℝ) (42033652943/100000000000 : ℝ) (2627103309/6250000000 : ℝ) (31521185263/62500000000 : ℝ) (63042370527/125000000000 : ℝ) (497294059657/1000000000000 : ℝ) (99458811933/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 2 (31521185263/62500000000 : ℝ) (63042370527/125000000000 : ℝ) (497294059657/1000000000000 : ℝ) (99458811933/200000000000 : ℝ) (125204127983/250000000000 : ℝ) (500816511941/1000000000000 : ℝ) (250402062169/500000000000 : ℝ) (500804124347/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 3 (125204127983/250000000000 : ℝ) (500816511941/1000000000000 : ℝ) (250402062169/500000000000 : ℝ) (500804124347/1000000000000 : ℝ) (100162063627/200000000000 : ℝ) (7825161221/15625000000 : ℝ) (31300644881/62500000000 : ℝ) (250405159053/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 4 (100162063627/200000000000 : ℝ) (7825161221/15625000000 : ℝ) (31300644881/62500000000 : ℝ) (250405159053/500000000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 5 (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 6 (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33255/262144 : ℝ))) 7 (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33255/262144 : ℝ)) hmem 8 (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33255/262144 : ℝ))) hcmem 8 (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33255/262144 : ℝ)) (198423666059/200000000000 : ℝ) (496059165149/500000000000 : ℝ) (100162063623/200000000000 : ℝ) (801296509/1600000000 : ℝ) (792920545959/1000000000000 : ℝ) (396460272989/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0474_exp_lower
  have heNumeric : (2054901177559/1000000000000 : ℝ)/4 ≤ Real.exp (-21314131299421/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901177559/1000000000000 : ℝ)/4 ≤ Real.exp ((16627/131072 : ℝ)-(396460272989/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16627/131072 : ℝ) (33255/262144 : ℝ) (396460272989/500000000000 : ℝ) (2054901177559/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0450_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0450_certificate
#check SmaleRate.Proofs.cover8_leaf0451_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0451_certificate
#check SmaleRate.Proofs.cover8_leaf0452_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0452_certificate
#check SmaleRate.Proofs.cover8_leaf0453_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0453_certificate
#check SmaleRate.Proofs.cover8_leaf0454_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0454_certificate
#check SmaleRate.Proofs.cover8_leaf0455_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0455_certificate
#check SmaleRate.Proofs.cover8_leaf0456_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0456_certificate
#check SmaleRate.Proofs.cover8_leaf0457_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0457_certificate
#check SmaleRate.Proofs.cover8_leaf0458_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0458_certificate
#check SmaleRate.Proofs.cover8_leaf0459_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0459_certificate
#check SmaleRate.Proofs.cover8_leaf0460_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0460_certificate
#check SmaleRate.Proofs.cover8_leaf0461_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0461_certificate
#check SmaleRate.Proofs.cover8_leaf0462_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0462_certificate
#check SmaleRate.Proofs.cover8_leaf0463_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0463_certificate
#check SmaleRate.Proofs.cover8_leaf0464_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0464_certificate
#check SmaleRate.Proofs.cover8_leaf0465_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0465_certificate
#check SmaleRate.Proofs.cover8_leaf0466_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0466_certificate
#check SmaleRate.Proofs.cover8_leaf0467_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0467_certificate
#check SmaleRate.Proofs.cover8_leaf0468_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0468_certificate
#check SmaleRate.Proofs.cover8_leaf0469_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0469_certificate
#check SmaleRate.Proofs.cover8_leaf0470_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0470_certificate
#check SmaleRate.Proofs.cover8_leaf0471_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0471_certificate
#check SmaleRate.Proofs.cover8_leaf0472_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0472_certificate
#check SmaleRate.Proofs.cover8_leaf0473_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0473_certificate
#check SmaleRate.Proofs.cover8_leaf0474_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0474_certificate
