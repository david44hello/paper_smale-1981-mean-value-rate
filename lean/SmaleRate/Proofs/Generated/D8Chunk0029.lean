/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0725; no trusted numerical premise.
theorem cover8_leaf0725_exp_radius : (39920449786755507/40000000000000000 : ℝ) ≤ Real.exp ((-33399/2097152 : ℝ)/8) ∧ Real.exp ((-33399/2097152 : ℝ)/8) ≤ (249502811167221919/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33399/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0725_exp_lower : (920113467893886463/1000000000000000000 : ℝ) ≤ Real.exp ((-85256480641923/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256480641923/128000000000000 : ℝ)/8) ≤ (1797096616980247/1953125000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256480641923/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0725_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901892853/1000000000000 : ℝ) ≤ 4*Real.exp (66797/524288 : ℝ)*Real.exp (-mu (radius 8 (33399/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901892853/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33399/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0725_exp_radius
  have hrNumeric : (196840052419/200000000000 : ℝ) ≤ Real.exp (-33399/2097152 : ℝ) ∧ Real.exp (-33399/2097152 : ℝ) ≤ (61512516381/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196840052419/200000000000 : ℝ) ≤ (radius 8 (33399/262144 : ℝ)) ∧ (radius 8 (33399/262144 : ℝ)) ≤ (61512516381/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33399/262144 : ℝ)) (196840052419/200000000000 : ℝ) (61512516381/62500000000 : ℝ) (177058871819/1000000000000 : ℝ) (88529435913/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33399/262144 : ℝ)) (196840052419/200000000000 : ℝ) (61512516381/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196840052419/200000000000 : ℝ) (61512516381/62500000000 : ℝ) (992100131047/1000000000000 : ℝ) (124012516381/125000000000 : ℝ) (496034339057/500000000000 : ℝ) (198413735623/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 1 (992100131047/1000000000000 : ℝ) (124012516381/125000000000 : ℝ) (496034339057/500000000000 : ℝ) (198413735623/200000000000 : ℝ) (49604220229/50000000000 : ℝ) (496042202291/500000000000 : ℝ) (198416880891/200000000000 : ℝ) (992084404457/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 2 (49604220229/50000000000 : ℝ) (496042202291/500000000000 : ℝ) (198416880891/200000000000 : ℝ) (992084404457/1000000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 3 (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 4 (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 5 (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 6 (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33399/262144 : ℝ)) 7 (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33399/262144 : ℝ))) (177058871819/1000000000000 : ℝ) (88529435913/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177058871819/1000000000000 : ℝ) (88529435913/500000000000 : ℝ) (588529435909/1000000000000 : ℝ) (588529435913/1000000000000 : ℝ) (420783640151/1000000000000 : ℝ) (2629897751/6250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 1 (588529435909/1000000000000 : ℝ) (588529435913/1000000000000 : ℝ) (420783640151/1000000000000 : ℝ) (2629897751/6250000000 : ℝ) (50465653803/100000000000 : ℝ) (504656538037/1000000000000 : ℝ) (99527595847/200000000000 : ℝ) (497637979243/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 2 (50465653803/100000000000 : ℝ) (504656538037/1000000000000 : ℝ) (99527595847/200000000000 : ℝ) (497637979243/1000000000000 : ℝ) (62643407329/125000000000 : ℝ) (6264340733/12500000000 : ℝ) (31320935727/62500000000 : ℝ) (12528374291/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 3 (62643407329/125000000000 : ℝ) (6264340733/12500000000 : ℝ) (31320935727/62500000000 : ℝ) (12528374291/25000000000 : ℝ) (125285278783/250000000000 : ℝ) (25057055757/50000000000 : ℝ) (250570557547/500000000000 : ℝ) (501141115103/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 4 (125285278783/250000000000 : ℝ) (25057055757/50000000000 : ℝ) (250570557547/500000000000 : ℝ) (501141115103/1000000000000 : ℝ) (501141115113/1000000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 5 (501141115113/1000000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 6 (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33399/262144 : ℝ))) 7 (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33399/262144 : ℝ)) hmem 8 (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33399/262144 : ℝ))) hcmem 8 (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33399/262144 : ℝ)) (992084404517/1000000000000 : ℝ) (24802110113/25000000000 : ℝ) (62642639389/125000000000 : ℝ) (250570557561/500000000000 : ℝ) (396735710811/500000000000 : ℝ) (793471421641/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0725_exp_lower
  have heNumeric : (2054901892853/1000000000000 : ℝ)/4 ≤ Real.exp (-85256480641923/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901892853/1000000000000 : ℝ)/4 ≤ Real.exp ((66797/524288 : ℝ)-(793471421641/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66797/524288 : ℝ) (33399/262144 : ℝ) (793471421641/1000000000000 : ℝ) (2054901892853/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0726; no trusted numerical premise.
theorem cover8_leaf0726_exp_radius : (499005607462917629/500000000000000000 : ℝ) ≤ Real.exp ((-66799/4194304 : ℝ)/8) ∧ Real.exp ((-66799/4194304 : ℝ)/8) ≤ (998011214925835259/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66799/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0726_exp_lower : (920113467595037383/1000000000000000000 : ℝ) ≤ Real.exp ((-42628240487257/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628240487257/64000000000000 : ℝ)/8) ≤ (115014183449379673/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628240487257/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0726_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450943757/500000000000 : ℝ) ≤ 4*Real.exp (33399/262144 : ℝ)*Real.exp (-mu (radius 8 (66799/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450943757/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66799/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0726_exp_radius
  have hrNumeric : (246050006861/250000000000 : ℝ) ≤ Real.exp (-66799/4194304 : ℝ) ∧ Real.exp (-66799/4194304 : ℝ) ≤ (196840005489/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246050006861/250000000000 : ℝ) ≤ (radius 8 (66799/524288 : ℝ)) ∧ (radius 8 (66799/524288 : ℝ)) ≤ (196840005489/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66799/524288 : ℝ)) (246050006861/250000000000 : ℝ) (196840005489/200000000000 : ℝ) (177060176147/1000000000000 : ℝ) (177060176153/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66799/524288 : ℝ)) (246050006861/250000000000 : ℝ) (196840005489/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246050006861/250000000000 : ℝ) (196840005489/200000000000 : ℝ) (496050006861/500000000000 : ℝ) (992100013723/1000000000000 : ℝ) (19841371197/20000000000 : ℝ) (248017139963/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 1 (496050006861/500000000000 : ℝ) (992100013723/1000000000000 : ℝ) (19841371197/20000000000 : ℝ) (248017139963/250000000000 : ℝ) (496042143393/500000000000 : ℝ) (248021071697/250000000000 : ℝ) (992084286661/1000000000000 : ℝ) (992084286663/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 2 (496042143393/500000000000 : ℝ) (248021071697/250000000000 : ℝ) (992084286661/1000000000000 : ℝ) (992084286663/1000000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 3 (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 4 (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 5 (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 6 (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66799/524288 : ℝ)) 7 (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66799/524288 : ℝ))) (177060176147/1000000000000 : ℝ) (177060176153/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177060176147/1000000000000 : ℝ) (177060176153/1000000000000 : ℝ) (588530088073/1000000000000 : ℝ) (588530088077/1000000000000 : ℝ) (105196297507/250000000000 : ℝ) (105196297509/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 1 (588530088073/1000000000000 : ℝ) (588530088077/1000000000000 : ℝ) (105196297507/250000000000 : ℝ) (105196297509/250000000000 : ℝ) (10093152781/20000000000 : ℝ) (504657639057/1000000000000 : ℝ) (99527834287/200000000000 : ℝ) (248819585721/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 2 (10093152781/20000000000 : ℝ) (504657639057/1000000000000 : ℝ) (99527834287/200000000000 : ℝ) (248819585721/500000000000 : ℝ) (250574202621/500000000000 : ℝ) (2004593621/4000000000 : ℝ) (501136118589/1000000000000 : ℝ) (501136118597/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 3 (250574202621/500000000000 : ℝ) (2004593621/4000000000 : ℝ) (501136118589/1000000000000 : ℝ) (501136118597/1000000000000 : ℝ) (100228452383/200000000000 : ℝ) (125285565481/250000000000 : ℝ) (501142261877/1000000000000 : ℝ) (250571130943/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 4 (100228452383/200000000000 : ℝ) (125285565481/250000000000 : ℝ) (501142261877/1000000000000 : ℝ) (250571130943/500000000000 : ℝ) (62642782737/125000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 5 (62642782737/125000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 6 (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66799/524288 : ℝ))) 7 (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66799/524288 : ℝ)) hmem 8 (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66799/524288 : ℝ))) hcmem 8 (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66799/524288 : ℝ)) (992084286723/1000000000000 : ℝ) (496042143363/500000000000 : ℝ) (100228452379/200000000000 : ℝ) (100228452381/200000000000 : ℝ) (793473331569/1000000000000 : ℝ) (198368332897/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0726_exp_lower
  have heNumeric : (1027450943757/500000000000 : ℝ)/4 ≤ Real.exp (-42628240487257/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450943757/500000000000 : ℝ)/4 ≤ Real.exp ((33399/262144 : ℝ)-(198368332897/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33399/262144 : ℝ) (66799/524288 : ℝ) (198368332897/250000000000 : ℝ) (1027450943757/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0727; no trusted numerical premise.
theorem cover8_leaf0727_exp_radius : (62375699073923983/62500000000000000 : ℝ) ≤ Real.exp ((-4175/262144 : ℝ)/8) ∧ Real.exp ((-4175/262144 : ℝ)/8) ≤ (998011185182783729/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4175/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0727_exp_lower : (92011346729722343/100000000000000000 : ℝ) ≤ Real.exp ((-85256481305953/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256481305953/128000000000000 : ℝ)/8) ≤ (920113467297223431/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256481305953/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0727_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901882193/1000000000000 : ℝ) ≤ 4*Real.exp (66799/524288 : ℝ)*Real.exp (-mu (radius 8 (4175/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901882193/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4175/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0727_exp_radius
  have hrNumeric : (123024974099/125000000000 : ℝ) ≤ Real.exp (-4175/262144 : ℝ) ∧ Real.exp (-4175/262144 : ℝ) ≤ (984199792793/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123024974099/125000000000 : ℝ) ≤ (radius 8 (4175/32768 : ℝ)) ∧ (radius 8 (4175/32768 : ℝ)) ≤ (984199792793/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4175/32768 : ℝ)) (123024974099/125000000000 : ℝ) (984199792793/1000000000000 : ℝ) (177061480469/1000000000000 : ℝ) (44265370119/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4175/32768 : ℝ)) (123024974099/125000000000 : ℝ) (984199792793/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123024974099/125000000000 : ℝ) (984199792793/1000000000000 : ℝ) (248024974099/250000000000 : ℝ) (992099896397/1000000000000 : ℝ) (496034220793/500000000000 : ℝ) (248017110397/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 1 (248024974099/250000000000 : ℝ) (992099896397/1000000000000 : ℝ) (496034220793/500000000000 : ℝ) (248017110397/250000000000 : ℝ) (992084168991/1000000000000 : ℝ) (992084168993/1000000000000 : ℝ) (496042084433/500000000000 : ℝ) (248021042217/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 2 (992084168991/1000000000000 : ℝ) (992084168993/1000000000000 : ℝ) (496042084433/500000000000 : ℝ) (248021042217/250000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 3 (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 4 (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 5 (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 6 (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4175/32768 : ℝ)) 7 (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4175/32768 : ℝ))) (177061480469/1000000000000 : ℝ) (44265370119/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177061480469/1000000000000 : ℝ) (44265370119/250000000000 : ℝ) (294265370117/500000000000 : ℝ) (294265370119/500000000000 : ℝ) (105196684973/250000000000 : ℝ) (420786739901/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 1 (294265370117/500000000000 : ℝ) (294265370119/500000000000 : ℝ) (105196684973/250000000000 : ℝ) (420786739901/1000000000000 : ℝ) (504658740063/1000000000000 : ℝ) (50465874007/100000000000 : ℝ) (3981122909/8000000000 : ℝ) (497640363633/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 2 (504658740063/1000000000000 : ℝ) (50465874007/100000000000 : ℝ) (3981122909/8000000000 : ℝ) (497640363633/1000000000000 : ℝ) (125287387961/250000000000 : ℝ) (125287387963/250000000000 : ℝ) (250568632769/500000000000 : ℝ) (501137265547/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 3 (125287387961/250000000000 : ℝ) (125287387963/250000000000 : ℝ) (250568632769/500000000000 : ℝ) (501137265547/1000000000000 : ℝ) (501143408691/1000000000000 : ℝ) (5011434087/10000000000 : ℝ) (501143408653/1000000000000 : ℝ) (250571704331/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 4 (501143408691/1000000000000 : ℝ) (5011434087/10000000000 : ℝ) (501143408653/1000000000000 : ℝ) (250571704331/500000000000 : ℝ) (15660731521/31250000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 5 (15660731521/31250000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 6 (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4175/32768 : ℝ))) 7 (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4175/32768 : ℝ)) hmem 8 (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4175/32768 : ℝ))) hcmem 8 (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4175/32768 : ℝ)) (31002630279/31250000000 : ℝ) (992084168931/1000000000000 : ℝ) (501143408671/1000000000000 : ℝ) (501143408681/1000000000000 : ℝ) (793475241507/1000000000000 : ℝ) (396737620763/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0727_exp_lower
  have heNumeric : (2054901882193/1000000000000 : ℝ)/4 ≤ Real.exp (-85256481305953/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901882193/1000000000000 : ℝ)/4 ≤ Real.exp ((66799/524288 : ℝ)-(396737620763/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66799/524288 : ℝ) (4175/32768 : ℝ) (396737620763/500000000000 : ℝ) (2054901882193/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0728; no trusted numerical premise.
theorem cover8_leaf0728_exp_radius : (998011155439733083/1000000000000000000 : ℝ) ≤ Real.exp ((-66801/4194304 : ℝ)/8) ∧ Real.exp ((-66801/4194304 : ℝ)/8) ≤ (249502788859933271/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66801/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0728_exp_lower : (920113467002744889/1000000000000000000 : ℝ) ≤ Real.exp ((-1065706020421/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065706020421/1600000000000 : ℝ)/8) ≤ (92011346700274489/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065706020421/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0728_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725469233/250000000000 : ℝ) ≤ 4*Real.exp (4175/32768 : ℝ)*Real.exp (-mu (radius 8 (66801/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725469233/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66801/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0728_exp_radius
  have hrNumeric : (984199558141/1000000000000 : ℝ) ≤ Real.exp (-66801/4194304 : ℝ) ∧ Real.exp (-66801/4194304 : ℝ) ≤ (492099779071/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984199558141/1000000000000 : ℝ) ≤ (radius 8 (66801/524288 : ℝ)) ∧ (radius 8 (66801/524288 : ℝ)) ≤ (492099779071/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66801/524288 : ℝ)) (984199558141/1000000000000 : ℝ) (492099779071/500000000000 : ℝ) (177062784777/1000000000000 : ℝ) (177062784783/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66801/524288 : ℝ)) (984199558141/1000000000000 : ℝ) (492099779071/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984199558141/1000000000000 : ℝ) (492099779071/500000000000 : ℝ) (99209977907/100000000000 : ℝ) (992099779071/1000000000000 : ℝ) (992068323323/1000000000000 : ℝ) (248017080831/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 1 (99209977907/100000000000 : ℝ) (992099779071/1000000000000 : ℝ) (992068323323/1000000000000 : ℝ) (248017080831/250000000000 : ℝ) (248021012799/250000000000 : ℝ) (496042025599/500000000000 : ℝ) (992084051071/1000000000000 : ℝ) (992084051073/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 2 (248021012799/250000000000 : ℝ) (496042025599/500000000000 : ℝ) (992084051071/1000000000000 : ℝ) (992084051073/1000000000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 3 (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 4 (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 5 (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 6 (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66801/524288 : ℝ)) 7 (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66801/524288 : ℝ))) (177062784777/1000000000000 : ℝ) (177062784783/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177062784777/1000000000000 : ℝ) (177062784783/1000000000000 : ℝ) (147132848097/250000000000 : ℝ) (73566424049/125000000000 : ℝ) (420788289733/1000000000000 : ℝ) (420788289741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 1 (147132848097/250000000000 : ℝ) (73566424049/125000000000 : ℝ) (420788289733/1000000000000 : ℝ) (420788289741/1000000000000 : ℝ) (25232992053/50000000000 : ℝ) (504659841067/1000000000000 : ℝ) (248820777899/500000000000 : ℝ) (99528311161/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 2 (25232992053/50000000000 : ℝ) (504659841067/1000000000000 : ℝ) (248820777899/500000000000 : ℝ) (99528311161/200000000000 : ℝ) (501150698429/1000000000000 : ℝ) (125287674609/250000000000 : ℝ) (50113841247/100000000000 : ℝ) (250569206239/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 3 (501150698429/1000000000000 : ℝ) (125287674609/250000000000 : ℝ) (50113841247/100000000000 : ℝ) (250569206239/500000000000 : ℝ) (501144555449/1000000000000 : ℝ) (501144555457/1000000000000 : ℝ) (501144555411/1000000000000 : ℝ) (25057227771/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 4 (501144555449/1000000000000 : ℝ) (501144555457/1000000000000 : ℝ) (501144555411/1000000000000 : ℝ) (25057227771/50000000000 : ℝ) (50114455543/100000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 5 (50114455543/100000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 6 (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66801/524288 : ℝ))) 7 (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66801/524288 : ℝ)) hmem 8 (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66801/524288 : ℝ))) hcmem 8 (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66801/524288 : ℝ)) (992084051133/1000000000000 : ℝ) (15501313299/15625000000 : ℝ) (501144555429/1000000000000 : ℝ) (501144555439/1000000000000 : ℝ) (99184643927/125000000000 : ℝ) (158695430287/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0728_exp_lower
  have heNumeric : (513725469233/250000000000 : ℝ)/4 ≤ Real.exp (-1065706020421/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725469233/250000000000 : ℝ)/4 ≤ Real.exp ((4175/32768 : ℝ)-(158695430287/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4175/32768 : ℝ) (66801/524288 : ℝ) (158695430287/200000000000 : ℝ) (513725469233/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0729; no trusted numerical premise.
theorem cover8_leaf0729_exp_radius : (499005562848341663/500000000000000000 : ℝ) ≤ Real.exp ((-33401/2097152 : ℝ)/8) ∧ Real.exp ((-33401/2097152 : ℝ)/8) ≤ (998011125696683327/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33401/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0729_exp_lower : (92011346670941649/100000000000000000 : ℝ) ≤ Real.exp ((-85256481960127/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256481960127/128000000000000 : ℝ)/8) ≤ (920113466709416491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256481960127/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0729_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901871691/1000000000000 : ℝ) ≤ 4*Real.exp (66801/524288 : ℝ)*Real.exp (-mu (radius 8 (33401/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901871691/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33401/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0729_exp_radius
  have hrNumeric : (984199323489/1000000000000 : ℝ) ≤ Real.exp (-33401/2097152 : ℝ) ∧ Real.exp (-33401/2097152 : ℝ) ≤ (98419932349/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984199323489/1000000000000 : ℝ) ≤ (radius 8 (33401/262144 : ℝ)) ∧ (radius 8 (33401/262144 : ℝ)) ≤ (98419932349/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33401/262144 : ℝ)) (984199323489/1000000000000 : ℝ) (98419932349/100000000000 : ℝ) (4426602227/25000000000 : ℝ) (88532044543/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33401/262144 : ℝ)) (984199323489/1000000000000 : ℝ) (98419932349/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984199323489/1000000000000 : ℝ) (98419932349/100000000000 : ℝ) (62006228859/62500000000 : ℝ) (198419932349/200000000000 : ℝ) (992068205059/1000000000000 : ℝ) (49603410253/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 1 (62006228859/62500000000 : ℝ) (198419932349/200000000000 : ℝ) (992068205059/1000000000000 : ℝ) (49603410253/50000000000 : ℝ) (992083933401/1000000000000 : ℝ) (992083933403/1000000000000 : ℝ) (248020983319/250000000000 : ℝ) (496041966639/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 2 (992083933401/1000000000000 : ℝ) (992083933403/1000000000000 : ℝ) (248020983319/250000000000 : ℝ) (496041966639/500000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 3 (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 4 (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 5 (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 6 (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33401/262144 : ℝ)) 7 (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33401/262144 : ℝ))) (4426602227/25000000000 : ℝ) (88532044543/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4426602227/25000000000 : ℝ) (88532044543/500000000000 : ℝ) (29426602227/50000000000 : ℝ) (588532044543/1000000000000 : ℝ) (420789839563/1000000000000 : ℝ) (420789839571/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 1 (29426602227/50000000000 : ℝ) (588532044543/1000000000000 : ℝ) (420789839563/1000000000000 : ℝ) (420789839571/1000000000000 : ℝ) (504660942051/1000000000000 : ℝ) (504660942057/1000000000000 : ℝ) (248821373981/500000000000 : ℝ) (497642747969/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 2 (504660942051/1000000000000 : ℝ) (504660942057/1000000000000 : ℝ) (248821373981/500000000000 : ℝ) (497642747969/1000000000000 : ℝ) (250575922503/500000000000 : ℝ) (501151845013/1000000000000 : ℝ) (100227911879/200000000000 : ℝ) (501139559403/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 3 (250575922503/500000000000 : ℝ) (501151845013/1000000000000 : ℝ) (100227911879/200000000000 : ℝ) (501139559403/1000000000000 : ℝ) (2505728511/5000000000 : ℝ) (7830401597/15625000000 : ℝ) (250572851081/500000000000 : ℝ) (501145702171/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 4 (2505728511/5000000000 : ℝ) (7830401597/15625000000 : ℝ) (250572851081/500000000000 : ℝ) (501145702171/1000000000000 : ℝ) (501145702181/1000000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 5 (501145702181/1000000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 6 (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33401/262144 : ℝ))) 7 (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33401/262144 : ℝ)) hmem 8 (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33401/262144 : ℝ))) hcmem 8 (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33401/262144 : ℝ)) (496041966669/500000000000 : ℝ) (992083933341/1000000000000 : ℝ) (25057285109/50000000000 : ℝ) (50114570219/100000000000 : ℝ) (158695812263/200000000000 : ℝ) (396739530667/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0729_exp_lower
  have heNumeric : (2054901871691/1000000000000 : ℝ)/4 ≤ Real.exp (-85256481960127/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901871691/1000000000000 : ℝ)/4 ≤ Real.exp ((66801/524288 : ℝ)-(396739530667/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66801/524288 : ℝ) (33401/262144 : ℝ) (396739530667/500000000000 : ℝ) (2054901871691/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0730; no trusted numerical premise.
theorem cover8_leaf0730_exp_radius : (499005547976817227/500000000000000000 : ℝ) ≤ Real.exp ((-66803/4194304 : ℝ)/8) ∧ Real.exp ((-66803/4194304 : ℝ)/8) ≤ (199602219190726891/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66803/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0730_exp_lower : (920113466419078459/1000000000000000000 : ℝ) ≤ Real.exp ((-42628241141623/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628241141623/64000000000000 : ℝ)/8) ≤ (46005673320953923/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628241141623/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0730_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862733313/125000000000 : ℝ) ≤ 4*Real.exp (33401/262144 : ℝ)*Real.exp (-mu (radius 8 (66803/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862733313/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66803/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0730_exp_radius
  have hrNumeric : (492099544419/500000000000 : ℝ) ≤ Real.exp (-66803/4194304 : ℝ) ∧ Real.exp (-66803/4194304 : ℝ) ≤ (984199088839/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492099544419/500000000000 : ℝ) ≤ (radius 8 (66803/524288 : ℝ)) ∧ (radius 8 (66803/524288 : ℝ)) ≤ (984199088839/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66803/524288 : ℝ)) (492099544419/500000000000 : ℝ) (984199088839/1000000000000 : ℝ) (177065393367/1000000000000 : ℝ) (88532696687/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66803/524288 : ℝ)) (492099544419/500000000000 : ℝ) (984199088839/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492099544419/500000000000 : ℝ) (984199088839/1000000000000 : ℝ) (992099544419/1000000000000 : ℝ) (49604977221/50000000000 : ℝ) (198413617359/200000000000 : ℝ) (248017021699/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 1 (992099544419/1000000000000 : ℝ) (49604977221/50000000000 : ℝ) (198413617359/200000000000 : ℝ) (248017021699/250000000000 : ℝ) (992083815607/1000000000000 : ℝ) (124010476951/125000000000 : ℝ) (496041907741/500000000000 : ℝ) (248020953871/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 2 (992083815607/1000000000000 : ℝ) (124010476951/125000000000 : ℝ) (496041907741/500000000000 : ℝ) (248020953871/250000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 3 (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 4 (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 5 (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 6 (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66803/524288 : ℝ)) 7 (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66803/524288 : ℝ))) (177065393367/1000000000000 : ℝ) (88532696687/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177065393367/1000000000000 : ℝ) (88532696687/500000000000 : ℝ) (588532696683/1000000000000 : ℝ) (588532696687/1000000000000 : ℝ) (52598923671/125000000000 : ℝ) (210395694689/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 1 (588532696683/1000000000000 : ℝ) (588532696687/1000000000000 : ℝ) (52598923671/125000000000 : ℝ) (210395694689/500000000000 : ℝ) (20186481721/40000000000 : ℝ) (504662043033/1000000000000 : ℝ) (497643940107/1000000000000 : ℝ) (124410985029/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 2 (20186481721/40000000000 : ℝ) (504662043033/1000000000000 : ℝ) (497643940107/1000000000000 : ℝ) (124410985029/250000000000 : ℝ) (250576495783/500000000000 : ℝ) (20046119663/40000000000 : ℝ) (250570353151/500000000000 : ℝ) (62642588289/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 3 (250576495783/500000000000 : ℝ) (20046119663/40000000000 : ℝ) (250570353151/500000000000 : ℝ) (62642588289/125000000000 : ℝ) (250573424467/500000000000 : ℝ) (31321678059/62500000000 : ℝ) (3915209757/7812500000 : ℝ) (250573424453/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 4 (250573424467/500000000000 : ℝ) (31321678059/62500000000 : ℝ) (3915209757/7812500000 : ℝ) (250573424453/500000000000 : ℝ) (100229369783/200000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 5 (100229369783/200000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 6 (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66803/524288 : ℝ))) 7 (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66803/524288 : ℝ)) hmem 8 (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66803/524288 : ℝ))) hcmem 8 (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66803/524288 : ℝ)) (124010476943/125000000000 : ℝ) (496041907773/500000000000 : ℝ) (250573424457/500000000000 : ℝ) (20045873957/40000000000 : ℝ) (793480971187/1000000000000 : ℝ) (793480971207/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0730_exp_lower
  have heNumeric : (256862733313/125000000000 : ℝ)/4 ≤ Real.exp (-42628241141623/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862733313/125000000000 : ℝ)/4 ≤ Real.exp ((33401/262144 : ℝ)-(793480971207/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33401/262144 : ℝ) (66803/524288 : ℝ) (793480971207/1000000000000 : ℝ) (256862733313/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0731; no trusted numerical premise.
theorem cover8_leaf0731_exp_radius : (99801106621058647/100000000000000000 : ℝ) ≤ Real.exp ((-16701/1048576 : ℝ)/8) ∧ Real.exp ((-16701/1048576 : ℝ)/8) ≤ (998011066210586471/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16701/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0731_exp_lower : (920113466131155727/1000000000000000000 : ℝ) ≤ Real.exp ((-85256482603677/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256482603677/128000000000000 : ℝ)/8) ≤ (57507091633197233/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256482603677/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0731_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686273267/12500000000 : ℝ) ≤ 4*Real.exp (66803/524288 : ℝ)*Real.exp (-mu (radius 8 (16701/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (25686273267/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16701/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0731_exp_radius
  have hrNumeric : (984198854187/1000000000000 : ℝ) ≤ Real.exp (-16701/1048576 : ℝ) ∧ Real.exp (-16701/1048576 : ℝ) ≤ (246049713547/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984198854187/1000000000000 : ℝ) ≤ (radius 8 (16701/131072 : ℝ)) ∧ (radius 8 (16701/131072 : ℝ)) ≤ (246049713547/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16701/131072 : ℝ)) (984198854187/1000000000000 : ℝ) (246049713547/250000000000 : ℝ) (35413339529/200000000000 : ℝ) (177066697651/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16701/131072 : ℝ)) (984198854187/1000000000000 : ℝ) (246049713547/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984198854187/1000000000000 : ℝ) (246049713547/250000000000 : ℝ) (992099427093/1000000000000 : ℝ) (496049713547/500000000000 : ℝ) (992067968531/1000000000000 : ℝ) (992067968533/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 1 (992099427093/1000000000000 : ℝ) (496049713547/500000000000 : ℝ) (992067968531/1000000000000 : ℝ) (992067968533/1000000000000 : ℝ) (248020924453/250000000000 : ℝ) (496041848907/500000000000 : ℝ) (992083697687/1000000000000 : ℝ) (992083697689/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 2 (248020924453/250000000000 : ℝ) (496041848907/500000000000 : ℝ) (992083697687/1000000000000 : ℝ) (992083697689/1000000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 3 (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 4 (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 5 (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 6 (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16701/131072 : ℝ)) 7 (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16701/131072 : ℝ))) (35413339529/200000000000 : ℝ) (177066697651/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35413339529/200000000000 : ℝ) (177066697651/1000000000000 : ℝ) (294266674411/500000000000 : ℝ) (294266674413/500000000000 : ℝ) (420792939157/1000000000000 : ℝ) (84158587833/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 1 (294266674411/500000000000 : ℝ) (294266674413/500000000000 : ℝ) (420792939157/1000000000000 : ℝ) (84158587833/200000000000 : ℝ) (504663143989/1000000000000 : ℝ) (126165785999/250000000000 : ℝ) (6220564153/12500000000 : ℝ) (497645132247/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 2 (504663143989/1000000000000 : ℝ) (126165785999/250000000000 : ℝ) (6220564153/12500000000 : ℝ) (497645132247/1000000000000 : ℝ) (250577069057/500000000000 : ℝ) (250577069061/500000000000 : ℝ) (250570926599/500000000000 : ℝ) (250570926603/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 3 (250577069057/500000000000 : ℝ) (250577069061/500000000000 : ℝ) (250570926599/500000000000 : ℝ) (250570926603/500000000000 : ℝ) (62643499457/125000000000 : ℝ) (31321749729/62500000000 : ℝ) (250573997809/500000000000 : ℝ) (501147995627/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 4 (62643499457/125000000000 : ℝ) (31321749729/62500000000 : ℝ) (250573997809/500000000000 : ℝ) (501147995627/1000000000000 : ℝ) (501147995637/1000000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 5 (501147995637/1000000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 6 (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16701/131072 : ℝ))) 7 (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16701/131072 : ℝ)) hmem 8 (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16701/131072 : ℝ))) hcmem 8 (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16701/131072 : ℝ)) (992083697749/1000000000000 : ℝ) (124010462219/125000000000 : ℝ) (125286998909/250000000000 : ℝ) (250573997823/500000000000 : ℝ) (9918536013/12500000000 : ℝ) (793482881059/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0731_exp_lower
  have heNumeric : (25686273267/12500000000 : ℝ)/4 ≤ Real.exp (-85256482603677/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686273267/12500000000 : ℝ)/4 ≤ Real.exp ((66803/524288 : ℝ)-(793482881059/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66803/524288 : ℝ) (16701/131072 : ℝ) (793482881059/1000000000000 : ℝ) (25686273267/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0732; no trusted numerical premise.
theorem cover8_leaf0732_exp_radius : (998011036467539371/1000000000000000000 : ℝ) ≤ Real.exp ((-66805/4194304 : ℝ)/8) ∧ Real.exp ((-66805/4194304 : ℝ)/8) ≤ (249502759116884843/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66805/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0732_exp_lower : (460056732922134061/500000000000000000 : ℝ) ≤ Real.exp ((-21314120730739/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314120730739/32000000000000 : ℝ)/8) ≤ (920113465844268123/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314120730739/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0732_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450928117/500000000000 : ℝ) ≤ 4*Real.exp (16701/131072 : ℝ)*Real.exp (-mu (radius 8 (66805/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450928117/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66805/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0732_exp_radius
  have hrNumeric : (196839723907/200000000000 : ℝ) ≤ Real.exp (-66805/4194304 : ℝ) ∧ Real.exp (-66805/4194304 : ℝ) ≤ (61512413721/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196839723907/200000000000 : ℝ) ≤ (radius 8 (66805/524288 : ℝ)) ∧ (radius 8 (66805/524288 : ℝ)) ≤ (61512413721/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66805/524288 : ℝ)) (196839723907/200000000000 : ℝ) (61512413721/62500000000 : ℝ) (88534000959/500000000000 : ℝ) (7082720077/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66805/524288 : ℝ)) (196839723907/200000000000 : ℝ) (61512413721/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196839723907/200000000000 : ℝ) (61512413721/62500000000 : ℝ) (992099309767/1000000000000 : ℝ) (124012413721/125000000000 : ℝ) (992067850267/1000000000000 : ℝ) (992067850269/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 1 (992099309767/1000000000000 : ℝ) (124012413721/125000000000 : ℝ) (992067850267/1000000000000 : ℝ) (992067850269/1000000000000 : ℝ) (992083580017/1000000000000 : ℝ) (992083580019/1000000000000 : ℝ) (248020894973/250000000000 : ℝ) (496041789947/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 2 (992083580017/1000000000000 : ℝ) (992083580019/1000000000000 : ℝ) (248020894973/250000000000 : ℝ) (496041789947/500000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 3 (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 4 (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 5 (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 6 (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66805/524288 : ℝ)) 7 (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66805/524288 : ℝ))) (88534000959/500000000000 : ℝ) (7082720077/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88534000959/500000000000 : ℝ) (7082720077/40000000000 : ℝ) (588534000959/1000000000000 : ℝ) (588534000963/1000000000000 : ℝ) (210397244467/500000000000 : ℝ) (26299655559/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 1 (588534000959/1000000000000 : ℝ) (588534000963/1000000000000 : ℝ) (210397244467/500000000000 : ℝ) (26299655559/62500000000 : ℝ) (252332122473/500000000000 : ℝ) (252332122477/500000000000 : ℝ) (124411581091/250000000000 : ℝ) (497646324373/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 2 (252332122473/500000000000 : ℝ) (252332122477/500000000000 : ℝ) (124411581091/250000000000 : ℝ) (497646324373/1000000000000 : ℝ) (100231056931/200000000000 : ℝ) (62644410583/125000000000 : ℝ) (250571500043/500000000000 : ℝ) (100228600019/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 3 (100231056931/200000000000 : ℝ) (62644410583/125000000000 : ℝ) (250571500043/500000000000 : ℝ) (100228600019/200000000000 : ℝ) (50114914237/100000000000 : ℝ) (25057457119/50000000000 : ℝ) (125287285583/250000000000 : ℝ) (250574571171/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 4 (50114914237/100000000000 : ℝ) (25057457119/50000000000 : ℝ) (125287285583/250000000000 : ℝ) (250574571171/500000000000 : ℝ) (501149142351/1000000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 5 (501149142351/1000000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 6 (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66805/524288 : ℝ))) 7 (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66805/524288 : ℝ)) hmem 8 (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66805/524288 : ℝ))) hcmem 8 (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66805/524288 : ℝ)) (496041789977/500000000000 : ℝ) (992083579957/1000000000000 : ℝ) (10022982847/20000000000 : ℝ) (501149142361/1000000000000 : ℝ) (396742395441/500000000000 : ℝ) (396742395451/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0732_exp_lower
  have heNumeric : (1027450928117/500000000000 : ℝ)/4 ≤ Real.exp (-21314120730739/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450928117/500000000000 : ℝ)/4 ≤ Real.exp ((16701/131072 : ℝ)-(396742395451/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16701/131072 : ℝ) (66805/524288 : ℝ) (396742395451/500000000000 : ℝ) (1027450928117/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0733; no trusted numerical premise.
theorem cover8_leaf0733_exp_radius : (998011006724493159/1000000000000000000 : ℝ) ≤ Real.exp ((-33403/2097152 : ℝ)/8) ∧ Real.exp ((-33403/2097152 : ℝ)/8) ≤ (24950275168112329/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33403/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0733_exp_lower : (920113465560830943/1000000000000000000 : ℝ) ≤ Real.exp ((-17051296647679/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051296647679/25600000000000 : ℝ)/8) ≤ (28753545798775967/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051296647679/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0733_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490185117/100000000000 : ℝ) ≤ 4*Real.exp (66805/524288 : ℝ)*Real.exp (-mu (radius 8 (33403/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490185117/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33403/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0733_exp_radius
  have hrNumeric : (246049596221/250000000000 : ℝ) ≤ Real.exp (-33403/2097152 : ℝ) ∧ Real.exp (-33403/2097152 : ℝ) ≤ (196839676977/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246049596221/250000000000 : ℝ) ≤ (radius 8 (33403/262144 : ℝ)) ∧ (radius 8 (33403/262144 : ℝ)) ≤ (196839676977/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33403/262144 : ℝ)) (246049596221/250000000000 : ℝ) (196839676977/200000000000 : ℝ) (2766707909/15625000000 : ℝ) (88534653091/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33403/262144 : ℝ)) (246049596221/250000000000 : ℝ) (196839676977/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246049596221/250000000000 : ℝ) (196839676977/200000000000 : ℝ) (496049596221/500000000000 : ℝ) (992099192443/1000000000000 : ℝ) (248016933001/250000000000 : ℝ) (198413546401/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 1 (496049596221/500000000000 : ℝ) (992099192443/1000000000000 : ℝ) (248016933001/250000000000 : ℝ) (198413546401/200000000000 : ℝ) (992083462223/1000000000000 : ℝ) (62005216389/62500000000 : ℝ) (496041731049/500000000000 : ℝ) (9920834621/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 2 (992083462223/1000000000000 : ℝ) (62005216389/62500000000 : ℝ) (496041731049/500000000000 : ℝ) (9920834621/10000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 3 (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 4 (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 5 (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 6 (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33403/262144 : ℝ)) 7 (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33403/262144 : ℝ))) (2766707909/15625000000 : ℝ) (88534653091/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2766707909/15625000000 : ℝ) (88534653091/500000000000 : ℝ) (18391707909/31250000000 : ℝ) (588534653091/1000000000000 : ℝ) (13149876209/31250000000 : ℝ) (52599504837/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 1 (18391707909/31250000000 : ℝ) (588534653091/1000000000000 : ℝ) (13149876209/31250000000 : ℝ) (52599504837/125000000000 : ℝ) (15770792059/31250000000 : ℝ) (252332672947/500000000000 : ℝ) (497647516471/1000000000000 : ℝ) (248823758239/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 2 (15770792059/31250000000 : ℝ) (252332672947/500000000000 : ℝ) (497647516471/1000000000000 : ℝ) (248823758239/500000000000 : ℝ) (501156431179/1000000000000 : ℝ) (250578215593/500000000000 : ℝ) (501144146957/1000000000000 : ℝ) (100228829393/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 3 (501156431179/1000000000000 : ℝ) (250578215593/500000000000 : ℝ) (501144146957/1000000000000 : ℝ) (100228829393/200000000000 : ℝ) (125287572267/250000000000 : ℝ) (125287572269/250000000000 : ℝ) (50115028903/100000000000 : ℝ) (250575144519/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 4 (125287572267/250000000000 : ℝ) (125287572269/250000000000 : ℝ) (50115028903/100000000000 : ℝ) (250575144519/500000000000 : ℝ) (501150289049/1000000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 5 (501150289049/1000000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 6 (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33403/262144 : ℝ))) 7 (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33403/262144 : ℝ)) hmem 8 (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33403/262144 : ℝ))) hcmem 8 (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33403/262144 : ℝ)) (12401043277/12500000000 : ℝ) (496041731081/500000000000 : ℝ) (62643786131/125000000000 : ℝ) (501150289057/1000000000000 : ℝ) (396743350349/500000000000 : ℝ) (158697340143/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0733_exp_lower
  have heNumeric : (205490185117/100000000000 : ℝ)/4 ≤ Real.exp (-17051296647679/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490185117/100000000000 : ℝ)/4 ≤ Real.exp ((66805/524288 : ℝ)-(158697340143/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66805/524288 : ℝ) (33403/262144 : ℝ) (158697340143/200000000000 : ℝ) (205490185117/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0734; no trusted numerical premise.
theorem cover8_leaf0734_exp_radius : (998010976981447833/1000000000000000000 : ℝ) ≤ Real.exp ((-66807/4194304 : ℝ)/8) ∧ Real.exp ((-66807/4194304 : ℝ)/8) ≤ (499005488490723917/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66807/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0734_exp_lower : (7188386447493117/7812500000000000 : ℝ) ≤ Real.exp ((-42628241775957/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628241775957/64000000000000 : ℝ)/8) ≤ (920113465279118977/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628241775957/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0734_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901846137/1000000000000 : ℝ) ≤ 4*Real.exp (33403/262144 : ℝ)*Real.exp (-mu (radius 8 (66807/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901846137/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66807/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0734_exp_radius
  have hrNumeric : (984198150233/1000000000000 : ℝ) ≤ Real.exp (-66807/4194304 : ℝ) ∧ Real.exp (-66807/4194304 : ℝ) ≤ (492099075117/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984198150233/1000000000000 : ℝ) ≤ (radius 8 (66807/524288 : ℝ)) ∧ (radius 8 (66807/524288 : ℝ)) ≤ (492099075117/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66807/524288 : ℝ)) (984198150233/1000000000000 : ℝ) (492099075117/500000000000 : ℝ) (22133826303/125000000000 : ℝ) (17707061043/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66807/524288 : ℝ)) (984198150233/1000000000000 : ℝ) (492099075117/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984198150233/1000000000000 : ℝ) (492099075117/500000000000 : ℝ) (248024768779/250000000000 : ℝ) (992099075117/1000000000000 : ℝ) (49603380687/50000000000 : ℝ) (496033806871/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 1 (248024768779/250000000000 : ℝ) (992099075117/1000000000000 : ℝ) (49603380687/50000000000 : ℝ) (496033806871/500000000000 : ℝ) (248020836107/250000000000 : ℝ) (99208334443/100000000000 : ℝ) (992083344303/1000000000000 : ℝ) (198416668861/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 2 (248020836107/250000000000 : ℝ) (99208334443/100000000000 : ℝ) (992083344303/1000000000000 : ℝ) (198416668861/200000000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 3 (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 4 (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 5 (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 6 (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66807/524288 : ℝ)) 7 (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66807/524288 : ℝ))) (22133826303/125000000000 : ℝ) (17707061043/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22133826303/125000000000 : ℝ) (17707061043/100000000000 : ℝ) (147133826303/250000000000 : ℝ) (117707061043/200000000000 : ℝ) (52599698553/125000000000 : ℝ) (26299849277/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 1 (147133826303/250000000000 : ℝ) (117707061043/200000000000 : ℝ) (52599698553/125000000000 : ℝ) (26299849277/62500000000 : ℝ) (252333223409/500000000000 : ℝ) (63083305853/125000000000 : ℝ) (124412177141/250000000000 : ℝ) (497648708571/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 2 (252333223409/500000000000 : ℝ) (63083305853/125000000000 : ℝ) (124412177141/250000000000 : ℝ) (497648708571/1000000000000 : ℝ) (501157577691/1000000000000 : ℝ) (250578788849/500000000000 : ℝ) (62643161727/125000000000 : ℝ) (489399701/976562500 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 3 (501157577691/1000000000000 : ℝ) (250578788849/500000000000 : ℝ) (62643161727/125000000000 : ℝ) (489399701/976562500 : ℝ) (501151435753/1000000000000 : ℝ) (501151435761/1000000000000 : ℝ) (100230287143/200000000000 : ℝ) (125287858931/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 4 (501151435753/1000000000000 : ℝ) (501151435761/1000000000000 : ℝ) (100230287143/200000000000 : ℝ) (125287858931/250000000000 : ℝ) (250575717867/500000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 5 (250575717867/500000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 6 (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66807/524288 : ℝ))) 7 (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66807/524288 : ℝ)) hmem 8 (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66807/524288 : ℝ))) hcmem 8 (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66807/524288 : ℝ)) (198416668873/200000000000 : ℝ) (62005209023/62500000000 : ℝ) (501151435733/1000000000000 : ℝ) (501151435743/1000000000000 : ℝ) (396744305247/500000000000 : ℝ) (793488610513/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0734_exp_lower
  have heNumeric : (2054901846137/1000000000000 : ℝ)/4 ≤ Real.exp (-42628241775957/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901846137/1000000000000 : ℝ)/4 ≤ Real.exp ((33403/262144 : ℝ)-(793488610513/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33403/262144 : ℝ) (66807/524288 : ℝ) (793488610513/1000000000000 : ℝ) (2054901846137/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0735; no trusted numerical premise.
theorem cover8_leaf0735_exp_radius : (499005473619201697/500000000000000000 : ℝ) ≤ Real.exp ((-8351/524288 : ℝ)/8) ∧ Real.exp ((-8351/524288 : ℝ)/8) ≤ (199602189447680679/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8351/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0735_exp_lower : (230028366249955577/250000000000000000 : ℝ) ≤ Real.exp ((-17051296772549/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051296772549/25600000000000 : ℝ)/8) ≤ (920113464999822309/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051296772549/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0735_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901841147/1000000000000 : ℝ) ≤ 4*Real.exp (66807/524288 : ℝ)*Real.exp (-mu (radius 8 (8351/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901841147/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8351/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0735_exp_radius
  have hrNumeric : (492098957791/500000000000 : ℝ) ≤ Real.exp (-8351/524288 : ℝ) ∧ Real.exp (-8351/524288 : ℝ) ≤ (984197915583/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492098957791/500000000000 : ℝ) ≤ (radius 8 (8351/65536 : ℝ)) ∧ (radius 8 (8351/65536 : ℝ)) ≤ (984197915583/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8351/65536 : ℝ)) (492098957791/500000000000 : ℝ) (984197915583/1000000000000 : ℝ) (88535957331/500000000000 : ℝ) (44267978667/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8351/65536 : ℝ)) (492098957791/500000000000 : ℝ) (984197915583/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492098957791/500000000000 : ℝ) (984197915583/1000000000000 : ℝ) (992098957791/1000000000000 : ℝ) (31003092431/31250000000 : ℝ) (248016873869/250000000000 : ℝ) (496033747739/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 1 (992098957791/1000000000000 : ℝ) (31003092431/31250000000 : ℝ) (248016873869/250000000000 : ℝ) (496033747739/500000000000 : ℝ) (992083226633/1000000000000 : ℝ) (198416645327/200000000000 : ℝ) (248020806627/250000000000 : ℝ) (992083226511/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 2 (992083226633/1000000000000 : ℝ) (198416645327/200000000000 : ℝ) (248020806627/250000000000 : ℝ) (992083226511/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 3 (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 4 (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 5 (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 6 (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8351/65536 : ℝ)) 7 (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8351/65536 : ℝ))) (88535957331/500000000000 : ℝ) (44267978667/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88535957331/500000000000 : ℝ) (44267978667/250000000000 : ℝ) (588535957331/1000000000000 : ℝ) (294267978667/500000000000 : ℝ) (420799138143/1000000000000 : ℝ) (420799138151/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 1 (588535957331/1000000000000 : ℝ) (294267978667/500000000000 : ℝ) (420799138143/1000000000000 : ℝ) (420799138151/1000000000000 : ℝ) (504667547737/1000000000000 : ℝ) (504667547743/1000000000000 : ℝ) (124412475161/250000000000 : ℝ) (497649900651/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 2 (504667547737/1000000000000 : ℝ) (504667547743/1000000000000 : ℝ) (124412475161/250000000000 : ℝ) (497649900651/1000000000000 : ℝ) (50115872419/100000000000 : ℝ) (501158724197/1000000000000 : ℝ) (501146440663/1000000000000 : ℝ) (50114644067/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 3 (50115872419/100000000000 : ℝ) (501158724197/1000000000000 : ℝ) (501146440663/1000000000000 : ℝ) (50114644067/100000000000 : ℝ) (250576291213/500000000000 : ℝ) (250576291217/500000000000 : ℝ) (125288145597/250000000000 : ℝ) (125288145599/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 4 (250576291213/500000000000 : ℝ) (250576291217/500000000000 : ℝ) (125288145597/250000000000 : ℝ) (125288145599/250000000000 : ℝ) (501152582407/1000000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 5 (501152582407/1000000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 6 (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8351/65536 : ℝ))) 7 (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8351/65536 : ℝ)) hmem 8 (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8351/65536 : ℝ))) hcmem 8 (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8351/65536 : ℝ)) (99208322657/100000000000 : ℝ) (992083226573/1000000000000 : ℝ) (250576291203/500000000000 : ℝ) (100230516483/200000000000 : ℝ) (49593157517/62500000000 : ℝ) (79349052029/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0735_exp_lower
  have heNumeric : (2054901841147/1000000000000 : ℝ)/4 ≤ Real.exp (-17051296772549/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901841147/1000000000000 : ℝ)/4 ≤ Real.exp ((66807/524288 : ℝ)-(79349052029/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66807/524288 : ℝ) (8351/65536 : ℝ) (79349052029/100000000000 : ℝ) (2054901841147/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0736; no trusted numerical premise.
theorem cover8_leaf0736_exp_radius : (998010917495359841/1000000000000000000 : ℝ) ≤ Real.exp ((-66809/4194304 : ℝ)/8) ∧ Real.exp ((-66809/4194304 : ℝ)/8) ≤ (499005458747679921/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66809/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0736_exp_lower : (920113464722710909/1000000000000000000 : ℝ) ≤ Real.exp ((-10657060521393/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657060521393/16000000000000 : ℝ)/8) ≤ (92011346472271091/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657060521393/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0736_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725459049/250000000000 : ℝ) ≤ 4*Real.exp (8351/65536 : ℝ)*Real.exp (-mu (radius 8 (66809/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725459049/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66809/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0736_exp_radius
  have hrNumeric : (984197680931/1000000000000 : ℝ) ≤ Real.exp (-66809/4194304 : ℝ) ∧ Real.exp (-66809/4194304 : ℝ) ≤ (246049420233/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984197680931/1000000000000 : ℝ) ≤ (radius 8 (66809/524288 : ℝ)) ∧ (radius 8 (66809/524288 : ℝ)) ≤ (246049420233/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66809/524288 : ℝ)) (984197680931/1000000000000 : ℝ) (246049420233/250000000000 : ℝ) (17707321889/100000000000 : ℝ) (11067076181/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66809/524288 : ℝ)) (984197680931/1000000000000 : ℝ) (246049420233/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984197680931/1000000000000 : ℝ) (246049420233/250000000000 : ℝ) (198419768093/200000000000 : ℝ) (496049420233/500000000000 : ℝ) (992067377213/1000000000000 : ℝ) (496033688607/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 1 (198419768093/200000000000 : ℝ) (496049420233/500000000000 : ℝ) (992067377213/1000000000000 : ℝ) (496033688607/500000000000 : ℝ) (992083108839/1000000000000 : ℝ) (24802077721/25000000000 : ℝ) (496041554357/500000000000 : ℝ) (248020777179/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 2 (992083108839/1000000000000 : ℝ) (24802077721/25000000000 : ℝ) (496041554357/500000000000 : ℝ) (248020777179/250000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 3 (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 4 (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 5 (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 6 (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66809/524288 : ℝ)) 7 (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66809/524288 : ℝ))) (17707321889/100000000000 : ℝ) (11067076181/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17707321889/100000000000 : ℝ) (11067076181/62500000000 : ℝ) (117707321889/200000000000 : ℝ) (73567076181/125000000000 : ℝ) (105200171961/250000000000 : ℝ) (105200171963/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 1 (117707321889/200000000000 : ℝ) (73567076181/125000000000 : ℝ) (105200171961/250000000000 : ℝ) (105200171963/250000000000 : ℝ) (126167162161/250000000000 : ℝ) (10093372973/20000000000 : ℝ) (49765109271/100000000000 : ℝ) (497651092717/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 2 (126167162161/250000000000 : ℝ) (10093372973/20000000000 : ℝ) (49765109271/100000000000 : ℝ) (497651092717/1000000000000 : ℝ) (501159870677/1000000000000 : ℝ) (125289967671/250000000000 : ℝ) (501147587497/1000000000000 : ℝ) (31321724219/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 3 (501159870677/1000000000000 : ℝ) (125289967671/250000000000 : ℝ) (501147587497/1000000000000 : ℝ) (31321724219/62500000000 : ℝ) (501153729087/1000000000000 : ℝ) (250576864547/500000000000 : ℝ) (501153729049/1000000000000 : ℝ) (501153729057/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 4 (501153729087/1000000000000 : ℝ) (250576864547/500000000000 : ℝ) (501153729049/1000000000000 : ℝ) (501153729057/1000000000000 : ℝ) (125288432267/250000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 5 (125288432267/250000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 6 (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66809/524288 : ℝ))) 7 (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66809/524288 : ℝ)) hmem 8 (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66809/524288 : ℝ))) hcmem 8 (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66809/524288 : ℝ)) (124010388597/125000000000 : ℝ) (496041554389/500000000000 : ℝ) (501153729067/1000000000000 : ℝ) (125288432269/250000000000 : ℝ) (49593276877/62500000000 : ℝ) (24796638439/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0736_exp_lower
  have heNumeric : (513725459049/250000000000 : ℝ)/4 ≤ Real.exp (-10657060521393/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725459049/250000000000 : ℝ)/4 ≤ Real.exp ((8351/65536 : ℝ)-(24796638439/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8351/65536 : ℝ) (66809/524288 : ℝ) (24796638439/31250000000 : ℝ) (513725459049/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0737; no trusted numerical premise.
theorem cover8_leaf0737_exp_radius : (39920435510092687/40000000000000000 : ℝ) ≤ Real.exp ((-33405/2097152 : ℝ)/8) ∧ Real.exp ((-33405/2097152 : ℝ)/8) ≤ (124751360969039647/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33405/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0737_exp_lower : (460056732223834883/500000000000000000 : ℝ) ≤ Real.exp ((-85256484477239/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256484477239/128000000000000 : ℝ)/8) ≤ (920113464447669767/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256484477239/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0737_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450915641/500000000000 : ℝ) ≤ 4*Real.exp (66809/524288 : ℝ)*Real.exp (-mu (radius 8 (33405/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450915641/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33405/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0737_exp_radius
  have hrNumeric : (24604936157/25000000000 : ℝ) ≤ Real.exp (-33405/2097152 : ℝ) ∧ Real.exp (-33405/2097152 : ℝ) ≤ (984197446281/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24604936157/25000000000 : ℝ) ≤ (radius 8 (33405/262144 : ℝ)) ∧ (radius 8 (33405/262144 : ℝ)) ≤ (984197446281/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33405/262144 : ℝ)) (24604936157/25000000000 : ℝ) (984197446281/1000000000000 : ℝ) (44268630777/250000000000 : ℝ) (88537261557/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33405/262144 : ℝ)) (24604936157/25000000000 : ℝ) (984197446281/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24604936157/25000000000 : ℝ) (984197446281/1000000000000 : ℝ) (49604936157/50000000000 : ℝ) (992098723141/1000000000000 : ℝ) (992067258949/1000000000000 : ℝ) (992067258951/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 1 (49604936157/50000000000 : ℝ) (992098723141/1000000000000 : ℝ) (992067258949/1000000000000 : ℝ) (992067258951/1000000000000 : ℝ) (248020747761/250000000000 : ℝ) (496041495523/500000000000 : ℝ) (992082990919/1000000000000 : ℝ) (496041495461/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 2 (248020747761/250000000000 : ℝ) (496041495523/500000000000 : ℝ) (992082990919/1000000000000 : ℝ) (496041495461/500000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 3 (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 4 (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 5 (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 6 (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33405/262144 : ℝ)) 7 (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33405/262144 : ℝ))) (44268630777/250000000000 : ℝ) (88537261557/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44268630777/250000000000 : ℝ) (88537261557/500000000000 : ℝ) (294268630777/500000000000 : ℝ) (588537261557/1000000000000 : ℝ) (420802237527/1000000000000 : ℝ) (84160447507/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 1 (294268630777/500000000000 : ℝ) (588537261557/1000000000000 : ℝ) (420802237527/1000000000000 : ℝ) (84160447507/200000000000 : ℝ) (25233487477/50000000000 : ℝ) (252334874773/500000000000 : ℝ) (497652284763/1000000000000 : ℝ) (49765228477/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 2 (25233487477/50000000000 : ℝ) (252334874773/500000000000 : ℝ) (497652284763/1000000000000 : ℝ) (49765228477/100000000000 : ℝ) (501161017151/1000000000000 : ℝ) (250580508579/500000000000 : ℝ) (250574367159/500000000000 : ℝ) (250574367163/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 3 (501161017151/1000000000000 : ℝ) (250580508579/500000000000 : ℝ) (250574367159/500000000000 : ℝ) (250574367163/500000000000 : ℝ) (250577437867/500000000000 : ℝ) (250577437871/500000000000 : ℝ) (31322179731/62500000000 : ℝ) (100230975141/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 4 (250577437867/500000000000 : ℝ) (250577437871/500000000000 : ℝ) (31322179731/62500000000 : ℝ) (100230975141/200000000000 : ℝ) (100230975143/200000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 5 (100230975143/200000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 6 (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33405/262144 : ℝ))) 7 (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33405/262144 : ℝ)) hmem 8 (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33405/262144 : ℝ))) hcmem 8 (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33405/262144 : ℝ)) (992082990981/1000000000000 : ℝ) (124010373873/125000000000 : ℝ) (250577437857/500000000000 : ℝ) (125288718931/250000000000 : ℝ) (793494339769/1000000000000 : ℝ) (198373584947/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0737_exp_lower
  have heNumeric : (1027450915641/500000000000 : ℝ)/4 ≤ Real.exp (-85256484477239/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450915641/500000000000 : ℝ)/4 ≤ Real.exp ((66809/524288 : ℝ)-(198373584947/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66809/524288 : ℝ) (33405/262144 : ℝ) (198373584947/250000000000 : ℝ) (1027450915641/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0738; no trusted numerical premise.
theorem cover8_leaf0738_exp_radius : (199602171601855079/200000000000000000 : ℝ) ≤ Real.exp ((-66811/4194304 : ℝ)/8) ∧ Real.exp ((-66811/4194304 : ℝ)/8) ≤ (249502714502318849/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66811/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0738_exp_lower : (460056732087579467/500000000000000000 : ℝ) ≤ Real.exp ((-42628242390259/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628242390259/64000000000000 : ℝ)/8) ≤ (184022692835031787/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628242390259/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0738_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901826413/1000000000000 : ℝ) ≤ 4*Real.exp (33405/262144 : ℝ)*Real.exp (-mu (radius 8 (66811/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901826413/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66811/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0738_exp_radius
  have hrNumeric : (984197211629/1000000000000 : ℝ) ≤ Real.exp (-66811/4194304 : ℝ) ∧ Real.exp (-66811/4194304 : ℝ) ≤ (98419721163/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984197211629/1000000000000 : ℝ) ≤ (radius 8 (66811/524288 : ℝ)) ∧ (radius 8 (66811/524288 : ℝ)) ≤ (98419721163/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66811/524288 : ℝ)) (984197211629/1000000000000 : ℝ) (98419721163/100000000000 : ℝ) (44268956829/250000000000 : ℝ) (88537913661/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66811/524288 : ℝ)) (984197211629/1000000000000 : ℝ) (98419721163/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984197211629/1000000000000 : ℝ) (98419721163/100000000000 : ℝ) (496049302907/500000000000 : ℝ) (198419721163/200000000000 : ℝ) (496033570343/500000000000 : ℝ) (992067140687/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 1 (496049302907/500000000000 : ℝ) (198419721163/200000000000 : ℝ) (496033570343/500000000000 : ℝ) (992067140687/1000000000000 : ℝ) (3968331493/4000000000 : ℝ) (992082873251/1000000000000 : ℝ) (1587332597/1600000000 : ℝ) (992082873127/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 2 (3968331493/4000000000 : ℝ) (992082873251/1000000000000 : ℝ) (1587332597/1600000000 : ℝ) (992082873127/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 3 (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 4 (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 5 (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 6 (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66811/524288 : ℝ)) 7 (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66811/524288 : ℝ))) (44268956829/250000000000 : ℝ) (88537913661/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44268956829/250000000000 : ℝ) (88537913661/500000000000 : ℝ) (294268956829/500000000000 : ℝ) (588537913661/1000000000000 : ℝ) (420803787193/1000000000000 : ℝ) (420803787201/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 1 (294268956829/500000000000 : ℝ) (588537913661/1000000000000 : ℝ) (420803787193/1000000000000 : ℝ) (420803787201/1000000000000 : ℝ) (20186834017/40000000000 : ℝ) (504670850431/1000000000000 : ℝ) (248826738401/500000000000 : ℝ) (497653476809/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 2 (20186834017/40000000000 : ℝ) (504670850431/1000000000000 : ℝ) (248826738401/500000000000 : ℝ) (497653476809/1000000000000 : ℝ) (501162163613/1000000000000 : ℝ) (25058108181/50000000000 : ℝ) (62643735141/125000000000 : ℝ) (100229976227/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 3 (501162163613/1000000000000 : ℝ) (25058108181/50000000000 : ℝ) (62643735141/125000000000 : ℝ) (100229976227/200000000000 : ℝ) (50115602237/100000000000 : ℝ) (250578011189/500000000000 : ℝ) (125289005583/250000000000 : ℝ) (25057801117/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 4 (50115602237/100000000000 : ℝ) (250578011189/500000000000 : ℝ) (125289005583/250000000000 : ℝ) (25057801117/50000000000 : ℝ) (501156022351/1000000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 5 (501156022351/1000000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 6 (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66811/524288 : ℝ))) 7 (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66811/524288 : ℝ)) hmem 8 (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66811/524288 : ℝ))) hcmem 8 (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66811/524288 : ℝ)) (992082873187/1000000000000 : ℝ) (992082873189/1000000000000 : ℝ) (10023120447/20000000000 : ℝ) (501156022359/1000000000000 : ℝ) (793496249489/1000000000000 : ℝ) (396748124753/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0738_exp_lower
  have heNumeric : (2054901826413/1000000000000 : ℝ)/4 ≤ Real.exp (-42628242390259/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901826413/1000000000000 : ℝ)/4 ≤ Real.exp ((33405/262144 : ℝ)-(396748124753/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33405/262144 : ℝ) (66811/524288 : ℝ) (396748124753/500000000000 : ℝ) (2054901826413/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0739; no trusted numerical premise.
theorem cover8_leaf0739_exp_radius : (998010828266234501/1000000000000000000 : ℝ) ≤ Real.exp ((-16703/1048576 : ℝ)/8) ∧ Real.exp ((-16703/1048576 : ℝ)/8) ≤ (499005414133117251/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16703/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0739_exp_lower : (920113463904028273/1000000000000000000 : ℝ) ≤ Real.exp ((-85256485082261/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256485082261/128000000000000 : ℝ)/8) ≤ (460056731952014137/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256485082261/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0739_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901821569/1000000000000 : ℝ) ≤ 4*Real.exp (66811/524288 : ℝ)*Real.exp (-mu (radius 8 (16703/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901821569/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16703/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0739_exp_radius
  have hrNumeric : (492098488489/500000000000 : ℝ) ≤ Real.exp (-16703/1048576 : ℝ) ∧ Real.exp (-16703/1048576 : ℝ) ≤ (984196976979/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492098488489/500000000000 : ℝ) ≤ (radius 8 (16703/131072 : ℝ)) ∧ (radius 8 (16703/131072 : ℝ)) ≤ (984196976979/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16703/131072 : ℝ)) (492098488489/500000000000 : ℝ) (984196976979/1000000000000 : ℝ) (88538565757/500000000000 : ℝ) (177077131521/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16703/131072 : ℝ)) (492098488489/500000000000 : ℝ) (984196976979/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492098488489/500000000000 : ℝ) (984196976979/1000000000000 : ℝ) (992098488489/1000000000000 : ℝ) (99209848849/100000000000 : ℝ) (496033511211/500000000000 : ℝ) (992067022423/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 1 (992098488489/1000000000000 : ℝ) (99209848849/100000000000 : ℝ) (496033511211/500000000000 : ℝ) (992067022423/1000000000000 : ℝ) (198416551091/200000000000 : ℝ) (992082755457/1000000000000 : ℝ) (99208275533/100000000000 : ℝ) (248020688833/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 2 (198416551091/200000000000 : ℝ) (992082755457/1000000000000 : ℝ) (99208275533/100000000000 : ℝ) (248020688833/250000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 3 (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 4 (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 5 (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 6 (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16703/131072 : ℝ)) 7 (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16703/131072 : ℝ))) (88538565757/500000000000 : ℝ) (177077131521/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88538565757/500000000000 : ℝ) (177077131521/1000000000000 : ℝ) (588538565757/1000000000000 : ℝ) (588538565761/1000000000000 : ℝ) (420805336841/1000000000000 : ℝ) (8416106737/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 1 (588538565757/1000000000000 : ℝ) (588538565761/1000000000000 : ℝ) (420805336841/1000000000000 : ℝ) (8416106737/20000000000 : ℝ) (504671951299/1000000000000 : ℝ) (252335975653/500000000000 : ℝ) (124413667207/250000000000 : ℝ) (497654668837/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 2 (504671951299/1000000000000 : ℝ) (252335975653/500000000000 : ℝ) (124413667207/250000000000 : ℝ) (497654668837/1000000000000 : ℝ) (501163310063/1000000000000 : ℝ) (62645413759/125000000000 : ℝ) (20046041117/40000000000 : ℝ) (250575513967/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 3 (501163310063/1000000000000 : ℝ) (62645413759/125000000000 : ℝ) (20046041117/40000000000 : ℝ) (250575513967/500000000000 : ℝ) (250578584497/500000000000 : ℝ) (501157169003/1000000000000 : ℝ) (125289292239/250000000000 : ℝ) (250578584483/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 4 (250578584497/500000000000 : ℝ) (501157169003/1000000000000 : ℝ) (125289292239/250000000000 : ℝ) (250578584483/500000000000 : ℝ) (20046286759/40000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 5 (20046286759/40000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 6 (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16703/131072 : ℝ))) 7 (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16703/131072 : ℝ)) hmem 8 (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16703/131072 : ℝ))) hcmem 8 (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16703/131072 : ℝ)) (15501293053/15625000000 : ℝ) (198416551079/200000000000 : ℝ) (250578584487/500000000000 : ℝ) (100231433797/200000000000 : ℝ) (793498159191/1000000000000 : ℝ) (198374539803/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0739_exp_lower
  have heNumeric : (2054901821569/1000000000000 : ℝ)/4 ≤ Real.exp (-85256485082261/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901821569/1000000000000 : ℝ)/4 ≤ Real.exp ((66811/524288 : ℝ)-(198374539803/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66811/524288 : ℝ) (16703/131072 : ℝ) (198374539803/250000000000 : ℝ) (2054901821569/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0740; no trusted numerical premise.
theorem cover8_leaf0740_exp_radius : (499005399261597247/500000000000000000 : ℝ) ≤ Real.exp ((-66813/4194304 : ℝ)/8) ∧ Real.exp ((-66813/4194304 : ℝ)/8) ≤ (199602159704638899/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66813/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0740_exp_lower : (920113463635887981/1000000000000000000 : ℝ) ≤ Real.exp ((-21314121345169/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314121345169/32000000000000 : ℝ)/8) ≤ (460056731817943991/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314121345169/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0740_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450908389/500000000000 : ℝ) ≤ 4*Real.exp (16703/131072 : ℝ)*Real.exp (-mu (radius 8 (66813/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450908389/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66813/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0740_exp_radius
  have hrNumeric : (984196742327/1000000000000 : ℝ) ≤ Real.exp (-66813/4194304 : ℝ) ∧ Real.exp (-66813/4194304 : ℝ) ≤ (123024592791/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984196742327/1000000000000 : ℝ) ≤ (radius 8 (66813/524288 : ℝ)) ∧ (radius 8 (66813/524288 : ℝ)) ≤ (123024592791/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66813/524288 : ℝ)) (984196742327/1000000000000 : ℝ) (123024592791/125000000000 : ℝ) (88539217851/500000000000 : ℝ) (177078435709/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66813/524288 : ℝ)) (984196742327/1000000000000 : ℝ) (123024592791/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984196742327/1000000000000 : ℝ) (123024592791/125000000000 : ℝ) (992098371163/1000000000000 : ℝ) (248024592791/250000000000 : ℝ) (496033452079/500000000000 : ℝ) (6200418151/6250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 1 (992098371163/1000000000000 : ℝ) (248024592791/250000000000 : ℝ) (496033452079/500000000000 : ℝ) (6200418151/6250000000 : ℝ) (49604131883/50000000000 : ℝ) (496041318831/500000000000 : ℝ) (198416527507/200000000000 : ℝ) (496041318769/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 2 (49604131883/50000000000 : ℝ) (496041318831/500000000000 : ℝ) (198416527507/200000000000 : ℝ) (496041318769/500000000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 3 (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 4 (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 5 (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 6 (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66813/524288 : ℝ)) 7 (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66813/524288 : ℝ))) (88539217851/500000000000 : ℝ) (177078435709/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88539217851/500000000000 : ℝ) (177078435709/1000000000000 : ℝ) (588539217851/1000000000000 : ℝ) (117707843571/200000000000 : ℝ) (420806886471/1000000000000 : ℝ) (420806886481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 1 (588539217851/1000000000000 : ℝ) (117707843571/200000000000 : ℝ) (420806886471/1000000000000 : ℝ) (420806886481/1000000000000 : ℝ) (504673052161/1000000000000 : ℝ) (63084131521/125000000000 : ℝ) (497655860841/1000000000000 : ℝ) (9953117217/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 2 (504673052161/1000000000000 : ℝ) (63084131521/125000000000 : ℝ) (497655860841/1000000000000 : ℝ) (9953117217/20000000000 : ℝ) (501164456501/1000000000000 : ℝ) (501164456509/1000000000000 : ℝ) (501152174709/1000000000000 : ℝ) (250576087359/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 3 (501164456501/1000000000000 : ℝ) (501164456509/1000000000000 : ℝ) (501152174709/1000000000000 : ℝ) (250576087359/500000000000 : ℝ) (100231663121/200000000000 : ℝ) (250579157807/500000000000 : ℝ) (501158315567/1000000000000 : ℝ) (62644789447/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 4 (100231663121/200000000000 : ℝ) (250579157807/500000000000 : ℝ) (501158315567/1000000000000 : ℝ) (62644789447/125000000000 : ℝ) (250579157793/500000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 5 (250579157793/500000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 6 (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66813/524288 : ℝ))) 7 (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66813/524288 : ℝ)) hmem 8 (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66813/524288 : ℝ))) hcmem 8 (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66813/524288 : ℝ)) (992082637597/1000000000000 : ℝ) (1240103297/1250000000 : ℝ) (100231663117/200000000000 : ℝ) (100231663119/200000000000 : ℝ) (793500068873/1000000000000 : ℝ) (198375017223/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0740_exp_lower
  have heNumeric : (1027450908389/500000000000 : ℝ)/4 ≤ Real.exp (-21314121345169/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450908389/500000000000 : ℝ)/4 ≤ Real.exp ((16703/131072 : ℝ)-(198375017223/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16703/131072 : ℝ) (66813/524288 : ℝ) (198375017223/250000000000 : ℝ) (1027450908389/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0741; no trusted numerical premise.
theorem cover8_leaf0741_exp_radius : (998010768780155373/1000000000000000000 : ℝ) ≤ Real.exp ((-33407/2097152 : ℝ)/8) ∧ Real.exp ((-33407/2097152 : ℝ)/8) ≤ (499005384390077687/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33407/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0741_exp_lower : (92011346336970293/100000000000000000 : ℝ) ≤ Real.exp ((-17051297135383/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051297135383/25600000000000 : ℝ)/8) ≤ (920113463369702931/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051297135383/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0741_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450906011/500000000000 : ℝ) ≤ 4*Real.exp (66813/524288 : ℝ)*Real.exp (-mu (radius 8 (33407/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450906011/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33407/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0741_exp_radius
  have hrNumeric : (246049126919/250000000000 : ℝ) ≤ Real.exp (-33407/2097152 : ℝ) ∧ Real.exp (-33407/2097152 : ℝ) ≤ (984196507677/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246049126919/250000000000 : ℝ) ≤ (radius 8 (33407/262144 : ℝ)) ∧ (radius 8 (33407/262144 : ℝ)) ≤ (984196507677/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33407/262144 : ℝ)) (246049126919/250000000000 : ℝ) (984196507677/1000000000000 : ℝ) (177079739881/1000000000000 : ℝ) (177079739887/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33407/262144 : ℝ)) (246049126919/250000000000 : ℝ) (984196507677/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246049126919/250000000000 : ℝ) (984196507677/1000000000000 : ℝ) (496049126919/500000000000 : ℝ) (992098253839/1000000000000 : ℝ) (496033392947/500000000000 : ℝ) (124008348237/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 1 (496049126919/500000000000 : ℝ) (992098253839/1000000000000 : ℝ) (496033392947/500000000000 : ℝ) (124008348237/125000000000 : ℝ) (496041259933/500000000000 : ℝ) (248020629967/250000000000 : ℝ) (992082519741/1000000000000 : ℝ) (992082519743/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 2 (496041259933/500000000000 : ℝ) (248020629967/250000000000 : ℝ) (992082519741/1000000000000 : ℝ) (992082519743/1000000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 3 (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 4 (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 5 (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 6 (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33407/262144 : ℝ)) 7 (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33407/262144 : ℝ))) (177079739881/1000000000000 : ℝ) (177079739887/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177079739881/1000000000000 : ℝ) (177079739887/1000000000000 : ℝ) (29426993497/50000000000 : ℝ) (73567483743/125000000000 : ℝ) (84161687217/200000000000 : ℝ) (420808436093/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 1 (29426993497/50000000000 : ℝ) (73567483743/125000000000 : ℝ) (84161687217/200000000000 : ℝ) (420808436093/1000000000000 : ℝ) (126168538253/250000000000 : ℝ) (504674153019/1000000000000 : ℝ) (497657052841/1000000000000 : ℝ) (497657052849/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 2 (126168538253/250000000000 : ℝ) (504674153019/1000000000000 : ℝ) (497657052841/1000000000000 : ℝ) (497657052849/1000000000000 : ℝ) (250582801463/500000000000 : ℝ) (250582801467/500000000000 : ℝ) (250576660741/500000000000 : ℝ) (501153321491/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 3 (250582801463/500000000000 : ℝ) (250582801467/500000000000 : ℝ) (250576660741/500000000000 : ℝ) (501153321491/1000000000000 : ℝ) (125289865551/250000000000 : ℝ) (501159462213/1000000000000 : ℝ) (250579731083/500000000000 : ℝ) (20046378487/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 4 (125289865551/250000000000 : ℝ) (501159462213/1000000000000 : ℝ) (250579731083/500000000000 : ℝ) (20046378487/40000000000 : ℝ) (100231892437/200000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 5 (100231892437/200000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 6 (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33407/262144 : ℝ))) 7 (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33407/262144 : ℝ)) hmem 8 (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33407/262144 : ℝ))) hcmem 8 (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33407/262144 : ℝ)) (992082519803/1000000000000 : ℝ) (496041259903/500000000000 : ℝ) (62644932773/125000000000 : ℝ) (250579731097/500000000000 : ℝ) (99187747317/125000000000 : ℝ) (158700395711/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0741_exp_lower
  have heNumeric : (1027450906011/500000000000 : ℝ)/4 ≤ Real.exp (-17051297135383/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450906011/500000000000 : ℝ)/4 ≤ Real.exp ((66813/524288 : ℝ)-(158700395711/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66813/524288 : ℝ) (33407/262144 : ℝ) (158700395711/200000000000 : ℝ) (1027450906011/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0742; no trusted numerical premise.
theorem cover8_leaf0742_exp_radius : (998010739037117139/1000000000000000000 : ℝ) ≤ Real.exp ((-66815/4194304 : ℝ)/8) ∧ Real.exp ((-66815/4194304 : ℝ)/8) ≤ (49900536951855857/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66815/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0742_exp_lower : (460056731553311631/500000000000000000 : ℝ) ≤ Real.exp ((-42628242984849/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628242984849/64000000000000 : ℝ)/8) ≤ (920113463106623263/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628242984849/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0742_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450903661/500000000000 : ℝ) ≤ 4*Real.exp (33407/262144 : ℝ)*Real.exp (-mu (radius 8 (66815/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450903661/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66815/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0742_exp_radius
  have hrNumeric : (492098136513/500000000000 : ℝ) ≤ Real.exp (-66815/4194304 : ℝ) ∧ Real.exp (-66815/4194304 : ℝ) ≤ (984196273027/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492098136513/500000000000 : ℝ) ≤ (radius 8 (66815/524288 : ℝ)) ∧ (radius 8 (66815/524288 : ℝ)) ≤ (984196273027/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66815/524288 : ℝ)) (492098136513/500000000000 : ℝ) (984196273027/1000000000000 : ℝ) (44270261011/250000000000 : ℝ) (3541620881/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66815/524288 : ℝ)) (492098136513/500000000000 : ℝ) (984196273027/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492098136513/500000000000 : ℝ) (984196273027/1000000000000 : ℝ) (992098136513/1000000000000 : ℝ) (496049068257/500000000000 : ℝ) (992066667631/1000000000000 : ℝ) (992066667633/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 1 (992098136513/1000000000000 : ℝ) (496049068257/500000000000 : ℝ) (992066667631/1000000000000 : ℝ) (992066667633/1000000000000 : ℝ) (124010300259/125000000000 : ℝ) (496041201037/500000000000 : ℝ) (992082401947/1000000000000 : ℝ) (992082401949/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 2 (124010300259/125000000000 : ℝ) (496041201037/500000000000 : ℝ) (992082401947/1000000000000 : ℝ) (992082401949/1000000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 3 (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 4 (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 5 (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 6 (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66815/524288 : ℝ)) 7 (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66815/524288 : ℝ))) (44270261011/250000000000 : ℝ) (3541620881/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44270261011/250000000000 : ℝ) (3541620881/20000000000 : ℝ) (294270261011/500000000000 : ℝ) (23541620881/40000000000 : ℝ) (16832399427/40000000000 : ℝ) (420809985683/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 1 (294270261011/500000000000 : ℝ) (23541620881/40000000000 : ℝ) (16832399427/40000000000 : ℝ) (420809985683/1000000000000 : ℝ) (63084406731/125000000000 : ℝ) (252337626927/500000000000 : ℝ) (497658244823/1000000000000 : ℝ) (49765824483/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 2 (63084406731/125000000000 : ℝ) (252337626927/500000000000 : ℝ) (497658244823/1000000000000 : ℝ) (49765824483/100000000000 : ℝ) (100233349867/200000000000 : ℝ) (250583374671/500000000000 : ℝ) (250577234119/500000000000 : ℝ) (250577234123/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 3 (100233349867/200000000000 : ℝ) (250583374671/500000000000 : ℝ) (250577234119/500000000000 : ℝ) (250577234123/500000000000 : ℝ) (250580304393/500000000000 : ℝ) (250580304397/500000000000 : ℝ) (125290152187/250000000000 : ℝ) (501160608757/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 4 (250580304393/500000000000 : ℝ) (250580304397/500000000000 : ℝ) (125290152187/250000000000 : ℝ) (501160608757/1000000000000 : ℝ) (501160608767/1000000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 5 (501160608767/1000000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 6 (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66815/524288 : ℝ))) 7 (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66815/524288 : ℝ)) hmem 8 (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66815/524288 : ℝ))) hcmem 8 (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66815/524288 : ℝ)) (992082402009/1000000000000 : ℝ) (248020600503/250000000000 : ℝ) (250580304383/500000000000 : ℝ) (62645076097/125000000000 : ℝ) (198375972043/250000000000 : ℝ) (793503888191/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0742_exp_lower
  have heNumeric : (1027450903661/500000000000 : ℝ)/4 ≤ Real.exp (-42628242984849/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450903661/500000000000 : ℝ)/4 ≤ Real.exp ((33407/262144 : ℝ)-(793503888191/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33407/262144 : ℝ) (66815/524288 : ℝ) (793503888191/1000000000000 : ℝ) (1027450903661/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0743; no trusted numerical premise.
theorem cover8_leaf0743_exp_radius : (998010709294079791/1000000000000000000 : ℝ) ≤ Real.exp ((-261/16384 : ℝ)/8) ∧ Real.exp ((-261/16384 : ℝ)/8) ≤ (62375669330879987/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-261/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0743_exp_lower : (920113462844578721/1000000000000000000 : ℝ) ≤ Real.exp ((-85256486261329/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256486261329/128000000000000 : ℝ)/8) ≤ (460056731422289361/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256486261329/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0743_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686272533/12500000000 : ℝ) ≤ 4*Real.exp (66815/524288 : ℝ)*Real.exp (-mu (radius 8 (261/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (25686272533/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (261/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0743_exp_radius
  have hrNumeric : (7873568307/8000000000 : ℝ) ≤ Real.exp (-261/16384 : ℝ) ∧ Real.exp (-261/16384 : ℝ) ≤ (123024504797/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7873568307/8000000000 : ℝ) ≤ (radius 8 (261/2048 : ℝ)) ∧ (radius 8 (261/2048 : ℝ)) ≤ (123024504797/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (261/2048 : ℝ)) (7873568307/8000000000 : ℝ) (123024504797/125000000000 : ℝ) (88541174101/500000000000 : ℝ) (177082348209/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (261/2048 : ℝ)) (7873568307/8000000000 : ℝ) (123024504797/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (261/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7873568307/8000000000 : ℝ) (123024504797/125000000000 : ℝ) (992098019187/1000000000000 : ℝ) (248024504797/250000000000 : ℝ) (124008318671/125000000000 : ℝ) (992066549369/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (261/2048 : ℝ)) 1 (992098019187/1000000000000 : ℝ) (248024504797/250000000000 : ℝ) (124008318671/125000000000 : ℝ) (992066549369/1000000000000 : ℝ) (992082284277/1000000000000 : ℝ) (992082284279/1000000000000 : ℝ) (124010285519/125000000000 : ℝ) (496041142077/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (261/2048 : ℝ)) 2 (992082284277/1000000000000 : ℝ) (992082284279/1000000000000 : ℝ) (124010285519/125000000000 : ℝ) (496041142077/500000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (261/2048 : ℝ)) 3 (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (261/2048 : ℝ)) 4 (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (261/2048 : ℝ)) 5 (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (261/2048 : ℝ)) 6 (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (261/2048 : ℝ)) 7 (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (261/2048 : ℝ))) (88541174101/500000000000 : ℝ) (177082348209/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88541174101/500000000000 : ℝ) (177082348209/1000000000000 : ℝ) (588541174101/1000000000000 : ℝ) (117708234821/200000000000 : ℝ) (420811535253/1000000000000 : ℝ) (210405767631/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 1 (588541174101/1000000000000 : ℝ) (117708234821/200000000000 : ℝ) (420811535253/1000000000000 : ℝ) (210405767631/500000000000 : ℝ) (504676354677/1000000000000 : ℝ) (126169088671/250000000000 : ℝ) (124414859199/250000000000 : ℝ) (124414859201/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 2 (504676354677/1000000000000 : ℝ) (126169088671/250000000000 : ℝ) (124414859199/250000000000 : ℝ) (124414859201/250000000000 : ℝ) (62645986967/125000000000 : ℝ) (7830748371/15625000000 : ℝ) (250577807493/500000000000 : ℝ) (100231122999/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 3 (62645986967/125000000000 : ℝ) (7830748371/15625000000 : ℝ) (250577807493/500000000000 : ℝ) (100231122999/200000000000 : ℝ) (501161755361/1000000000000 : ℝ) (50116175537/100000000000 : ℝ) (501161755323/1000000000000 : ℝ) (125290438833/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 4 (501161755361/1000000000000 : ℝ) (50116175537/100000000000 : ℝ) (501161755323/1000000000000 : ℝ) (125290438833/250000000000 : ℝ) (250580877671/500000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 5 (250580877671/500000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 6 (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (261/2048 : ℝ))) 7 (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (261/2048 : ℝ)) hmem 8 (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (261/2048 : ℝ))) hcmem 8 (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (261/2048 : ℝ)) (496041142107/500000000000 : ℝ) (992082284217/1000000000000 : ℝ) (501161755341/1000000000000 : ℝ) (501161755351/1000000000000 : ℝ) (396752898899/500000000000 : ℝ) (396752898909/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0743_exp_lower
  have heNumeric : (25686272533/12500000000 : ℝ)/4 ≤ Real.exp (-85256486261329/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686272533/12500000000 : ℝ)/4 ≤ Real.exp ((66815/524288 : ℝ)-(396752898909/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66815/524288 : ℝ) (261/2048 : ℝ) (396752898909/500000000000 : ℝ) (25686272533/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0744; no trusted numerical premise.
theorem cover8_leaf0744_exp_radius : (998010679551043329/1000000000000000000 : ℝ) ≤ Real.exp ((-66817/4194304 : ℝ)/8) ∧ Real.exp ((-66817/4194304 : ℝ)/8) ≤ (99801067955104333/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66817/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0744_exp_lower : (920113462585984607/1000000000000000000 : ℝ) ≤ Real.exp ((-133213260233/200000000000 : ℝ)/8) ∧ Real.exp ((-133213260233/200000000000 : ℝ)/8) ≤ (28753545705812019/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133213260233/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0744_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745089901/50000000000 : ℝ) ≤ 4*Real.exp (261/2048 : ℝ)*Real.exp (-mu (radius 8 (66817/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745089901/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66817/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0744_exp_radius
  have hrNumeric : (39367832149/40000000000 : ℝ) ≤ Real.exp (-66817/4194304 : ℝ) ∧ Real.exp (-66817/4194304 : ℝ) ≤ (492097901863/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39367832149/40000000000 : ℝ) ≤ (radius 8 (66817/524288 : ℝ)) ∧ (radius 8 (66817/524288 : ℝ)) ≤ (492097901863/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66817/524288 : ℝ)) (39367832149/40000000000 : ℝ) (492097901863/500000000000 : ℝ) (35416730469/200000000000 : ℝ) (691733017/3906250000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66817/524288 : ℝ)) (39367832149/40000000000 : ℝ) (492097901863/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39367832149/40000000000 : ℝ) (492097901863/500000000000 : ℝ) (496048950931/500000000000 : ℝ) (992097901863/1000000000000 : ℝ) (7750518993/7812500000 : ℝ) (496033215553/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 1 (496048950931/500000000000 : ℝ) (992097901863/1000000000000 : ℝ) (7750518993/7812500000 : ℝ) (496033215553/500000000000 : ℝ) (992082166483/1000000000000 : ℝ) (198416433297/200000000000 : ℝ) (496041083179/500000000000 : ℝ) (24802054159/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 2 (992082166483/1000000000000 : ℝ) (198416433297/200000000000 : ℝ) (496041083179/500000000000 : ℝ) (24802054159/25000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 3 (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 4 (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 5 (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 6 (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66817/524288 : ℝ)) 7 (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66817/524288 : ℝ))) (35416730469/200000000000 : ℝ) (691733017/3906250000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35416730469/200000000000 : ℝ) (691733017/3906250000 : ℝ) (147135456543/250000000000 : ℝ) (4597983017/7812500000 : ℝ) (420813084807/1000000000000 : ℝ) (26300817801/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 1 (147135456543/250000000000 : ℝ) (4597983017/7812500000 : ℝ) (420813084807/1000000000000 : ℝ) (26300817801/62500000000 : ℝ) (504677455489/1000000000000 : ℝ) (63084681937/125000000000 : ℝ) (497660628751/1000000000000 : ℝ) (497660628759/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 2 (504677455489/1000000000000 : ℝ) (63084681937/125000000000 : ℝ) (497660628751/1000000000000 : ℝ) (497660628759/1000000000000 : ℝ) (12529226053/25000000000 : ℝ) (31323065133/62500000000 : ℝ) (501156761717/1000000000000 : ℝ) (20046270469/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 3 (12529226053/25000000000 : ℝ) (31323065133/62500000000 : ℝ) (501156761717/1000000000000 : ℝ) (20046270469/40000000000 : ℝ) (250581450959/500000000000 : ℝ) (501162901927/1000000000000 : ℝ) (12529072547/25000000000 : ℝ) (501162901889/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 4 (250581450959/500000000000 : ℝ) (501162901927/1000000000000 : ℝ) (12529072547/25000000000 : ℝ) (501162901889/1000000000000 : ℝ) (501162901899/1000000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 5 (501162901899/1000000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 6 (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66817/524288 : ℝ))) 7 (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66817/524288 : ℝ)) hmem 8 (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66817/524288 : ℝ))) hcmem 8 (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66817/524288 : ℝ)) (49604108321/50000000000 : ℝ) (992082166423/1000000000000 : ℝ) (250581450949/500000000000 : ℝ) (125290725477/250000000000 : ℝ) (198376926849/250000000000 : ℝ) (158701541483/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0744_exp_lower
  have heNumeric : (102745089901/50000000000 : ℝ)/4 ≤ Real.exp (-133213260233/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745089901/50000000000 : ℝ)/4 ≤ Real.exp ((261/2048 : ℝ)-(158701541483/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (261/2048 : ℝ) (66817/524288 : ℝ) (158701541483/200000000000 : ℝ) (102745089901/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0745; no trusted numerical premise.
theorem cover8_leaf0745_exp_radius : (499005324904003877/500000000000000000 : ℝ) ≤ Real.exp ((-33409/2097152 : ℝ)/8) ∧ Real.exp ((-33409/2097152 : ℝ)/8) ≤ (199602129961601551/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33409/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0745_exp_lower : (184022692465662121/200000000000000000 : ℝ) ≤ Real.exp ((-85256486835887/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256486835887/128000000000000 : ℝ)/8) ≤ (460056731164155303/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256486835887/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0745_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862724177/125000000000 : ℝ) ≤ 4*Real.exp (66817/524288 : ℝ)*Real.exp (-mu (radius 8 (33409/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862724177/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33409/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0745_exp_radius
  have hrNumeric : (492097784537/500000000000 : ℝ) ≤ Real.exp (-33409/2097152 : ℝ) ∧ Real.exp (-33409/2097152 : ℝ) ≤ (39367822763/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492097784537/500000000000 : ℝ) ≤ (radius 8 (33409/262144 : ℝ)) ∧ (radius 8 (33409/262144 : ℝ)) ≤ (39367822763/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33409/262144 : ℝ)) (492097784537/500000000000 : ℝ) (39367822763/40000000000 : ℝ) (44271239121/250000000000 : ℝ) (177084956491/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33409/262144 : ℝ)) (492097784537/500000000000 : ℝ) (39367822763/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492097784537/500000000000 : ℝ) (39367822763/40000000000 : ℝ) (992097784537/1000000000000 : ℝ) (496048892269/500000000000 : ℝ) (992066312841/1000000000000 : ℝ) (496033156421/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 1 (992097784537/1000000000000 : ℝ) (496048892269/500000000000 : ℝ) (992066312841/1000000000000 : ℝ) (496033156421/500000000000 : ℝ) (992082048689/1000000000000 : ℝ) (99208204869/100000000000 : ℝ) (248020512141/250000000000 : ℝ) (496041024283/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 2 (992082048689/1000000000000 : ℝ) (99208204869/100000000000 : ℝ) (248020512141/250000000000 : ℝ) (496041024283/500000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 3 (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 4 (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 5 (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 6 (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33409/262144 : ℝ)) 7 (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33409/262144 : ℝ))) (44271239121/250000000000 : ℝ) (177084956491/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44271239121/250000000000 : ℝ) (177084956491/1000000000000 : ℝ) (294271239121/500000000000 : ℝ) (294271239123/500000000000 : ℝ) (420814634351/1000000000000 : ℝ) (10520365859/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 1 (294271239121/500000000000 : ℝ) (294271239123/500000000000 : ℝ) (420814634351/1000000000000 : ℝ) (10520365859/25000000000 : ℝ) (63084819537/125000000000 : ℝ) (504678556303/1000000000000 : ℝ) (248830910349/500000000000 : ℝ) (497661820707/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 2 (63084819537/125000000000 : ℝ) (504678556303/1000000000000 : ℝ) (248830910349/500000000000 : ℝ) (497661820707/1000000000000 : ℝ) (501170188497/1000000000000 : ℝ) (100234037701/200000000000 : ℝ) (501157908441/1000000000000 : ℝ) (10023158169/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 3 (501170188497/1000000000000 : ℝ) (100234037701/200000000000 : ℝ) (501157908441/1000000000000 : ℝ) (10023158169/20000000000 : ℝ) (501164048469/1000000000000 : ℝ) (250582024239/500000000000 : ℝ) (501164048431/1000000000000 : ℝ) (12529101211/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 4 (501164048469/1000000000000 : ℝ) (250582024239/500000000000 : ℝ) (501164048431/1000000000000 : ℝ) (12529101211/25000000000 : ℝ) (10023280969/20000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 5 (10023280969/20000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 6 (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33409/262144 : ℝ))) 7 (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33409/262144 : ℝ)) hmem 8 (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33409/262144 : ℝ))) hcmem 8 (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33409/262144 : ℝ)) (496041024313/500000000000 : ℝ) (248020512157/250000000000 : ℝ) (501164048449/1000000000000 : ℝ) (501164048459/1000000000000 : ℝ) (158701923397/200000000000 : ℝ) (198377404251/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0745_exp_lower
  have heNumeric : (256862724177/125000000000 : ℝ)/4 ≤ Real.exp (-85256486835887/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862724177/125000000000 : ℝ)/4 ≤ Real.exp ((66817/524288 : ℝ)-(198377404251/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66817/524288 : ℝ) (33409/262144 : ℝ) (198377404251/250000000000 : ℝ) (256862724177/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0746; no trusted numerical premise.
theorem cover8_leaf0746_exp_radius : (199602124012994613/200000000000000000 : ℝ) ≤ Real.exp ((-66819/4194304 : ℝ)/8) ∧ Real.exp ((-66819/4194304 : ℝ)/8) ≤ (499005310032486533/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66819/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0746_exp_lower : (920113462073857001/1000000000000000000 : ℝ) ≤ Real.exp ((-8525648711907/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525648711907/12800000000000 : ℝ)/8) ≤ (460056731036928501/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525648711907/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0746_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490178887/100000000000 : ℝ) ≤ 4*Real.exp (33409/262144 : ℝ)*Real.exp (-mu (radius 8 (66819/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490178887/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66819/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0746_exp_radius
  have hrNumeric : (123024416803/125000000000 : ℝ) ≤ Real.exp (-66819/4194304 : ℝ) ∧ Real.exp (-66819/4194304 : ℝ) ≤ (39367813377/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123024416803/125000000000 : ℝ) ≤ (radius 8 (66819/524288 : ℝ)) ∧ (radius 8 (66819/524288 : ℝ)) ≤ (39367813377/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66819/524288 : ℝ)) (123024416803/125000000000 : ℝ) (39367813377/40000000000 : ℝ) (177086260607/1000000000000 : ℝ) (88543130307/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66819/524288 : ℝ)) (123024416803/125000000000 : ℝ) (39367813377/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123024416803/125000000000 : ℝ) (39367813377/40000000000 : ℝ) (248024416803/250000000000 : ℝ) (992097667213/1000000000000 : ℝ) (992066194577/1000000000000 : ℝ) (992066194579/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 1 (248024416803/250000000000 : ℝ) (992097667213/1000000000000 : ℝ) (992066194577/1000000000000 : ℝ) (992066194579/1000000000000 : ℝ) (496040965447/500000000000 : ℝ) (62005120681/62500000000 : ℝ) (992081930769/1000000000000 : ℝ) (248020482693/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 2 (496040965447/500000000000 : ℝ) (62005120681/62500000000 : ℝ) (992081930769/1000000000000 : ℝ) (248020482693/250000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 3 (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 4 (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 5 (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 6 (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66819/524288 : ℝ)) 7 (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66819/524288 : ℝ))) (177086260607/1000000000000 : ℝ) (88543130307/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177086260607/1000000000000 : ℝ) (88543130307/500000000000 : ℝ) (588543130303/1000000000000 : ℝ) (588543130307/1000000000000 : ℝ) (42081618387/100000000000 : ℝ) (420816183879/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 1 (588543130303/1000000000000 : ℝ) (588543130307/1000000000000 : ℝ) (42081618387/100000000000 : ℝ) (420816183879/1000000000000 : ℝ) (252339828543/500000000000 : ℝ) (504679657093/1000000000000 : ℝ) (497663012627/1000000000000 : ℝ) (99532602527/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 2 (252339828543/500000000000 : ℝ) (504679657093/1000000000000 : ℝ) (497663012627/1000000000000 : ℝ) (99532602527/200000000000 : ℝ) (62646416857/125000000000 : ℝ) (31323208429/62500000000 : ℝ) (125289763787/250000000000 : ℝ) (125289763789/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 3 (62646416857/125000000000 : ℝ) (31323208429/62500000000 : ℝ) (125289763787/250000000000 : ℝ) (125289763789/250000000000 : ℝ) (250582597501/500000000000 : ℝ) (50116519501/100000000000 : ℝ) (125291298741/250000000000 : ℝ) (501165194973/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 4 (250582597501/500000000000 : ℝ) (50116519501/100000000000 : ℝ) (125291298741/250000000000 : ℝ) (501165194973/1000000000000 : ℝ) (501165194983/1000000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 5 (501165194983/1000000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 6 (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66819/524288 : ℝ))) 7 (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66819/524288 : ℝ)) hmem 8 (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66819/524288 : ℝ))) hcmem 8 (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66819/524288 : ℝ)) (992081930831/1000000000000 : ℝ) (496040965417/500000000000 : ℝ) (250582597491/500000000000 : ℝ) (31322824687/62500000000 : ℝ) (396755763273/500000000000 : ℝ) (158702305313/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0746_exp_lower
  have heNumeric : (205490178887/100000000000 : ℝ)/4 ≤ Real.exp (-8525648711907/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490178887/100000000000 : ℝ)/4 ≤ Real.exp ((33409/262144 : ℝ)-(158702305313/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33409/262144 : ℝ) (66819/524288 : ℝ) (158702305313/200000000000 : ℝ) (205490178887/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0747; no trusted numerical premise.
theorem cover8_leaf0747_exp_radius : (998010590321939263/1000000000000000000 : ℝ) ≤ Real.exp ((-16705/1048576 : ℝ)/8) ∧ Real.exp ((-16705/1048576 : ℝ)/8) ≤ (15593915473780301/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16705/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0747_exp_lower : (920113461820553539/1000000000000000000 : ℝ) ≤ Real.exp ((-85256487400973/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256487400973/128000000000000 : ℝ)/8) ≤ (46005673091027677/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256487400973/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0747_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862723043/125000000000 : ℝ) ≤ 4*Real.exp (66819/524288 : ℝ)*Real.exp (-mu (radius 8 (16705/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862723043/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16705/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0747_exp_radius
  have hrNumeric : (984195099773/1000000000000 : ℝ) ≤ Real.exp (-16705/1048576 : ℝ) ∧ Real.exp (-16705/1048576 : ℝ) ≤ (492097549887/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984195099773/1000000000000 : ℝ) ≤ (radius 8 (16705/131072 : ℝ)) ∧ (radius 8 (16705/131072 : ℝ)) ≤ (492097549887/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16705/131072 : ℝ)) (984195099773/1000000000000 : ℝ) (492097549887/500000000000 : ℝ) (88543782363/500000000000 : ℝ) (177087564733/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16705/131072 : ℝ)) (984195099773/1000000000000 : ℝ) (492097549887/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984195099773/1000000000000 : ℝ) (492097549887/500000000000 : ℝ) (496048774943/500000000000 : ℝ) (992097549887/1000000000000 : ℝ) (992066076313/1000000000000 : ℝ) (198413215263/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 1 (496048774943/500000000000 : ℝ) (992097549887/1000000000000 : ℝ) (992066076313/1000000000000 : ℝ) (198413215263/200000000000 : ℝ) (992081813099/1000000000000 : ℝ) (992081813101/1000000000000 : ℝ) (496040906487/500000000000 : ℝ) (992081812977/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 2 (992081813099/1000000000000 : ℝ) (992081813101/1000000000000 : ℝ) (496040906487/500000000000 : ℝ) (992081812977/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 3 (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 4 (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 5 (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 6 (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16705/131072 : ℝ)) 7 (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16705/131072 : ℝ))) (88543782363/500000000000 : ℝ) (177087564733/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88543782363/500000000000 : ℝ) (177087564733/1000000000000 : ℝ) (588543782363/1000000000000 : ℝ) (588543782367/1000000000000 : ℝ) (210408866689/500000000000 : ℝ) (105204433347/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 1 (588543782363/1000000000000 : ℝ) (588543782367/1000000000000 : ℝ) (210408866689/500000000000 : ℝ) (105204433347/250000000000 : ℝ) (50468075787/100000000000 : ℝ) (252340378939/500000000000 : ℝ) (497664204547/1000000000000 : ℝ) (99532840911/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 2 (50468075787/100000000000 : ℝ) (252340378939/500000000000 : ℝ) (497664204547/1000000000000 : ℝ) (99532840911/200000000000 : ℝ) (62646560151/125000000000 : ℝ) (501172481217/1000000000000 : ℝ) (501160201847/1000000000000 : ℝ) (3915314077/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 3 (62646560151/125000000000 : ℝ) (501172481217/1000000000000 : ℝ) (501160201847/1000000000000 : ℝ) (3915314077/7812500000 : ℝ) (501166341527/1000000000000 : ℝ) (501166341537/1000000000000 : ℝ) (501166341489/1000000000000 : ℝ) (501166341499/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 4 (501166341527/1000000000000 : ℝ) (501166341537/1000000000000 : ℝ) (501166341489/1000000000000 : ℝ) (501166341499/1000000000000 : ℝ) (125291585377/250000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 5 (125291585377/250000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 6 (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16705/131072 : ℝ))) 7 (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16705/131072 : ℝ)) hmem 8 (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16705/131072 : ℝ))) hcmem 8 (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16705/131072 : ℝ)) (248020453259/250000000000 : ℝ) (992081813039/1000000000000 : ℝ) (501166341507/1000000000000 : ℝ) (250583170759/500000000000 : ℝ) (158702687219/200000000000 : ℝ) (198378359029/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0747_exp_lower
  have heNumeric : (256862723043/125000000000 : ℝ)/4 ≤ Real.exp (-85256487400973/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862723043/125000000000 : ℝ)/4 ≤ Real.exp ((66819/524288 : ℝ)-(198378359029/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66819/524288 : ℝ) (16705/131072 : ℝ) (198378359029/250000000000 : ℝ) (256862723043/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0748; no trusted numerical premise.
theorem cover8_leaf0748_exp_radius : (998010560578906347/1000000000000000000 : ℝ) ≤ Real.exp ((-66821/4194304 : ℝ)/8) ∧ Real.exp ((-66821/4194304 : ℝ)/8) ≤ (249502640144726587/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66821/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0748_exp_lower : (57507091348161593/62500000000000000 : ℝ) ≤ Real.exp ((-21314121919791/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314121919791/32000000000000 : ℝ)/8) ≤ (920113461570585489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314121919791/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0748_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450889939/500000000000 : ℝ) ≤ 4*Real.exp (16705/131072 : ℝ)*Real.exp (-mu (radius 8 (66821/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450889939/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66821/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0748_exp_radius
  have hrNumeric : (984194865123/1000000000000 : ℝ) ≤ Real.exp (-66821/4194304 : ℝ) ∧ Real.exp (-66821/4194304 : ℝ) ≤ (246048716281/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984194865123/1000000000000 : ℝ) ≤ (radius 8 (66821/524288 : ℝ)) ∧ (radius 8 (66821/524288 : ℝ)) ≤ (246048716281/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66821/524288 : ℝ)) (984194865123/1000000000000 : ℝ) (246048716281/250000000000 : ℝ) (17708886883/100000000000 : ℝ) (44272217209/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66821/524288 : ℝ)) (984194865123/1000000000000 : ℝ) (246048716281/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984194865123/1000000000000 : ℝ) (246048716281/250000000000 : ℝ) (992097432561/1000000000000 : ℝ) (496048716281/500000000000 : ℝ) (19841319161/20000000000 : ℝ) (248016489513/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 1 (992097432561/1000000000000 : ℝ) (496048716281/500000000000 : ℝ) (19841319161/20000000000 : ℝ) (248016489513/250000000000 : ℝ) (198416339061/200000000000 : ℝ) (992081695307/1000000000000 : ℝ) (49604084759/50000000000 : ℝ) (992081695183/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 2 (198416339061/200000000000 : ℝ) (992081695307/1000000000000 : ℝ) (49604084759/50000000000 : ℝ) (992081695183/1000000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 3 (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 4 (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 5 (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 6 (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66821/524288 : ℝ)) 7 (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66821/524288 : ℝ))) (17708886883/100000000000 : ℝ) (44272217209/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17708886883/100000000000 : ℝ) (44272217209/250000000000 : ℝ) (117708886883/200000000000 : ℝ) (294272217209/500000000000 : ℝ) (420819282863/1000000000000 : ℝ) (420819282871/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 1 (117708886883/200000000000 : ℝ) (294272217209/500000000000 : ℝ) (420819282863/1000000000000 : ℝ) (420819282871/1000000000000 : ℝ) (504681858639/1000000000000 : ℝ) (100936371729/200000000000 : ℝ) (497665396449/1000000000000 : ℝ) (62208174557/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 2 (504681858639/1000000000000 : ℝ) (100936371729/200000000000 : ℝ) (497665396449/1000000000000 : ℝ) (62208174557/125000000000 : ℝ) (62646703443/125000000000 : ℝ) (501173627551/1000000000000 : ℝ) (501161348529/1000000000000 : ℝ) (501161348537/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 3 (62646703443/125000000000 : ℝ) (501173627551/1000000000000 : ℝ) (501161348529/1000000000000 : ℝ) (501161348537/1000000000000 : ℝ) (125291872009/250000000000 : ℝ) (125291872011/250000000000 : ℝ) (250583743999/500000000000 : ℝ) (501167488007/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 4 (125291872009/250000000000 : ℝ) (125291872011/250000000000 : ℝ) (250583743999/500000000000 : ℝ) (501167488007/1000000000000 : ℝ) (501167488017/1000000000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 5 (501167488017/1000000000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 6 (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66821/524288 : ℝ))) 7 (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66821/524288 : ℝ)) hmem 8 (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66821/524288 : ℝ))) hcmem 8 (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66821/524288 : ℝ)) (496040847621/500000000000 : ℝ) (198416339049/200000000000 : ℝ) (31322968001/62500000000 : ℝ) (250583744013/500000000000 : ℝ) (396757672809/500000000000 : ℝ) (396757672819/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0748_exp_lower
  have heNumeric : (1027450889939/500000000000 : ℝ)/4 ≤ Real.exp (-21314121919791/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450889939/500000000000 : ℝ)/4 ≤ Real.exp ((16705/131072 : ℝ)-(396757672819/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16705/131072 : ℝ) (66821/524288 : ℝ) (396757672819/500000000000 : ℝ) (1027450889939/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0749; no trusted numerical premise.
theorem cover8_leaf0749_exp_radius : (499005265417937159/500000000000000000 : ℝ) ≤ Real.exp ((-33411/2097152 : ℝ)/8) ∧ Real.exp ((-33411/2097152 : ℝ)/8) ≤ (998010530835874319/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33411/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0749_exp_lower : (920113461321882593/1000000000000000000 : ℝ) ≤ Real.exp ((-85256487955947/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256487955947/128000000000000 : ℝ)/8) ≤ (460056730660941297/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256487955947/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0749_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980355087/200000000000 : ℝ) ≤ 4*Real.exp (66821/524288 : ℝ)*Real.exp (-mu (radius 8 (33411/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980355087/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33411/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0749_exp_radius
  have hrNumeric : (123024328809/125000000000 : ℝ) ≤ Real.exp (-33411/2097152 : ℝ) ∧ Real.exp (-33411/2097152 : ℝ) ≤ (984194630473/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123024328809/125000000000 : ℝ) ≤ (radius 8 (33411/262144 : ℝ)) ∧ (radius 8 (33411/262144 : ℝ)) ≤ (984194630473/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33411/262144 : ℝ)) (123024328809/125000000000 : ℝ) (984194630473/1000000000000 : ℝ) (177090172929/1000000000000 : ℝ) (35418034587/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33411/262144 : ℝ)) (123024328809/125000000000 : ℝ) (984194630473/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123024328809/125000000000 : ℝ) (984194630473/1000000000000 : ℝ) (248024328809/250000000000 : ℝ) (992097315237/1000000000000 : ℝ) (496032919893/500000000000 : ℝ) (248016459947/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 1 (248024328809/250000000000 : ℝ) (992097315237/1000000000000 : ℝ) (496032919893/500000000000 : ℝ) (248016459947/250000000000 : ℝ) (992081577511/1000000000000 : ℝ) (992081577513/1000000000000 : ℝ) (496040788693/500000000000 : ℝ) (248020394347/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 2 (992081577511/1000000000000 : ℝ) (992081577513/1000000000000 : ℝ) (496040788693/500000000000 : ℝ) (248020394347/250000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 3 (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 4 (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 5 (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 6 (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33411/262144 : ℝ)) 7 (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33411/262144 : ℝ))) (177090172929/1000000000000 : ℝ) (35418034587/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177090172929/1000000000000 : ℝ) (35418034587/200000000000 : ℝ) (574751061/976562500 : ℝ) (147136271617/250000000000 : ℝ) (420820832337/1000000000000 : ℝ) (84164166469/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 1 (574751061/976562500 : ℝ) (147136271617/250000000000 : ℝ) (420820832337/1000000000000 : ℝ) (84164166469/200000000000 : ℝ) (2523414797/5000000000 : ℝ) (504682959407/1000000000000 : ℝ) (497666588343/1000000000000 : ℝ) (497666588351/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 2 (2523414797/5000000000 : ℝ) (504682959407/1000000000000 : ℝ) (497666588343/1000000000000 : ℝ) (497666588351/1000000000000 : ℝ) (501174773871/1000000000000 : ℝ) (501174773879/1000000000000 : ℝ) (125290623801/250000000000 : ℝ) (125290623803/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 3 (501174773871/1000000000000 : ℝ) (501174773879/1000000000000 : ℝ) (125290623801/250000000000 : ℝ) (125290623803/250000000000 : ℝ) (501168634537/1000000000000 : ℝ) (250584317273/500000000000 : ℝ) (501168634499/1000000000000 : ℝ) (125292158627/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 4 (501168634537/1000000000000 : ℝ) (250584317273/500000000000 : ℝ) (501168634499/1000000000000 : ℝ) (125292158627/250000000000 : ℝ) (250584317259/500000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 5 (250584317259/500000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 6 (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33411/262144 : ℝ))) 7 (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33411/262144 : ℝ)) hmem 8 (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33411/262144 : ℝ))) hcmem 8 (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33411/262144 : ℝ)) (124010197181/125000000000 : ℝ) (992081577451/1000000000000 : ℝ) (501168634517/1000000000000 : ℝ) (501168634527/1000000000000 : ℝ) (79351725513/100000000000 : ℝ) (793517255149/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0749_exp_lower
  have heNumeric : (410980355087/200000000000 : ℝ)/4 ≤ Real.exp (-85256487955947/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980355087/200000000000 : ℝ)/4 ≤ Real.exp ((66821/524288 : ℝ)-(793517255149/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66821/524288 : ℝ) (33411/262144 : ℝ) (793517255149/1000000000000 : ℝ) (410980355087/200000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0725_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0725_certificate
#check SmaleRate.Proofs.cover8_leaf0726_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0726_certificate
#check SmaleRate.Proofs.cover8_leaf0727_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0727_certificate
#check SmaleRate.Proofs.cover8_leaf0728_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0728_certificate
#check SmaleRate.Proofs.cover8_leaf0729_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0729_certificate
#check SmaleRate.Proofs.cover8_leaf0730_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0730_certificate
#check SmaleRate.Proofs.cover8_leaf0731_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0731_certificate
#check SmaleRate.Proofs.cover8_leaf0732_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0732_certificate
#check SmaleRate.Proofs.cover8_leaf0733_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0733_certificate
#check SmaleRate.Proofs.cover8_leaf0734_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0734_certificate
#check SmaleRate.Proofs.cover8_leaf0735_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0735_certificate
#check SmaleRate.Proofs.cover8_leaf0736_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0736_certificate
#check SmaleRate.Proofs.cover8_leaf0737_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0737_certificate
#check SmaleRate.Proofs.cover8_leaf0738_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0738_certificate
#check SmaleRate.Proofs.cover8_leaf0739_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0739_certificate
#check SmaleRate.Proofs.cover8_leaf0740_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0740_certificate
#check SmaleRate.Proofs.cover8_leaf0741_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0741_certificate
#check SmaleRate.Proofs.cover8_leaf0742_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0742_certificate
#check SmaleRate.Proofs.cover8_leaf0743_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0743_certificate
#check SmaleRate.Proofs.cover8_leaf0744_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0744_certificate
#check SmaleRate.Proofs.cover8_leaf0745_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0745_certificate
#check SmaleRate.Proofs.cover8_leaf0746_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0746_certificate
#check SmaleRate.Proofs.cover8_leaf0747_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0747_certificate
#check SmaleRate.Proofs.cover8_leaf0748_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0748_certificate
#check SmaleRate.Proofs.cover8_leaf0749_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0749_certificate
