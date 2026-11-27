/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1075; no trusted numerical premise.
theorem cover8_leaf1075_exp_radius : (499000417327339583/500000000000000000 : ℝ) ≤ Real.exp ((-16787/1048576 : ℝ)/8) ∧ Real.exp ((-16787/1048576 : ℝ)/8) ≤ (998000834654679167/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16787/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1075_exp_lower : (920113498923389231/1000000000000000000 : ℝ) ≤ Real.exp ((-85256446108997/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256446108997/128000000000000 : ℝ)/8) ≤ (57507093682711827/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256446108997/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1075_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451223621/500000000000 : ℝ) ≤ 4*Real.exp (67147/524288 : ℝ)*Real.exp (-mu (radius 8 (16787/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451223621/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16787/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1075_exp_radius
  have hrNumeric : (246029534363/250000000000 : ℝ) ≤ Real.exp (-16787/1048576 : ℝ) ∧ Real.exp (-16787/1048576 : ℝ) ≤ (984118137453/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246029534363/250000000000 : ℝ) ≤ (radius 8 (16787/131072 : ℝ)) ∧ (radius 8 (16787/131072 : ℝ)) ≤ (984118137453/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16787/131072 : ℝ)) (246029534363/250000000000 : ℝ) (984118137453/1000000000000 : ℝ) (44378691069/250000000000 : ℝ) (88757382141/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16787/131072 : ℝ)) (246029534363/250000000000 : ℝ) (984118137453/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246029534363/250000000000 : ℝ) (984118137453/1000000000000 : ℝ) (496029534363/500000000000 : ℝ) (992059068727/1000000000000 : ℝ) (496013643323/500000000000 : ℝ) (124003410831/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 1 (496029534363/500000000000 : ℝ) (992059068727/1000000000000 : ℝ) (496013643323/500000000000 : ℝ) (124003410831/125000000000 : ℝ) (496021588843/500000000000 : ℝ) (124005397211/125000000000 : ℝ) (496021588779/500000000000 : ℝ) (992043177561/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 2 (496021588843/500000000000 : ℝ) (124005397211/125000000000 : ℝ) (496021588779/500000000000 : ℝ) (992043177561/1000000000000 : ℝ) (496021588811/500000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 3 (496021588811/500000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 4 (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 5 (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 6 (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16787/131072 : ℝ)) 7 (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16787/131072 : ℝ))) (44378691069/250000000000 : ℝ) (88757382141/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44378691069/250000000000 : ℝ) (88757382141/500000000000 : ℝ) (294378691069/500000000000 : ℝ) (588757382141/1000000000000 : ℝ) (210662505133/500000000000 : ℝ) (210662505137/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 1 (294378691069/500000000000 : ℝ) (588757382141/1000000000000 : ℝ) (210662505133/500000000000 : ℝ) (210662505137/500000000000 : ℝ) (252520598101/500000000000 : ℝ) (31565074763/62500000000 : ℝ) (49805442481/100000000000 : ℝ) (498054424817/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 2 (252520598101/500000000000 : ℝ) (31565074763/62500000000 : ℝ) (49805442481/100000000000 : ℝ) (498054424817/1000000000000 : ℝ) (250773905253/500000000000 : ℝ) (501547810513/1000000000000 : ℝ) (125383911069/250000000000 : ℝ) (501535644283/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 3 (250773905253/500000000000 : ℝ) (501547810513/1000000000000 : ℝ) (125383911069/250000000000 : ℝ) (501535644283/1000000000000 : ℝ) (501541727391/1000000000000 : ℝ) (250770863699/500000000000 : ℝ) (250770863677/500000000000 : ℝ) (250770863681/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 4 (501541727391/1000000000000 : ℝ) (250770863699/500000000000 : ℝ) (250770863677/500000000000 : ℝ) (250770863681/500000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 5 (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 6 (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16787/131072 : ℝ))) 7 (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16787/131072 : ℝ)) hmem 8 (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16787/131072 : ℝ))) hcmem 8 (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16787/131072 : ℝ)) (992043177621/1000000000000 : ℝ) (7936345421/8000000000 : ℝ) (125385431843/250000000000 : ℝ) (25077086369/50000000000 : ℝ) (794138723857/1000000000000 : ℝ) (397069361937/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1075_exp_lower
  have heNumeric : (1027451223621/500000000000 : ℝ)/4 ≤ Real.exp (-85256446108997/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451223621/500000000000 : ℝ)/4 ≤ Real.exp ((67147/524288 : ℝ)-(397069361937/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67147/524288 : ℝ) (16787/131072 : ℝ) (397069361937/500000000000 : ℝ) (1027451223621/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1076; no trusted numerical premise.
theorem cover8_leaf1076_exp_radius : (998000804911936991/1000000000000000000 : ℝ) ≤ Real.exp ((-67149/4194304 : ℝ)/8) ∧ Real.exp ((-67149/4194304 : ℝ)/8) ≤ (31187525153498031/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67149/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1076_exp_lower : (460056749700557967/500000000000000000 : ℝ) ≤ Real.exp ((-21314111394333/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314111394333/32000000000000 : ℝ)/8) ≤ (184022699880223187/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314111394333/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1076_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451227889/500000000000 : ℝ) ≤ 4*Real.exp (16787/131072 : ℝ)*Real.exp (-mu (radius 8 (67149/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451227889/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67149/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1076_exp_radius
  have hrNumeric : (49205895141/50000000000 : ℝ) ≤ Real.exp (-67149/4194304 : ℝ) ∧ Real.exp (-67149/4194304 : ℝ) ≤ (984117902821/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49205895141/50000000000 : ℝ) ≤ (radius 8 (67149/524288 : ℝ)) ∧ (radius 8 (67149/524288 : ℝ)) ≤ (984117902821/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67149/524288 : ℝ)) (49205895141/50000000000 : ℝ) (984117902821/1000000000000 : ℝ) (177516065039/1000000000000 : ℝ) (88758032523/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67149/524288 : ℝ)) (49205895141/50000000000 : ℝ) (984117902821/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49205895141/50000000000 : ℝ) (984117902821/1000000000000 : ℝ) (99205895141/100000000000 : ℝ) (992058951411/1000000000000 : ℝ) (248006792097/250000000000 : ℝ) (992027168389/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 1 (99205895141/100000000000 : ℝ) (992058951411/1000000000000 : ℝ) (248006792097/250000000000 : ℝ) (992027168389/1000000000000 : ℝ) (992043059899/1000000000000 : ℝ) (9920430599/10000000000 : ℝ) (992043059771/1000000000000 : ℝ) (992043059773/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 2 (992043059899/1000000000000 : ℝ) (9920430599/10000000000 : ℝ) (992043059771/1000000000000 : ℝ) (992043059773/1000000000000 : ℝ) (198408611967/200000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 3 (198408611967/200000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 4 (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 5 (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 6 (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67149/524288 : ℝ)) 7 (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67149/524288 : ℝ))) (177516065039/1000000000000 : ℝ) (88758032523/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177516065039/1000000000000 : ℝ) (88758032523/500000000000 : ℝ) (588758032519/1000000000000 : ℝ) (588758032523/1000000000000 : ℝ) (421326553921/1000000000000 : ℝ) (42132655393/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 1 (588758032519/1000000000000 : ℝ) (588758032523/1000000000000 : ℝ) (421326553921/1000000000000 : ℝ) (42132655393/100000000000 : ℝ) (25252114661/50000000000 : ℝ) (505042293227/1000000000000 : ℝ) (49805561229/100000000000 : ℝ) (249027806149/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 2 (25252114661/50000000000 : ℝ) (505042293227/1000000000000 : ℝ) (49805561229/100000000000 : ℝ) (249027806149/500000000000 : ℝ) (100309790551/200000000000 : ℝ) (501548952763/1000000000000 : ℝ) (125384196717/250000000000 : ℝ) (125384196719/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 3 (100309790551/200000000000 : ℝ) (501548952763/1000000000000 : ℝ) (125384196717/250000000000 : ℝ) (125384196719/250000000000 : ℝ) (501542869811/1000000000000 : ℝ) (25077143491/50000000000 : ℝ) (250771434887/500000000000 : ℝ) (501542869783/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 4 (501542869811/1000000000000 : ℝ) (25077143491/50000000000 : ℝ) (250771434887/500000000000 : ℝ) (501542869783/1000000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 5 (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 6 (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67149/524288 : ℝ))) 7 (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67149/524288 : ℝ)) hmem 8 (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67149/524288 : ℝ))) hcmem 8 (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67149/524288 : ℝ)) (496021529917/500000000000 : ℝ) (992043059837/1000000000000 : ℝ) (15673214681/31250000000 : ℝ) (250771434901/500000000000 : ℝ) (794140627049/1000000000000 : ℝ) (794140627069/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1076_exp_lower
  have heNumeric : (1027451227889/500000000000 : ℝ)/4 ≤ Real.exp (-21314111394333/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451227889/500000000000 : ℝ)/4 ≤ Real.exp ((16787/131072 : ℝ)-(794140627069/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16787/131072 : ℝ) (67149/524288 : ℝ) (794140627069/1000000000000 : ℝ) (1027451227889/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1077; no trusted numerical premise.
theorem cover8_leaf1077_exp_radius : (124750096896149463/125000000000000000 : ℝ) ≤ Real.exp ((-33575/2097152 : ℝ)/8) ∧ Real.exp ((-33575/2097152 : ℝ)/8) ≤ (199600155033839141/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33575/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1077_exp_lower : (920113499881372949/1000000000000000000 : ℝ) ≤ Real.exp ((-85256445042851/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256445042851/128000000000000 : ℝ)/8) ≤ (18402269997627459/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256445042851/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1077_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451232179/500000000000 : ℝ) ≤ 4*Real.exp (67149/524288 : ℝ)*Real.exp (-mu (radius 8 (33575/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451232179/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33575/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1077_exp_radius
  have hrNumeric : (246029417047/250000000000 : ℝ) ≤ Real.exp (-33575/2097152 : ℝ) ∧ Real.exp (-33575/2097152 : ℝ) ≤ (984117668189/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246029417047/250000000000 : ℝ) ≤ (radius 8 (33575/262144 : ℝ)) ∧ (radius 8 (33575/262144 : ℝ)) ≤ (984117668189/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33575/262144 : ℝ)) (246029417047/250000000000 : ℝ) (984117668189/1000000000000 : ℝ) (177517365793/1000000000000 : ℝ) (177517365799/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33575/262144 : ℝ)) (246029417047/250000000000 : ℝ) (984117668189/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246029417047/250000000000 : ℝ) (984117668189/1000000000000 : ℝ) (496029417047/500000000000 : ℝ) (198411766819/200000000000 : ℝ) (992027050129/1000000000000 : ℝ) (99202705013/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 1 (496029417047/500000000000 : ℝ) (198411766819/200000000000 : ℝ) (992027050129/1000000000000 : ℝ) (99202705013/100000000000 : ℝ) (992042942111/1000000000000 : ℝ) (992042942113/1000000000000 : ℝ) (31001341937/31250000000 : ℝ) (496021470993/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 2 (992042942111/1000000000000 : ℝ) (992042942113/1000000000000 : ℝ) (31001341937/31250000000 : ℝ) (496021470993/500000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 3 (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 4 (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 5 (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 6 (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33575/262144 : ℝ)) 7 (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33575/262144 : ℝ))) (177517365793/1000000000000 : ℝ) (177517365799/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177517365793/1000000000000 : ℝ) (177517365799/1000000000000 : ℝ) (36797417681/62500000000 : ℝ) (5887586829/10000000000 : ℝ) (421328097559/1000000000000 : ℝ) (421328097567/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 1 (36797417681/62500000000 : ℝ) (5887586829/10000000000 : ℝ) (421328097559/1000000000000 : ℝ) (421328097567/1000000000000 : ℝ) (505043390227/1000000000000 : ℝ) (252521695117/500000000000 : ℝ) (249028399879/500000000000 : ℝ) (249028399883/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 2 (505043390227/1000000000000 : ℝ) (252521695117/500000000000 : ℝ) (249028399879/500000000000 : ℝ) (249028399883/500000000000 : ℝ) (31346880937/62500000000 : ℝ) (100310019/200000000 : ℝ) (62692241181/125000000000 : ℝ) (31346120591/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 3 (31346880937/62500000000 : ℝ) (100310019/200000000 : ℝ) (62692241181/125000000000 : ℝ) (31346120591/62500000000 : ℝ) (25077200611/50000000000 : ℝ) (125386003057/250000000000 : ℝ) (501544012183/1000000000000 : ℝ) (15673250381/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 4 (25077200611/50000000000 : ℝ) (125386003057/250000000000 : ℝ) (501544012183/1000000000000 : ℝ) (15673250381/31250000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 5 (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 6 (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33575/262144 : ℝ))) 7 (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33575/262144 : ℝ)) hmem 8 (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33575/262144 : ℝ))) hcmem 8 (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33575/262144 : ℝ)) (992042942047/1000000000000 : ℝ) (19840858841/20000000000 : ℝ) (501544012201/1000000000000 : ℝ) (50154401221/100000000000 : ℝ) (49633908139/62500000000 : ℝ) (397071265121/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1077_exp_lower
  have heNumeric : (1027451232179/500000000000 : ℝ)/4 ≤ Real.exp (-85256445042851/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451232179/500000000000 : ℝ)/4 ≤ Real.exp ((67149/524288 : ℝ)-(397071265121/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67149/524288 : ℝ) (33575/262144 : ℝ) (397071265121/500000000000 : ℝ) (1027451232179/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1078; no trusted numerical premise.
theorem cover8_leaf1078_exp_radius : (499000372713227651/500000000000000000 : ℝ) ≤ Real.exp ((-67151/4194304 : ℝ)/8) ∧ Real.exp ((-67151/4194304 : ℝ)/8) ≤ (998000745426455303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67151/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1078_exp_lower : (920113500363470191/1000000000000000000 : ℝ) ≤ Real.exp ((-42628222253161/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628222253161/64000000000000 : ℝ)/8) ≤ (57507093772716887/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628222253161/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1078_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725618243/250000000000 : ℝ) ≤ 4*Real.exp (33575/262144 : ℝ)*Real.exp (-mu (radius 8 (67151/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725618243/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67151/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1078_exp_radius
  have hrNumeric : (246029358389/250000000000 : ℝ) ≤ Real.exp (-67151/4194304 : ℝ) ∧ Real.exp (-67151/4194304 : ℝ) ≤ (984117433557/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246029358389/250000000000 : ℝ) ≤ (radius 8 (67151/524288 : ℝ)) ∧ (radius 8 (67151/524288 : ℝ)) ≤ (984117433557/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67151/524288 : ℝ)) (246029358389/250000000000 : ℝ) (984117433557/1000000000000 : ℝ) (177518666537/1000000000000 : ℝ) (177518666543/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67151/524288 : ℝ)) (246029358389/250000000000 : ℝ) (984117433557/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246029358389/250000000000 : ℝ) (984117433557/1000000000000 : ℝ) (496029358389/500000000000 : ℝ) (992058716779/1000000000000 : ℝ) (99202693187/100000000000 : ℝ) (992026931871/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 1 (496029358389/500000000000 : ℝ) (992058716779/1000000000000 : ℝ) (99202693187/100000000000 : ℝ) (992026931871/1000000000000 : ℝ) (248010706081/250000000000 : ℝ) (39681712973/40000000000 : ℝ) (248010706049/250000000000 : ℝ) (496021412099/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 2 (248010706081/250000000000 : ℝ) (39681712973/40000000000 : ℝ) (248010706049/250000000000 : ℝ) (496021412099/500000000000 : ℝ) (49602141213/50000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 3 (49602141213/50000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 4 (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 5 (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 6 (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67151/524288 : ℝ)) 7 (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67151/524288 : ℝ))) (177518666537/1000000000000 : ℝ) (177518666543/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177518666537/1000000000000 : ℝ) (177518666543/1000000000000 : ℝ) (147189833317/250000000000 : ℝ) (73594916659/125000000000 : ℝ) (21066482059/50000000000 : ℝ) (105332410297/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 1 (147189833317/250000000000 : ℝ) (73594916659/125000000000 : ℝ) (21066482059/50000000000 : ℝ) (105332410297/250000000000 : ℝ) (63130560903/125000000000 : ℝ) (50504448723/100000000000 : ℝ) (498057987213/1000000000000 : ℝ) (24902899361/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 2 (63130560903/125000000000 : ℝ) (50504448723/100000000000 : ℝ) (498057987213/1000000000000 : ℝ) (24902899361/50000000000 : ℝ) (250775618609/500000000000 : ℝ) (20062049489/40000000000 : ℝ) (501539072017/1000000000000 : ℝ) (62692384003/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 3 (250775618609/500000000000 : ℝ) (20062049489/40000000000 : ℝ) (501539072017/1000000000000 : ℝ) (62692384003/125000000000 : ℝ) (501545154617/1000000000000 : ℝ) (4012361237/8000000000 : ℝ) (25077257729/50000000000 : ℝ) (125386288647/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 4 (501545154617/1000000000000 : ℝ) (4012361237/8000000000 : ℝ) (25077257729/50000000000 : ℝ) (125386288647/250000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 5 (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 6 (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67151/524288 : ℝ))) 7 (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67151/524288 : ℝ)) hmem 8 (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67151/524288 : ℝ))) hcmem 8 (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67151/524288 : ℝ)) (992042824259/1000000000000 : ℝ) (496021412131/500000000000 : ℝ) (250772577299/500000000000 : ℝ) (501545154607/1000000000000 : ℝ) (397072216691/500000000000 : ℝ) (794144433399/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1078_exp_lower
  have heNumeric : (513725618243/250000000000 : ℝ)/4 ≤ Real.exp (-42628222253161/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725618243/250000000000 : ℝ)/4 ≤ Real.exp ((33575/262144 : ℝ)-(794144433399/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33575/262144 : ℝ) (67151/524288 : ℝ) (794144433399/1000000000000 : ℝ) (513725618243/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1079; no trusted numerical premise.
theorem cover8_leaf1079_exp_radius : (998000715683715787/1000000000000000000 : ℝ) ≤ Real.exp ((-4197/262144 : ℝ)/8) ∧ Real.exp ((-4197/262144 : ℝ)/8) ≤ (249500178920928947/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4197/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1079_exp_lower : (920113500847752703/1000000000000000000 : ℝ) ≤ Real.exp ((-85256443967361/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256443967361/128000000000000 : ℝ)/8) ≤ (1797096681343267/1953125000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256443967361/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1079_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862810203/125000000000 : ℝ) ≤ 4*Real.exp (67151/524288 : ℝ)*Real.exp (-mu (radius 8 (4197/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (256862810203/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4197/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1079_exp_radius
  have hrNumeric : (246029299731/250000000000 : ℝ) ≤ Real.exp (-4197/262144 : ℝ) ∧ Real.exp (-4197/262144 : ℝ) ≤ (39364687957/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246029299731/250000000000 : ℝ) ≤ (radius 8 (4197/32768 : ℝ)) ∧ (radius 8 (4197/32768 : ℝ)) ≤ (39364687957/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4197/32768 : ℝ)) (246029299731/250000000000 : ℝ) (39364687957/40000000000 : ℝ) (177519967271/1000000000000 : ℝ) (177519967277/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4197/32768 : ℝ)) (246029299731/250000000000 : ℝ) (39364687957/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246029299731/250000000000 : ℝ) (39364687957/40000000000 : ℝ) (496029299731/500000000000 : ℝ) (992058599463/1000000000000 : ℝ) (992026813611/1000000000000 : ℝ) (248006703403/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 1 (496029299731/500000000000 : ℝ) (992058599463/1000000000000 : ℝ) (992026813611/1000000000000 : ℝ) (248006703403/250000000000 : ℝ) (124005338317/125000000000 : ℝ) (496021353269/500000000000 : ℝ) (992042706409/1000000000000 : ℝ) (992042706411/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 2 (124005338317/125000000000 : ℝ) (496021353269/500000000000 : ℝ) (992042706409/1000000000000 : ℝ) (992042706411/1000000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 3 (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 4 (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 5 (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 6 (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4197/32768 : ℝ)) 7 (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4197/32768 : ℝ))) (177519967271/1000000000000 : ℝ) (177519967277/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177519967271/1000000000000 : ℝ) (177519967277/1000000000000 : ℝ) (117751996727/200000000000 : ℝ) (588759983639/1000000000000 : ℝ) (421331184783/1000000000000 : ℝ) (421331184791/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 1 (117751996727/200000000000 : ℝ) (588759983639/1000000000000 : ℝ) (421331184783/1000000000000 : ℝ) (421331184791/1000000000000 : ℝ) (505045584209/1000000000000 : ℝ) (101009116843/200000000000 : ℝ) (249029587327/500000000000 : ℝ) (249029587331/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 2 (505045584209/1000000000000 : ℝ) (101009116843/200000000000 : ℝ) (249029587327/500000000000 : ℝ) (249029587331/500000000000 : ℝ) (501552379431/1000000000000 : ℝ) (501552379439/1000000000000 : ℝ) (125385053643/250000000000 : ℝ) (25077010729/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 3 (501552379431/1000000000000 : ℝ) (501552379439/1000000000000 : ℝ) (125385053643/250000000000 : ℝ) (25077010729/50000000000 : ℝ) (501546297001/1000000000000 : ℝ) (50154629701/100000000000 : ℝ) (125386574241/250000000000 : ℝ) (501546296973/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 4 (501546297001/1000000000000 : ℝ) (50154629701/100000000000 : ℝ) (125386574241/250000000000 : ℝ) (501546296973/1000000000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 5 (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 6 (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4197/32768 : ℝ))) 7 (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4197/32768 : ℝ)) hmem 8 (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4197/32768 : ℝ))) hcmem 8 (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4197/32768 : ℝ)) (124005338309/125000000000 : ℝ) (39681708259/40000000000 : ℝ) (250773148491/500000000000 : ℝ) (15673321781/31250000000 : ℝ) (397073168259/500000000000 : ℝ) (794146336537/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1079_exp_lower
  have heNumeric : (256862810203/125000000000 : ℝ)/4 ≤ Real.exp (-85256443967361/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862810203/125000000000 : ℝ)/4 ≤ Real.exp ((67151/524288 : ℝ)-(794146336537/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67151/524288 : ℝ) (4197/32768 : ℝ) (794146336537/1000000000000 : ℝ) (256862810203/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1080; no trusted numerical premise.
theorem cover8_leaf1080_exp_radius : (499000342970488579/500000000000000000 : ℝ) ≤ Real.exp ((-67153/4194304 : ℝ)/8) ∧ Real.exp ((-67153/4194304 : ℝ)/8) ≤ (998000685940977159/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67153/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1080_exp_lower : (184022700267005117/200000000000000000 : ℝ) ≤ Real.exp ((-5328527714067/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328527714067/8000000000000 : ℝ)/8) ≤ (460056750667512793/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328527714067/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1080_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490249033/100000000000 : ℝ) ≤ 4*Real.exp (4197/32768 : ℝ)*Real.exp (-mu (radius 8 (67153/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490249033/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67153/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1080_exp_radius
  have hrNumeric : (984116964293/1000000000000 : ℝ) ≤ Real.exp (-67153/4194304 : ℝ) ∧ Real.exp (-67153/4194304 : ℝ) ≤ (492058482147/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984116964293/1000000000000 : ℝ) ≤ (radius 8 (67153/524288 : ℝ)) ∧ (radius 8 (67153/524288 : ℝ)) ≤ (492058482147/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67153/524288 : ℝ)) (984116964293/1000000000000 : ℝ) (492058482147/500000000000 : ℝ) (177521267989/1000000000000 : ℝ) (44380316999/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67153/524288 : ℝ)) (984116964293/1000000000000 : ℝ) (492058482147/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984116964293/1000000000000 : ℝ) (492058482147/500000000000 : ℝ) (496029241073/500000000000 : ℝ) (992058482147/1000000000000 : ℝ) (992026695353/1000000000000 : ℝ) (496013347677/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 1 (496029241073/500000000000 : ℝ) (992058482147/1000000000000 : ℝ) (992026695353/1000000000000 : ℝ) (496013347677/500000000000 : ℝ) (992042588749/1000000000000 : ℝ) (992042588751/1000000000000 : ℝ) (496021294311/500000000000 : ℝ) (62002661789/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 2 (992042588749/1000000000000 : ℝ) (992042588751/1000000000000 : ℝ) (496021294311/500000000000 : ℝ) (62002661789/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 3 (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 4 (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 5 (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 6 (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67153/524288 : ℝ)) 7 (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67153/524288 : ℝ))) (177521267989/1000000000000 : ℝ) (44380316999/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177521267989/1000000000000 : ℝ) (44380316999/250000000000 : ℝ) (294380316997/500000000000 : ℝ) (294380316999/500000000000 : ℝ) (210666364181/500000000000 : ℝ) (421332728371/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 1 (294380316997/500000000000 : ℝ) (294380316999/500000000000 : ℝ) (210666364181/500000000000 : ℝ) (421332728371/1000000000000 : ℝ) (252523340589/500000000000 : ℝ) (101009336237/200000000000 : ℝ) (498060362077/1000000000000 : ℝ) (99612072417/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 2 (252523340589/500000000000 : ℝ) (101009336237/200000000000 : ℝ) (498060362077/1000000000000 : ℝ) (99612072417/200000000000 : ℝ) (501553521627/1000000000000 : ℝ) (100310704327/200000000000 : ℝ) (501541357111/1000000000000 : ℝ) (1567316741/3125000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 3 (501553521627/1000000000000 : ℝ) (100310704327/200000000000 : ℝ) (501541357111/1000000000000 : ℝ) (1567316741/3125000000 : ℝ) (501547439369/1000000000000 : ℝ) (250773719689/500000000000 : ℝ) (125386859833/250000000000 : ℝ) (501547439341/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 4 (501547439369/1000000000000 : ℝ) (250773719689/500000000000 : ℝ) (125386859833/250000000000 : ℝ) (501547439341/1000000000000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 5 (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 6 (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67153/524288 : ℝ))) 7 (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67153/524288 : ℝ)) hmem 8 (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67153/524288 : ℝ))) hcmem 8 (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67153/524288 : ℝ)) (198408517737/200000000000 : ℝ) (62002661793/62500000000 : ℝ) (10030948787/20000000000 : ℝ) (391833937/781250000 : ℝ) (794148239629/1000000000000 : ℝ) (794148239649/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1080_exp_lower
  have heNumeric : (205490249033/100000000000 : ℝ)/4 ≤ Real.exp (-5328527714067/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490249033/100000000000 : ℝ)/4 ≤ Real.exp ((4197/32768 : ℝ)-(794148239649/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4197/32768 : ℝ) (67153/524288 : ℝ) (794148239649/1000000000000 : ℝ) (205490249033/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1081; no trusted numerical premise.
theorem cover8_leaf1081_exp_radius : (124750082024779927/125000000000000000 : ℝ) ≤ Real.exp ((-33577/2097152 : ℝ)/8) ∧ Real.exp ((-33577/2097152 : ℝ)/8) ≤ (998000656198239417/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33577/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1081_exp_lower : (230028375455919659/250000000000000000 : ℝ) ≤ Real.exp ((-85256442881247/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256442881247/128000000000000 : ℝ)/8) ≤ (920113501823678637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256442881247/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1081_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745124953/50000000000 : ℝ) ≤ 4*Real.exp (67153/524288 : ℝ)*Real.exp (-mu (radius 8 (33577/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (102745124953/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33577/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1081_exp_radius
  have hrNumeric : (984116729661/1000000000000 : ℝ) ≤ Real.exp (-33577/2097152 : ℝ) ∧ Real.exp (-33577/2097152 : ℝ) ≤ (492058364831/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984116729661/1000000000000 : ℝ) ≤ (radius 8 (33577/262144 : ℝ)) ∧ (radius 8 (33577/262144 : ℝ)) ≤ (492058364831/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33577/262144 : ℝ)) (984116729661/1000000000000 : ℝ) (492058364831/500000000000 : ℝ) (346723767/1953125000 : ℝ) (17752256871/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33577/262144 : ℝ)) (984116729661/1000000000000 : ℝ) (492058364831/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984116729661/1000000000000 : ℝ) (492058364831/500000000000 : ℝ) (99205836483/100000000000 : ℝ) (992058364831/1000000000000 : ℝ) (496013288547/500000000000 : ℝ) (198405315419/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 1 (99205836483/100000000000 : ℝ) (992058364831/1000000000000 : ℝ) (496013288547/500000000000 : ℝ) (198405315419/200000000000 : ℝ) (496021235481/500000000000 : ℝ) (992042470963/1000000000000 : ℝ) (496021235417/500000000000 : ℝ) (248010617709/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 2 (496021235481/500000000000 : ℝ) (992042470963/1000000000000 : ℝ) (496021235417/500000000000 : ℝ) (248010617709/250000000000 : ℝ) (496021235449/500000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 3 (496021235449/500000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 4 (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 5 (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 6 (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33577/262144 : ℝ)) 7 (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33577/262144 : ℝ))) (346723767/1953125000 : ℝ) (17752256871/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (346723767/1953125000 : ℝ) (17752256871/100000000000 : ℝ) (2299848767/3906250000 : ℝ) (117752256871/200000000000 : ℝ) (421334271931/1000000000000 : ℝ) (421334271939/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 1 (2299848767/3906250000 : ℝ) (117752256871/200000000000 : ℝ) (421334271931/1000000000000 : ℝ) (421334271939/1000000000000 : ℝ) (505047778141/1000000000000 : ℝ) (505047778147/1000000000000 : ℝ) (498061549493/1000000000000 : ℝ) (996123099/2000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 2 (505047778141/1000000000000 : ℝ) (505047778147/1000000000000 : ℝ) (498061549493/1000000000000 : ℝ) (996123099/2000000000 : ℝ) (501554663817/1000000000000 : ℝ) (31347166489/62500000000 : ℝ) (501542499643/1000000000000 : ℝ) (501542499651/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 3 (501554663817/1000000000000 : ℝ) (31347166489/62500000000 : ℝ) (501542499643/1000000000000 : ℝ) (501542499651/1000000000000 : ℝ) (50154858173/100000000000 : ℝ) (250774290869/500000000000 : ℝ) (501548581693/1000000000000 : ℝ) (501548581701/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 4 (50154858173/100000000000 : ℝ) (250774290869/500000000000 : ℝ) (501548581693/1000000000000 : ℝ) (501548581701/1000000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 5 (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 6 (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33577/262144 : ℝ))) 7 (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33577/262144 : ℝ)) hmem 8 (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33577/262144 : ℝ))) hcmem 8 (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33577/262144 : ℝ)) (992042470897/1000000000000 : ℝ) (9920424709/10000000000 : ℝ) (501548581711/1000000000000 : ℝ) (12538714543/25000000000 : ℝ) (794150142731/1000000000000 : ℝ) (794150142749/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1081_exp_lower
  have heNumeric : (102745124953/50000000000 : ℝ)/4 ≤ Real.exp (-85256442881247/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745124953/50000000000 : ℝ)/4 ≤ Real.exp ((67153/524288 : ℝ)-(794150142749/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67153/524288 : ℝ) (33577/262144 : ℝ) (794150142749/1000000000000 : ℝ) (102745124953/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1082; no trusted numerical premise.
theorem cover8_leaf1082_exp_radius : (6237503915346891/6250000000000000 : ℝ) ≤ Real.exp ((-67155/4194304 : ℝ)/8) ∧ Real.exp ((-67155/4194304 : ℝ)/8) ≤ (998000626455502561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67155/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1082_exp_lower : (230028375578657993/250000000000000000 : ℝ) ≤ Real.exp ((-42628221167431/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628221167431/64000000000000 : ℝ)/8) ≤ (920113502314631973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628221167431/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1082_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862813479/125000000000 : ℝ) ≤ 4*Real.exp (33577/262144 : ℝ)*Real.exp (-mu (radius 8 (67155/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862813479/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67155/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1082_exp_radius
  have hrNumeric : (984116495029/1000000000000 : ℝ) ≤ Real.exp (-67155/4194304 : ℝ) ∧ Real.exp (-67155/4194304 : ℝ) ≤ (98411649503/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984116495029/1000000000000 : ℝ) ≤ (radius 8 (67155/524288 : ℝ)) ∧ (radius 8 (67155/524288 : ℝ)) ≤ (98411649503/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67155/524288 : ℝ)) (984116495029/1000000000000 : ℝ) (98411649503/100000000000 : ℝ) (5547620919/31250000000 : ℝ) (35504773883/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67155/524288 : ℝ)) (984116495029/1000000000000 : ℝ) (98411649503/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984116495029/1000000000000 : ℝ) (98411649503/100000000000 : ℝ) (496029123757/500000000000 : ℝ) (198411649503/200000000000 : ℝ) (198405291767/200000000000 : ℝ) (248006614709/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 1 (496029123757/500000000000 : ℝ) (198411649503/200000000000 : ℝ) (198405291767/200000000000 : ℝ) (248006614709/250000000000 : ℝ) (496021176587/500000000000 : ℝ) (124005294147/125000000000 : ℝ) (992042353047/1000000000000 : ℝ) (992042353049/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 2 (496021176587/500000000000 : ℝ) (124005294147/125000000000 : ℝ) (992042353047/1000000000000 : ℝ) (992042353049/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 3 (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 4 (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 5 (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 6 (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67155/524288 : ℝ)) 7 (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67155/524288 : ℝ))) (5547620919/31250000000 : ℝ) (35504773883/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5547620919/31250000000 : ℝ) (35504773883/200000000000 : ℝ) (36797620919/62500000000 : ℝ) (147190483677/250000000000 : ℝ) (210667907741/500000000000 : ℝ) (421335815491/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 1 (36797620919/62500000000 : ℝ) (147190483677/250000000000 : ℝ) (210667907741/500000000000 : ℝ) (421335815491/1000000000000 : ℝ) (505048875093/1000000000000 : ℝ) (5050488751/10000000000 : ℝ) (249031368447/500000000000 : ℝ) (249031368451/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 2 (505048875093/1000000000000 : ℝ) (5050488751/10000000000 : ℝ) (249031368447/500000000000 : ℝ) (249031368451/500000000000 : ℝ) (501555805993/1000000000000 : ℝ) (501555806001/1000000000000 : ℝ) (250771821081/500000000000 : ℝ) (501543642171/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 3 (501555805993/1000000000000 : ℝ) (501555806001/1000000000000 : ℝ) (250771821081/500000000000 : ℝ) (501543642171/1000000000000 : ℝ) (501549724077/1000000000000 : ℝ) (250774862043/500000000000 : ℝ) (12538743101/25000000000 : ℝ) (10030994481/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 4 (501549724077/1000000000000 : ℝ) (250774862043/500000000000 : ℝ) (12538743101/25000000000 : ℝ) (10030994481/20000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 5 (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 6 (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67155/524288 : ℝ))) 7 (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67155/524288 : ℝ)) hmem 8 (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67155/524288 : ℝ))) hcmem 8 (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67155/524288 : ℝ)) (99204235311/100000000000 : ℝ) (992042353113/1000000000000 : ℝ) (250774862029/500000000000 : ℝ) (125387431017/250000000000 : ℝ) (79415204581/100000000000 : ℝ) (794152045829/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1082_exp_lower
  have heNumeric : (256862813479/125000000000 : ℝ)/4 ≤ Real.exp (-42628221167431/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862813479/125000000000 : ℝ)/4 ≤ Real.exp ((33577/262144 : ℝ)-(794152045829/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33577/262144 : ℝ) (67155/524288 : ℝ) (794152045829/1000000000000 : ℝ) (256862813479/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1083; no trusted numerical premise.
theorem cover8_leaf1083_exp_radius : (99800059671276659/100000000000000000 : ℝ) ≤ Real.exp ((-16789/1048576 : ℝ)/8) ∧ Real.exp ((-16789/1048576 : ℝ)/8) ≤ (998000596712766591/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16789/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1083_exp_lower : (920113502808575677/1000000000000000000 : ℝ) ≤ Real.exp ((-85256441785149/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256441785149/128000000000000 : ℝ)/8) ≤ (460056751404287839/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256441785149/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1083_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902516657/1000000000000 : ℝ) ≤ 4*Real.exp (67155/524288 : ℝ)*Real.exp (-mu (radius 8 (16789/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902516657/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16789/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1083_exp_radius
  have hrNumeric : (492058130199/500000000000 : ℝ) ≤ Real.exp (-16789/1048576 : ℝ) ∧ Real.exp (-16789/1048576 : ℝ) ≤ (984116260399/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492058130199/500000000000 : ℝ) ≤ (radius 8 (16789/131072 : ℝ)) ∧ (radius 8 (16789/131072 : ℝ)) ≤ (984116260399/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16789/131072 : ℝ)) (492058130199/500000000000 : ℝ) (984116260399/1000000000000 : ℝ) (177525170097/1000000000000 : ℝ) (22190646263/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16789/131072 : ℝ)) (492058130199/500000000000 : ℝ) (984116260399/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492058130199/500000000000 : ℝ) (984116260399/1000000000000 : ℝ) (992058130199/1000000000000 : ℝ) (4960290651/5000000000 : ℝ) (31000823143/31250000000 : ℝ) (496013170289/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 1 (992058130199/1000000000000 : ℝ) (4960290651/5000000000 : ℝ) (31000823143/31250000000 : ℝ) (496013170289/500000000000 : ℝ) (992042235387/1000000000000 : ℝ) (992042235389/1000000000000 : ℝ) (49602111763/50000000000 : ℝ) (496021117631/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 2 (992042235387/1000000000000 : ℝ) (992042235389/1000000000000 : ℝ) (49602111763/50000000000 : ℝ) (496021117631/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 3 (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 4 (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 5 (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 6 (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16789/131072 : ℝ)) 7 (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16789/131072 : ℝ))) (177525170097/1000000000000 : ℝ) (22190646263/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177525170097/1000000000000 : ℝ) (22190646263/125000000000 : ℝ) (73595323131/125000000000 : ℝ) (147190646263/250000000000 : ℝ) (421337359009/1000000000000 : ℝ) (210668679509/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 1 (73595323131/125000000000 : ℝ) (147190646263/250000000000 : ℝ) (421337359009/1000000000000 : ℝ) (210668679509/500000000000 : ℝ) (126262493007/250000000000 : ℝ) (101009994407/200000000000 : ℝ) (249031962139/500000000000 : ℝ) (249031962143/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 2 (126262493007/250000000000 : ℝ) (101009994407/200000000000 : ℝ) (249031962139/500000000000 : ℝ) (249031962143/500000000000 : ℝ) (501556948153/1000000000000 : ℝ) (501556948161/1000000000000 : ℝ) (100308956933/200000000000 : ℝ) (501544784673/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 3 (501556948153/1000000000000 : ℝ) (501556948161/1000000000000 : ℝ) (100308956933/200000000000 : ℝ) (501544784673/1000000000000 : ℝ) (501550866409/1000000000000 : ℝ) (501550866417/1000000000000 : ℝ) (125387716593/250000000000 : ℝ) (501550866381/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 4 (501550866409/1000000000000 : ℝ) (501550866417/1000000000000 : ℝ) (125387716593/250000000000 : ℝ) (501550866381/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 5 (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 6 (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16789/131072 : ℝ))) 7 (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16789/131072 : ℝ)) hmem 8 (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16789/131072 : ℝ))) hcmem 8 (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16789/131072 : ℝ)) (992042235323/1000000000000 : ℝ) (496021117663/500000000000 : ℝ) (50155086639/100000000000 : ℝ) (501550866399/1000000000000 : ℝ) (397076974433/500000000000 : ℝ) (794153948883/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1083_exp_lower
  have heNumeric : (2054902516657/1000000000000 : ℝ)/4 ≤ Real.exp (-85256441785149/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902516657/1000000000000 : ℝ)/4 ≤ Real.exp ((67155/524288 : ℝ)-(794153948883/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67155/524288 : ℝ) (16789/131072 : ℝ) (794153948883/1000000000000 : ℝ) (2054902516657/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1084; no trusted numerical premise.
theorem cover8_leaf1084_exp_radius : (998000566970031507/1000000000000000000 : ℝ) ≤ Real.exp ((-67157/4194304 : ℝ)/8) ∧ Real.exp ((-67157/4194304 : ℝ)/8) ≤ (249500141742507877/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67157/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1084_exp_lower : (115014187912929937/125000000000000000 : ℝ) ≤ Real.exp ((-21314110308603/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314110308603/32000000000000 : ℝ)/8) ≤ (920113503303439497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314110308603/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1084_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902525499/1000000000000 : ℝ) ≤ 4*Real.exp (16789/131072 : ℝ)*Real.exp (-mu (radius 8 (67157/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902525499/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67157/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1084_exp_radius
  have hrNumeric : (492058012883/500000000000 : ℝ) ≤ Real.exp (-67157/4194304 : ℝ) ∧ Real.exp (-67157/4194304 : ℝ) ≤ (984116025767/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492058012883/500000000000 : ℝ) ≤ (radius 8 (67157/524288 : ℝ)) ∧ (radius 8 (67157/524288 : ℝ)) ≤ (984116025767/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67157/524288 : ℝ)) (492058012883/500000000000 : ℝ) (984116025767/1000000000000 : ℝ) (88763235391/500000000000 : ℝ) (177526470789/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67157/524288 : ℝ)) (492058012883/500000000000 : ℝ) (984116025767/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492058012883/500000000000 : ℝ) (984116025767/1000000000000 : ℝ) (992058012883/1000000000000 : ℝ) (248014503221/250000000000 : ℝ) (992026222317/1000000000000 : ℝ) (992026222319/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 1 (992058012883/1000000000000 : ℝ) (248014503221/250000000000 : ℝ) (992026222317/1000000000000 : ℝ) (992026222319/1000000000000 : ℝ) (1240052647/1250000000 : ℝ) (496021058801/500000000000 : ℝ) (31001316171/31250000000 : ℝ) (39681684699/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 2 (1240052647/1250000000 : ℝ) (496021058801/500000000000 : ℝ) (31001316171/31250000000 : ℝ) (39681684699/40000000000 : ℝ) (31001316173/31250000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 3 (31001316173/31250000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 4 (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 5 (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 6 (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67157/524288 : ℝ)) 7 (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67157/524288 : ℝ))) (88763235391/500000000000 : ℝ) (177526470789/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88763235391/500000000000 : ℝ) (177526470789/1000000000000 : ℝ) (588763235391/1000000000000 : ℝ) (117752647079/200000000000 : ℝ) (210669451263/500000000000 : ℝ) (84267780507/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 1 (588763235391/1000000000000 : ℝ) (117752647079/200000000000 : ℝ) (210669451263/500000000000 : ℝ) (84267780507/200000000000 : ℝ) (252525534479/500000000000 : ℝ) (101010213793/200000000000 : ℝ) (249032555827/500000000000 : ℝ) (249032555831/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 2 (252525534479/500000000000 : ℝ) (101010213793/200000000000 : ℝ) (249032555827/500000000000 : ℝ) (249032555831/500000000000 : ℝ) (250779045153/500000000000 : ℝ) (250779045157/500000000000 : ℝ) (12538648179/25000000000 : ℝ) (501545927169/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 3 (250779045153/500000000000 : ℝ) (250779045157/500000000000 : ℝ) (12538648179/25000000000 : ℝ) (501545927169/1000000000000 : ℝ) (501552008733/1000000000000 : ℝ) (250776004371/500000000000 : ℝ) (62694001087/125000000000 : ℝ) (100310401741/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 4 (501552008733/1000000000000 : ℝ) (250776004371/500000000000 : ℝ) (62694001087/125000000000 : ℝ) (100310401741/200000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 5 (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 6 (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67157/524288 : ℝ))) 7 (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67157/524288 : ℝ)) hmem 8 (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67157/524288 : ℝ))) hcmem 8 (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67157/524288 : ℝ)) (198408423507/200000000000 : ℝ) (992042117539/1000000000000 : ℝ) (250776004357/500000000000 : ℝ) (125388002181/250000000000 : ℝ) (794155851909/1000000000000 : ℝ) (794155851929/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1084_exp_lower
  have heNumeric : (2054902525499/1000000000000 : ℝ)/4 ≤ Real.exp (-21314110308603/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902525499/1000000000000 : ℝ)/4 ≤ Real.exp ((16789/131072 : ℝ)-(794155851929/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16789/131072 : ℝ) (67157/524288 : ℝ) (794155851929/1000000000000 : ℝ) (2054902525499/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1085; no trusted numerical premise.
theorem cover8_leaf1085_exp_radius : (99800053722729731/100000000000000000 : ℝ) ≤ Real.exp ((-33579/2097152 : ℝ)/8) ∧ Real.exp ((-33579/2097152 : ℝ)/8) ≤ (998000537227297311/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33579/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1085_exp_lower : (920113503800833627/1000000000000000000 : ℝ) ≤ Real.exp ((-85256440680859/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256440680859/128000000000000 : ℝ)/8) ≤ (230028375950208407/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256440680859/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1085_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980506877/200000000000 : ℝ) ≤ 4*Real.exp (67157/524288 : ℝ)*Real.exp (-mu (radius 8 (33579/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980506877/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33579/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1085_exp_radius
  have hrNumeric : (492057895567/500000000000 : ℝ) ≤ Real.exp (-33579/2097152 : ℝ) ∧ Real.exp (-33579/2097152 : ℝ) ≤ (196823158227/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492057895567/500000000000 : ℝ) ≤ (radius 8 (33579/262144 : ℝ)) ∧ (radius 8 (33579/262144 : ℝ)) ≤ (196823158227/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33579/262144 : ℝ)) (492057895567/500000000000 : ℝ) (196823158227/200000000000 : ℝ) (177527771457/1000000000000 : ℝ) (22190971433/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33579/262144 : ℝ)) (492057895567/500000000000 : ℝ) (196823158227/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492057895567/500000000000 : ℝ) (196823158227/200000000000 : ℝ) (992057895567/1000000000000 : ℝ) (62003618473/62500000000 : ℝ) (496013052029/500000000000 : ℝ) (49601305203/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 1 (992057895567/1000000000000 : ℝ) (62003618473/62500000000 : ℝ) (496013052029/500000000000 : ℝ) (49601305203/50000000000 : ℝ) (248010499953/250000000000 : ℝ) (496020999907/500000000000 : ℝ) (198408399937/200000000000 : ℝ) (992041999687/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 2 (248010499953/250000000000 : ℝ) (496020999907/500000000000 : ℝ) (198408399937/200000000000 : ℝ) (992041999687/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 3 (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 4 (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 5 (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 6 (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33579/262144 : ℝ)) 7 (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33579/262144 : ℝ))) (177527771457/1000000000000 : ℝ) (22190971433/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177527771457/1000000000000 : ℝ) (22190971433/125000000000 : ℝ) (18398871429/31250000000 : ℝ) (147190971433/250000000000 : ℝ) (16853617841/40000000000 : ℝ) (210670223017/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 1 (18398871429/31250000000 : ℝ) (147190971433/250000000000 : ℝ) (16853617841/40000000000 : ℝ) (210670223017/500000000000 : ℝ) (126263041469/250000000000 : ℝ) (505052165883/1000000000000 : ℝ) (62258287377/125000000000 : ℝ) (31129143689/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 2 (126263041469/250000000000 : ℝ) (505052165883/1000000000000 : ℝ) (62258287377/125000000000 : ℝ) (31129143689/62500000000 : ℝ) (250779616223/500000000000 : ℝ) (250779616227/500000000000 : ℝ) (501547069643/1000000000000 : ℝ) (501547069651/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 3 (250779616223/500000000000 : ℝ) (250779616227/500000000000 : ℝ) (501547069643/1000000000000 : ℝ) (501547069651/1000000000000 : ℝ) (125388287761/250000000000 : ℝ) (501553151053/1000000000000 : ℝ) (501553151007/1000000000000 : ℝ) (62694143877/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 4 (125388287761/250000000000 : ℝ) (501553151053/1000000000000 : ℝ) (501553151007/1000000000000 : ℝ) (62694143877/125000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 5 (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 6 (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33579/262144 : ℝ))) 7 (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33579/262144 : ℝ)) hmem 8 (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33579/262144 : ℝ))) hcmem 8 (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33579/262144 : ℝ)) (248010499937/250000000000 : ℝ) (992041999751/1000000000000 : ℝ) (20062126041/40000000000 : ℝ) (100310630207/200000000000 : ℝ) (794157754933/1000000000000 : ℝ) (794157754953/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1085_exp_lower
  have heNumeric : (410980506877/200000000000 : ℝ)/4 ≤ Real.exp (-85256440680859/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980506877/200000000000 : ℝ)/4 ≤ Real.exp ((67157/524288 : ℝ)-(794157754953/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67157/524288 : ℝ) (33579/262144 : ℝ) (794157754953/1000000000000 : ℝ) (410980506877/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1086; no trusted numerical premise.
theorem cover8_leaf1086_exp_radius : (249500126871141/250000000000000 : ℝ) ≤ Real.exp ((-67159/4194304 : ℝ)/8) ∧ Real.exp ((-67159/4194304 : ℝ)/8) ≤ (998000507484564001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67159/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1086_exp_lower : (920113504301218127/1000000000000000000 : ℝ) ≤ Real.exp ((-42628220061989/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628220061989/64000000000000 : ℝ)/8) ≤ (57507094018826133/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628220061989/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1086_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196101733/40000000000 : ℝ) ≤ 4*Real.exp (33579/262144 : ℝ)*Real.exp (-mu (radius 8 (67159/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (82196101733/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67159/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1086_exp_radius
  have hrNumeric : (984115556503/1000000000000 : ℝ) ≤ Real.exp (-67159/4194304 : ℝ) ∧ Real.exp (-67159/4194304 : ℝ) ≤ (123014444563/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984115556503/1000000000000 : ℝ) ≤ (radius 8 (67159/524288 : ℝ)) ∧ (radius 8 (67159/524288 : ℝ)) ≤ (123014444563/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67159/524288 : ℝ)) (984115556503/1000000000000 : ℝ) (123014444563/125000000000 : ℝ) (177529072117/1000000000000 : ℝ) (177529072123/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67159/524288 : ℝ)) (984115556503/1000000000000 : ℝ) (123014444563/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984115556503/1000000000000 : ℝ) (123014444563/125000000000 : ℝ) (992057778251/1000000000000 : ℝ) (248014444563/250000000000 : ℝ) (4960129929/5000000000 : ℝ) (992025985801/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 1 (992057778251/1000000000000 : ℝ) (248014444563/250000000000 : ℝ) (4960129929/5000000000 : ℝ) (992025985801/1000000000000 : ℝ) (39681675281/40000000000 : ℝ) (992041882027/1000000000000 : ℝ) (496020940949/500000000000 : ℝ) (9920418819/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 2 (39681675281/40000000000 : ℝ) (992041882027/1000000000000 : ℝ) (496020940949/500000000000 : ℝ) (9920418819/10000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 3 (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 4 (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 5 (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 6 (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67159/524288 : ℝ)) 7 (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67159/524288 : ℝ))) (177529072117/1000000000000 : ℝ) (177529072123/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177529072117/1000000000000 : ℝ) (177529072123/1000000000000 : ℝ) (294382268029/500000000000 : ℝ) (294382268031/500000000000 : ℝ) (421341989501/1000000000000 : ℝ) (421341989509/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 1 (294382268029/500000000000 : ℝ) (294382268031/500000000000 : ℝ) (421341989501/1000000000000 : ℝ) (421341989509/1000000000000 : ℝ) (505053262779/1000000000000 : ℝ) (252526631393/500000000000 : ℝ) (498067486361/1000000000000 : ℝ) (15564608949/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 2 (505053262779/1000000000000 : ℝ) (252526631393/500000000000 : ℝ) (498067486361/1000000000000 : ℝ) (15564608949/31250000000 : ℝ) (50156037457/100000000000 : ℝ) (501560374577/1000000000000 : ℝ) (50154821211/100000000000 : ℝ) (250774106059/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 3 (50156037457/100000000000 : ℝ) (501560374577/1000000000000 : ℝ) (50154821211/100000000000 : ℝ) (250774106059/500000000000 : ℝ) (25077714667/50000000000 : ℝ) (125388573337/250000000000 : ℝ) (501554293303/1000000000000 : ℝ) (501554293311/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 4 (25077714667/50000000000 : ℝ) (125388573337/250000000000 : ℝ) (501554293303/1000000000000 : ℝ) (501554293311/1000000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 5 (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 6 (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67159/524288 : ℝ))) 7 (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67159/524288 : ℝ)) hmem 8 (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67159/524288 : ℝ))) hcmem 8 (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67159/524288 : ℝ)) (992041881961/1000000000000 : ℝ) (248010470491/250000000000 : ℝ) (501554293321/1000000000000 : ℝ) (50155429333/100000000000 : ℝ) (397079828967/500000000000 : ℝ) (794159657951/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1086_exp_lower
  have heNumeric : (82196101733/40000000000 : ℝ)/4 ≤ Real.exp (-42628220061989/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196101733/40000000000 : ℝ)/4 ≤ Real.exp ((33579/262144 : ℝ)-(794159657951/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33579/262144 : ℝ) (67159/524288 : ℝ) (794159657951/1000000000000 : ℝ) (82196101733/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1087; no trusted numerical premise.
theorem cover8_leaf1087_exp_radius : (124750059717728947/125000000000000000 : ℝ) ≤ Real.exp ((-8395/524288 : ℝ)/8) ∧ Real.exp ((-8395/524288 : ℝ)/8) ≤ (998000477741831577/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8395/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1087_exp_lower : (920113504803787897/1000000000000000000 : ℝ) ≤ Real.exp ((-17051287912933/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051287912933/25600000000000 : ℝ)/8) ≤ (460056752401893949/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051287912933/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1087_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980510461/200000000000 : ℝ) ≤ 4*Real.exp (67159/524288 : ℝ)*Real.exp (-mu (radius 8 (8395/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980510461/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8395/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1087_exp_radius
  have hrNumeric : (61507207617/62500000000 : ℝ) ≤ Real.exp (-8395/524288 : ℝ) ∧ Real.exp (-8395/524288 : ℝ) ≤ (984115321873/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61507207617/62500000000 : ℝ) ≤ (radius 8 (8395/65536 : ℝ)) ∧ (radius 8 (8395/65536 : ℝ)) ≤ (984115321873/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8395/65536 : ℝ)) (61507207617/62500000000 : ℝ) (984115321873/1000000000000 : ℝ) (177530372767/1000000000000 : ℝ) (177530372773/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8395/65536 : ℝ)) (61507207617/62500000000 : ℝ) (984115321873/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61507207617/62500000000 : ℝ) (984115321873/1000000000000 : ℝ) (124007207617/125000000000 : ℝ) (992057660937/1000000000000 : ℝ) (992025867541/1000000000000 : ℝ) (992025867543/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 1 (124007207617/125000000000 : ℝ) (992057660937/1000000000000 : ℝ) (992025867541/1000000000000 : ℝ) (992025867543/1000000000000 : ℝ) (496020882119/500000000000 : ℝ) (12400522053/12500000000 : ℝ) (992041764111/1000000000000 : ℝ) (992041764113/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 2 (496020882119/500000000000 : ℝ) (12400522053/12500000000 : ℝ) (992041764111/1000000000000 : ℝ) (992041764113/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 3 (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 4 (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 5 (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 6 (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8395/65536 : ℝ)) 7 (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8395/65536 : ℝ))) (177530372767/1000000000000 : ℝ) (177530372773/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177530372767/1000000000000 : ℝ) (177530372773/1000000000000 : ℝ) (588765186383/1000000000000 : ℝ) (588765186387/1000000000000 : ℝ) (421343532959/1000000000000 : ℝ) (421343532967/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 1 (588765186383/1000000000000 : ℝ) (588765186387/1000000000000 : ℝ) (421343532959/1000000000000 : ℝ) (421343532967/1000000000000 : ℝ) (505054359671/1000000000000 : ℝ) (505054359677/1000000000000 : ℝ) (124517168423/250000000000 : ℝ) (498068673699/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 2 (505054359671/1000000000000 : ℝ) (505054359677/1000000000000 : ℝ) (124517168423/250000000000 : ℝ) (498068673699/1000000000000 : ℝ) (501561516681/1000000000000 : ℝ) (31347594793/62500000000 : ℝ) (125387338641/250000000000 : ℝ) (501549354571/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 3 (501561516681/1000000000000 : ℝ) (31347594793/62500000000 : ℝ) (125387338641/250000000000 : ℝ) (501549354571/1000000000000 : ℝ) (250777717811/500000000000 : ℝ) (50155543563/100000000000 : ℝ) (100311087117/200000000000 : ℝ) (501555435593/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 4 (250777717811/500000000000 : ℝ) (50155543563/100000000000 : ℝ) (100311087117/200000000000 : ℝ) (501555435593/1000000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 5 (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 6 (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8395/65536 : ℝ))) 7 (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8395/65536 : ℝ)) hmem 8 (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8395/65536 : ℝ))) hcmem 8 (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8395/65536 : ℝ)) (496020882087/500000000000 : ℝ) (992041764177/1000000000000 : ℝ) (501555435603/1000000000000 : ℝ) (125388858903/250000000000 : ℝ) (49635097557/62500000000 : ℝ) (79416156093/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1087_exp_lower
  have heNumeric : (410980510461/200000000000 : ℝ)/4 ≤ Real.exp (-17051287912933/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980510461/200000000000 : ℝ)/4 ≤ Real.exp ((67159/524288 : ℝ)-(79416156093/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67159/524288 : ℝ) (8395/65536 : ℝ) (79416156093/100000000000 : ℝ) (410980510461/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1088; no trusted numerical premise.
theorem cover8_leaf1088_exp_radius : (499000223999550019/500000000000000000 : ℝ) ≤ Real.exp ((-67161/4194304 : ℝ)/8) ∧ Real.exp ((-67161/4194304 : ℝ)/8) ≤ (998000447999100039/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67161/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1088_exp_lower : (184022701061478559/200000000000000000 : ℝ) ≤ Real.exp ((-426282195021/640000000000 : ℝ)/8) ∧ Real.exp ((-426282195021/640000000000 : ℝ)/8) ≤ (230028376326848199/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-426282195021/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1088_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451280651/500000000000 : ℝ) ≤ 4*Real.exp (8395/65536 : ℝ)*Real.exp (-mu (radius 8 (67161/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451280651/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67161/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1088_exp_radius
  have hrNumeric : (24602877181/25000000000 : ℝ) ≤ Real.exp (-67161/4194304 : ℝ) ∧ Real.exp (-67161/4194304 : ℝ) ≤ (984115087241/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24602877181/25000000000 : ℝ) ≤ (radius 8 (67161/524288 : ℝ)) ∧ (radius 8 (67161/524288 : ℝ)) ≤ (984115087241/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67161/524288 : ℝ)) (24602877181/25000000000 : ℝ) (984115087241/1000000000000 : ℝ) (44382918353/250000000000 : ℝ) (177531673419/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67161/524288 : ℝ)) (24602877181/25000000000 : ℝ) (984115087241/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24602877181/25000000000 : ℝ) (984115087241/1000000000000 : ℝ) (49602877181/50000000000 : ℝ) (992057543621/1000000000000 : ℝ) (496012874641/500000000000 : ℝ) (248006437321/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 1 (49602877181/50000000000 : ℝ) (992057543621/1000000000000 : ℝ) (496012874641/500000000000 : ℝ) (248006437321/250000000000 : ℝ) (992041646451/1000000000000 : ℝ) (992041646453/1000000000000 : ℝ) (992041646323/1000000000000 : ℝ) (496020823163/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 2 (992041646451/1000000000000 : ℝ) (992041646453/1000000000000 : ℝ) (992041646323/1000000000000 : ℝ) (496020823163/500000000000 : ℝ) (992041646387/1000000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 3 (992041646387/1000000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 4 (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 5 (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 6 (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67161/524288 : ℝ)) 7 (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67161/524288 : ℝ))) (44382918353/250000000000 : ℝ) (177531673419/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44382918353/250000000000 : ℝ) (177531673419/1000000000000 : ℝ) (294382918353/500000000000 : ℝ) (58876583671/100000000000 : ℝ) (210672538203/500000000000 : ℝ) (84269015283/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 1 (294382918353/500000000000 : ℝ) (58876583671/100000000000 : ℝ) (210672538203/500000000000 : ℝ) (84269015283/200000000000 : ℝ) (126263864139/250000000000 : ℝ) (505055456563/1000000000000 : ℝ) (99613972203/200000000000 : ℝ) (498069861023/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 2 (126263864139/250000000000 : ℝ) (505055456563/1000000000000 : ℝ) (99613972203/200000000000 : ℝ) (498069861023/1000000000000 : ℝ) (100312531757/200000000000 : ℝ) (501562658793/1000000000000 : ℝ) (50155049701/100000000000 : ℝ) (501550497019/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 3 (100312531757/200000000000 : ℝ) (501562658793/1000000000000 : ℝ) (50155049701/100000000000 : ℝ) (501550497019/1000000000000 : ℝ) (501556577897/1000000000000 : ℝ) (250778288953/500000000000 : ℝ) (25077828893/50000000000 : ℝ) (50155657787/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 4 (501556577897/1000000000000 : ℝ) (250778288953/500000000000 : ℝ) (25077828893/50000000000 : ℝ) (50155657787/100000000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 5 (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 6 (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67161/524288 : ℝ))) 7 (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67161/524288 : ℝ)) hmem 8 (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67161/524288 : ℝ))) hcmem 8 (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67161/524288 : ℝ)) (496020823193/500000000000 : ℝ) (99204164639/100000000000 : ℝ) (250778288939/500000000000 : ℝ) (15673643059/31250000000 : ℝ) (19854086597/25000000000 : ℝ) (7941634639/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1088_exp_lower
  have heNumeric : (1027451280651/500000000000 : ℝ)/4 ≤ Real.exp (-426282195021/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451280651/500000000000 : ℝ)/4 ≤ Real.exp ((8395/65536 : ℝ)-(7941634639/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8395/65536 : ℝ) (67161/524288 : ℝ) (7941634639/10000000000 : ℝ) (1027451280651/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1089; no trusted numerical premise.
theorem cover8_leaf1089_exp_radius : (998000418256369387/1000000000000000000 : ℝ) ≤ Real.exp ((-33581/2097152 : ℝ)/8) ∧ Real.exp ((-33581/2097152 : ℝ)/8) ≤ (249500104564092347/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33581/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1089_exp_lower : (184022701162866621/200000000000000000 : ℝ) ≤ Real.exp ((-85256438440023/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256438440023/128000000000000 : ℝ)/8) ≤ (460056752907166553/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256438440023/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1089_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902570359/1000000000000 : ℝ) ≤ 4*Real.exp (67161/524288 : ℝ)*Real.exp (-mu (radius 8 (33581/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902570359/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33581/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1089_exp_radius
  have hrNumeric : (984114852609/1000000000000 : ℝ) ≤ Real.exp (-33581/2097152 : ℝ) ∧ Real.exp (-33581/2097152 : ℝ) ≤ (98411485261/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984114852609/1000000000000 : ℝ) ≤ (radius 8 (33581/262144 : ℝ)) ∧ (radius 8 (33581/262144 : ℝ)) ≤ (98411485261/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33581/262144 : ℝ)) (984114852609/1000000000000 : ℝ) (98411485261/100000000000 : ℝ) (88766487021/500000000000 : ℝ) (177532974049/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33581/262144 : ℝ)) (984114852609/1000000000000 : ℝ) (98411485261/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984114852609/1000000000000 : ℝ) (98411485261/100000000000 : ℝ) (7750448643/7812500000 : ℝ) (198411485261/200000000000 : ℝ) (62001601939/62500000000 : ℝ) (39681025241/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 1 (7750448643/7812500000 : ℝ) (198411485261/200000000000 : ℝ) (62001601939/62500000000 : ℝ) (39681025241/40000000000 : ℝ) (124005191083/125000000000 : ℝ) (198408305733/200000000000 : ℝ) (124005191067/125000000000 : ℝ) (496020764269/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 2 (124005191083/125000000000 : ℝ) (198408305733/200000000000 : ℝ) (124005191067/125000000000 : ℝ) (496020764269/500000000000 : ℝ) (4960207643/5000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 3 (4960207643/5000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 4 (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 5 (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 6 (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33581/262144 : ℝ)) 7 (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33581/262144 : ℝ))) (88766487021/500000000000 : ℝ) (177532974049/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88766487021/500000000000 : ℝ) (177532974049/1000000000000 : ℝ) (588766487021/1000000000000 : ℝ) (23550659481/40000000000 : ℝ) (421346619829/1000000000000 : ℝ) (421346619839/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 1 (588766487021/1000000000000 : ℝ) (23550659481/40000000000 : ℝ) (421346619829/1000000000000 : ℝ) (421346619839/1000000000000 : ℝ) (20202262137/40000000000 : ℝ) (63132069179/125000000000 : ℝ) (778236013/1562500000 : ℝ) (62258881041/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 2 (20202262137/40000000000 : ℝ) (63132069179/125000000000 : ℝ) (778236013/1562500000 : ℝ) (62258881041/125000000000 : ℝ) (62695475109/125000000000 : ℝ) (6269547511/12500000000 : ℝ) (6269395493/12500000000 : ℝ) (62693954931/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 3 (62695475109/125000000000 : ℝ) (6269547511/12500000000 : ℝ) (6269395493/12500000000 : ℝ) (62693954931/125000000000 : ℝ) (125389430039/250000000000 : ℝ) (125389430041/250000000000 : ℝ) (501557720119/1000000000000 : ℝ) (7836839377/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 4 (125389430039/250000000000 : ℝ) (125389430041/250000000000 : ℝ) (501557720119/1000000000000 : ℝ) (7836839377/15625000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 5 (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 6 (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33581/262144 : ℝ))) 7 (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33581/262144 : ℝ)) hmem 8 (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33581/262144 : ℝ))) hcmem 8 (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33581/262144 : ℝ)) (992041528599/1000000000000 : ℝ) (496020764301/500000000000 : ℝ) (501557720137/1000000000000 : ℝ) (250778860073/500000000000 : ℝ) (794165366823/1000000000000 : ℝ) (794165366841/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1089_exp_lower
  have heNumeric : (2054902570359/1000000000000 : ℝ)/4 ≤ Real.exp (-85256438440023/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902570359/1000000000000 : ℝ)/4 ≤ Real.exp ((67161/524288 : ℝ)-(794165366841/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67161/524288 : ℝ) (33581/262144 : ℝ) (794165366841/1000000000000 : ℝ) (2054902570359/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1090; no trusted numerical premise.
theorem cover8_leaf1090_exp_radius : (998000388513639623/1000000000000000000 : ℝ) ≤ Real.exp ((-67163/4194304 : ℝ)/8) ∧ Real.exp ((-67163/4194304 : ℝ)/8) ≤ (124750048564204953/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67163/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1090_exp_lower : (57507094145201791/62500000000000000 : ℝ) ≤ Real.exp ((-8525643787367/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525643787367/12800000000000 : ℝ)/8) ≤ (920113506323228657/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525643787367/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1090_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725644863/250000000000 : ℝ) ≤ 4*Real.exp (33581/262144 : ℝ)*Real.exp (-mu (radius 8 (67163/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725644863/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67163/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1090_exp_radius
  have hrNumeric : (492057308989/500000000000 : ℝ) ≤ Real.exp (-67163/4194304 : ℝ) ∧ Real.exp (-67163/4194304 : ℝ) ≤ (984114617979/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492057308989/500000000000 : ℝ) ≤ (radius 8 (67163/524288 : ℝ)) ∧ (radius 8 (67163/524288 : ℝ)) ≤ (984114617979/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67163/524288 : ℝ)) (492057308989/500000000000 : ℝ) (984114617979/1000000000000 : ℝ) (88767137331/500000000000 : ℝ) (177534274669/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67163/524288 : ℝ)) (492057308989/500000000000 : ℝ) (984114617979/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492057308989/500000000000 : ℝ) (984114617979/1000000000000 : ℝ) (992057308989/1000000000000 : ℝ) (99205730899/100000000000 : ℝ) (198405102553/200000000000 : ℝ) (992025512767/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 1 (992057308989/1000000000000 : ℝ) (99205730899/100000000000 : ℝ) (198405102553/200000000000 : ℝ) (992025512767/1000000000000 : ℝ) (992041410877/1000000000000 : ℝ) (992041410879/1000000000000 : ℝ) (992041410749/1000000000000 : ℝ) (15500647043/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 2 (992041410877/1000000000000 : ℝ) (992041410879/1000000000000 : ℝ) (992041410749/1000000000000 : ℝ) (15500647043/15625000000 : ℝ) (992041410813/1000000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 3 (992041410813/1000000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 4 (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 5 (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 6 (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67163/524288 : ℝ)) 7 (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67163/524288 : ℝ))) (88767137331/500000000000 : ℝ) (177534274669/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88767137331/500000000000 : ℝ) (177534274669/1000000000000 : ℝ) (588767137331/1000000000000 : ℝ) (117753427467/200000000000 : ℝ) (84269632647/200000000000 : ℝ) (105337040811/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 1 (588767137331/1000000000000 : ℝ) (117753427467/200000000000 : ℝ) (84269632647/200000000000 : ℝ) (105337040811/250000000000 : ℝ) (505057650283/1000000000000 : ℝ) (50505765029/100000000000 : ℝ) (124518058903/250000000000 : ℝ) (24903611781/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 2 (505057650283/1000000000000 : ℝ) (50505765029/100000000000 : ℝ) (124518058903/250000000000 : ℝ) (24903611781/50000000000 : ℝ) (501564942947/1000000000000 : ℝ) (100312988591/200000000000 : ℝ) (501552781857/1000000000000 : ℝ) (250776390933/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 3 (501564942947/1000000000000 : ℝ) (100312988591/200000000000 : ℝ) (501552781857/1000000000000 : ℝ) (250776390933/500000000000 : ℝ) (250779431201/500000000000 : ℝ) (501558862411/1000000000000 : ℝ) (100311772473/200000000000 : ℝ) (250779431187/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 4 (250779431201/500000000000 : ℝ) (501558862411/1000000000000 : ℝ) (100311772473/200000000000 : ℝ) (250779431187/500000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 5 (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 6 (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67163/524288 : ℝ))) 7 (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67163/524288 : ℝ)) hmem 8 (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67163/524288 : ℝ))) hcmem 8 (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67163/524288 : ℝ)) (248010352703/250000000000 : ℝ) (3875161761/3906250000 : ℝ) (501558862383/1000000000000 : ℝ) (501558862393/1000000000000 : ℝ) (158833453949/200000000000 : ℝ) (158833453953/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1090_exp_lower
  have heNumeric : (513725644863/250000000000 : ℝ)/4 ≤ Real.exp (-8525643787367/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725644863/250000000000 : ℝ)/4 ≤ Real.exp ((33581/262144 : ℝ)-(158833453953/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33581/262144 : ℝ) (67163/524288 : ℝ) (158833453953/200000000000 : ℝ) (513725644863/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1091; no trusted numerical premise.
theorem cover8_leaf1091_exp_radius : (124750044846363843/125000000000000000 : ℝ) ≤ Real.exp ((-16791/1048576 : ℝ)/8) ∧ Real.exp ((-16791/1048576 : ℝ)/8) ≤ (199600071754182149/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16791/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1091_exp_lower : (920113506834309477/1000000000000000000 : ℝ) ≤ Real.exp ((-17051287460977/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051287460977/25600000000000 : ℝ)/8) ≤ (460056753417154739/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051287460977/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1091_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902588583/1000000000000 : ℝ) ≤ 4*Real.exp (67163/524288 : ℝ)*Real.exp (-mu (radius 8 (16791/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902588583/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16791/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1091_exp_radius
  have hrNumeric : (984114383347/1000000000000 : ℝ) ≤ Real.exp (-16791/1048576 : ℝ) ∧ Real.exp (-16791/1048576 : ℝ) ≤ (246028595837/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984114383347/1000000000000 : ℝ) ≤ (radius 8 (16791/131072 : ℝ)) ∧ (radius 8 (16791/131072 : ℝ)) ≤ (246028595837/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16791/131072 : ℝ)) (984114383347/1000000000000 : ℝ) (246028595837/250000000000 : ℝ) (177535575273/1000000000000 : ℝ) (177535575279/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16791/131072 : ℝ)) (984114383347/1000000000000 : ℝ) (246028595837/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984114383347/1000000000000 : ℝ) (246028595837/250000000000 : ℝ) (992057191673/1000000000000 : ℝ) (496028595837/500000000000 : ℝ) (992025394507/1000000000000 : ℝ) (248006348627/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 1 (992057191673/1000000000000 : ℝ) (496028595837/500000000000 : ℝ) (992025394507/1000000000000 : ℝ) (248006348627/250000000000 : ℝ) (99204129309/100000000000 : ℝ) (992041293091/1000000000000 : ℝ) (496020646481/500000000000 : ℝ) (248010323241/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 2 (99204129309/100000000000 : ℝ) (992041293091/1000000000000 : ℝ) (496020646481/500000000000 : ℝ) (248010323241/250000000000 : ℝ) (496020646513/500000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 3 (496020646513/500000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 4 (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 5 (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 6 (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16791/131072 : ℝ)) 7 (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16791/131072 : ℝ))) (177535575273/1000000000000 : ℝ) (177535575279/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177535575273/1000000000000 : ℝ) (177535575279/1000000000000 : ℝ) (147191946909/250000000000 : ℝ) (14719194691/25000000000 : ℝ) (3370797653/8000000000 : ℝ) (421349706633/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 1 (147191946909/250000000000 : ℝ) (14719194691/25000000000 : ℝ) (3370797653/8000000000 : ℝ) (421349706633/1000000000000 : ℝ) (50505874713/100000000000 : ℝ) (505058747137/1000000000000 : ℝ) (498073422891/1000000000000 : ℝ) (249036711449/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 2 (50505874713/100000000000 : ℝ) (505058747137/1000000000000 : ℝ) (498073422891/1000000000000 : ℝ) (249036711449/500000000000 : ℝ) (50156608501/100000000000 : ℝ) (250783042509/500000000000 : ℝ) (501553924263/1000000000000 : ℝ) (501553924271/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 3 (50156608501/100000000000 : ℝ) (250783042509/500000000000 : ℝ) (501553924263/1000000000000 : ℝ) (501553924271/1000000000000 : ℝ) (125390001159/250000000000 : ℝ) (100312000929/200000000000 : ℝ) (501560004599/1000000000000 : ℝ) (122451173/244140625 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 4 (125390001159/250000000000 : ℝ) (100312000929/200000000000 : ℝ) (501560004599/1000000000000 : ℝ) (122451173/244140625 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 5 (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 6 (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16791/131072 : ℝ))) 7 (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16791/131072 : ℝ)) hmem 8 (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16791/131072 : ℝ))) hcmem 8 (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16791/131072 : ℝ)) (39681651721/40000000000 : ℝ) (248010323257/250000000000 : ℝ) (501560004617/1000000000000 : ℝ) (501560004627/1000000000000 : ℝ) (15883383453/20000000000 : ℝ) (79416917267/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1091_exp_lower
  have heNumeric : (2054902588583/1000000000000 : ℝ)/4 ≤ Real.exp (-17051287460977/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902588583/1000000000000 : ℝ)/4 ≤ Real.exp ((67163/524288 : ℝ)-(79416917267/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67163/524288 : ℝ) (16791/131072 : ℝ) (79416917267/100000000000 : ℝ) (2054902588583/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1092; no trusted numerical premise.
theorem cover8_leaf1092_exp_radius : (31187510282130711/31250000000000000 : ℝ) ≤ Real.exp ((-67165/4194304 : ℝ)/8) ∧ Real.exp ((-67165/4194304 : ℝ)/8) ≤ (998000329028182753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67165/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1092_exp_lower : (920113507346885483/1000000000000000000 : ℝ) ≤ Real.exp ((-21314109183609/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314109183609/32000000000000 : ℝ)/8) ≤ (230028376836721371/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314109183609/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1092_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902597741/1000000000000 : ℝ) ≤ 4*Real.exp (16791/131072 : ℝ)*Real.exp (-mu (radius 8 (67165/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902597741/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67165/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1092_exp_radius
  have hrNumeric : (196822829743/200000000000 : ℝ) ≤ Real.exp (-67165/4194304 : ℝ) ∧ Real.exp (-67165/4194304 : ℝ) ≤ (246028537179/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196822829743/200000000000 : ℝ) ≤ (radius 8 (67165/524288 : ℝ)) ∧ (radius 8 (67165/524288 : ℝ)) ≤ (246028537179/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67165/524288 : ℝ)) (196822829743/200000000000 : ℝ) (246028537179/250000000000 : ℝ) (177536875879/1000000000000 : ℝ) (35507375177/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67165/524288 : ℝ)) (196822829743/200000000000 : ℝ) (246028537179/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196822829743/200000000000 : ℝ) (246028537179/250000000000 : ℝ) (992057074357/1000000000000 : ℝ) (496028537179/500000000000 : ℝ) (124003159531/125000000000 : ℝ) (992025276249/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 1 (992057074357/1000000000000 : ℝ) (496028537179/500000000000 : ℝ) (124003159531/125000000000 : ℝ) (992025276249/1000000000000 : ℝ) (496020587651/500000000000 : ℝ) (124005146913/125000000000 : ℝ) (39681647007/40000000000 : ℝ) (992041175177/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 2 (496020587651/500000000000 : ℝ) (124005146913/125000000000 : ℝ) (39681647007/40000000000 : ℝ) (992041175177/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 3 (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 4 (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 5 (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 6 (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67165/524288 : ℝ)) 7 (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67165/524288 : ℝ))) (177536875879/1000000000000 : ℝ) (35507375177/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177536875879/1000000000000 : ℝ) (35507375177/200000000000 : ℝ) (588768437939/1000000000000 : ℝ) (588768437943/1000000000000 : ℝ) (210675625001/500000000000 : ℝ) (421351250011/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 1 (588768437939/1000000000000 : ℝ) (588768437943/1000000000000 : ℝ) (210675625001/500000000000 : ℝ) (421351250011/1000000000000 : ℝ) (50505984397/100000000000 : ℝ) (505059843977/1000000000000 : ℝ) (498074610161/1000000000000 : ℝ) (498074610169/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 2 (50505984397/100000000000 : ℝ) (505059843977/1000000000000 : ℝ) (498074610161/1000000000000 : ℝ) (498074610169/1000000000000 : ℝ) (100313445413/200000000000 : ℝ) (501567227073/1000000000000 : ℝ) (501555066661/1000000000000 : ℝ) (501555066669/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 3 (100313445413/200000000000 : ℝ) (501567227073/1000000000000 : ℝ) (501555066661/1000000000000 : ℝ) (501555066669/1000000000000 : ℝ) (501561146863/1000000000000 : ℝ) (501561146871/1000000000000 : ℝ) (250780573413/500000000000 : ℝ) (100312229367/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 4 (501561146863/1000000000000 : ℝ) (501561146871/1000000000000 : ℝ) (250780573413/500000000000 : ℝ) (100312229367/200000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 5 (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 6 (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67165/524288 : ℝ))) 7 (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67165/524288 : ℝ)) hmem 8 (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67165/524288 : ℝ))) hcmem 8 (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67165/524288 : ℝ)) (496020587619/500000000000 : ℝ) (992041175241/1000000000000 : ℝ) (125390286711/250000000000 : ℝ) (501561146853/1000000000000 : ℝ) (99271384443/125000000000 : ℝ) (397085537781/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1092_exp_lower
  have heNumeric : (2054902597741/1000000000000 : ℝ)/4 ≤ Real.exp (-21314109183609/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902597741/1000000000000 : ℝ)/4 ≤ Real.exp ((16791/131072 : ℝ)-(397085537781/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16791/131072 : ℝ) (67165/524288 : ℝ) (397085537781/500000000000 : ℝ) (2054902597741/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1093; no trusted numerical premise.
theorem cover8_leaf1093_exp_radius : (998000299285455647/1000000000000000000 : ℝ) ≤ Real.exp ((-33583/2097152 : ℝ)/8) ∧ Real.exp ((-33583/2097152 : ℝ)/8) ≤ (31187509352670489/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33583/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1093_exp_lower : (230028376965584211/250000000000000000 : ℝ) ≤ Real.exp ((-85256436160787/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256436160787/128000000000000 : ℝ)/8) ≤ (184022701572467369/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256436160787/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1093_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098052139/20000000000 : ℝ) ≤ 4*Real.exp (67165/524288 : ℝ)*Real.exp (-mu (radius 8 (33583/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (41098052139/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33583/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1093_exp_radius
  have hrNumeric : (246028478521/250000000000 : ℝ) ≤ Real.exp (-33583/2097152 : ℝ) ∧ Real.exp (-33583/2097152 : ℝ) ≤ (196822782817/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246028478521/250000000000 : ℝ) ≤ (radius 8 (33583/262144 : ℝ)) ∧ (radius 8 (33583/262144 : ℝ)) ≤ (196822782817/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33583/262144 : ℝ)) (246028478521/250000000000 : ℝ) (196822782817/200000000000 : ℝ) (17753817647/100000000000 : ℝ) (44384544119/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33583/262144 : ℝ)) (246028478521/250000000000 : ℝ) (196822782817/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246028478521/250000000000 : ℝ) (196822782817/200000000000 : ℝ) (496028478521/500000000000 : ℝ) (992056957043/1000000000000 : ℝ) (992025157989/1000000000000 : ℝ) (99202515799/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 1 (496028478521/500000000000 : ℝ) (992056957043/1000000000000 : ℝ) (992025157989/1000000000000 : ℝ) (99202515799/100000000000 : ℝ) (198408211503/200000000000 : ℝ) (992041057517/1000000000000 : ℝ) (248010264347/250000000000 : ℝ) (99204105739/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 2 (198408211503/200000000000 : ℝ) (992041057517/1000000000000 : ℝ) (248010264347/250000000000 : ℝ) (99204105739/100000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 3 (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 4 (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 5 (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 6 (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33583/262144 : ℝ)) 7 (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33583/262144 : ℝ))) (17753817647/100000000000 : ℝ) (44384544119/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17753817647/100000000000 : ℝ) (44384544119/250000000000 : ℝ) (117753817647/200000000000 : ℝ) (294384544119/500000000000 : ℝ) (421352793357/1000000000000 : ℝ) (84270558673/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 1 (117753817647/200000000000 : ℝ) (294384544119/500000000000 : ℝ) (421352793357/1000000000000 : ℝ) (84270558673/200000000000 : ℝ) (126265235199/250000000000 : ℝ) (252530470401/500000000000 : ℝ) (249037898707/500000000000 : ℝ) (498075797421/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 2 (126265235199/250000000000 : ℝ) (252530470401/500000000000 : ℝ) (249037898707/500000000000 : ℝ) (498075797421/1000000000000 : ℝ) (100313673821/200000000000 : ℝ) (62696046139/125000000000 : ℝ) (501556209043/1000000000000 : ℝ) (10031124181/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 3 (100313673821/200000000000 : ℝ) (62696046139/125000000000 : ℝ) (501556209043/1000000000000 : ℝ) (10031124181/20000000000 : ℝ) (250781144537/500000000000 : ℝ) (501562289081/1000000000000 : ℝ) (501562289037/1000000000000 : ℝ) (100312457809/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 4 (250781144537/500000000000 : ℝ) (501562289081/1000000000000 : ℝ) (501562289037/1000000000000 : ℝ) (100312457809/200000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 5 (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 6 (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33583/262144 : ℝ))) 7 (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33583/262144 : ℝ)) hmem 8 (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33583/262144 : ℝ))) hcmem 8 (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33583/262144 : ℝ)) (992041057451/1000000000000 : ℝ) (496020528727/500000000000 : ℝ) (100312457811/200000000000 : ℝ) (501562289063/1000000000000 : ℝ) (794172978413/1000000000000 : ℝ) (794172978429/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1093_exp_lower
  have heNumeric : (41098052139/20000000000 : ℝ)/4 ≤ Real.exp (-85256436160787/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098052139/20000000000 : ℝ)/4 ≤ Real.exp ((67165/524288 : ℝ)-(794172978429/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67165/524288 : ℝ) (33583/262144 : ℝ) (794172978429/1000000000000 : ℝ) (41098052139/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1094; no trusted numerical premise.
theorem cover8_leaf1094_exp_radius : (249500067385682357/250000000000000000 : ℝ) ≤ Real.exp ((-67167/4194304 : ℝ)/8) ∧ Real.exp ((-67167/4194304 : ℝ)/8) ≤ (998000269542729429/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67167/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1094_exp_lower : (57507094273726777/62500000000000000 : ℝ) ≤ Real.exp ((-8525643558509/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525643558509/12800000000000 : ℝ)/8) ≤ (920113508379628433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525643558509/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1094_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16053926689/7812500000 : ℝ) ≤ 4*Real.exp (33583/262144 : ℝ)*Real.exp (-mu (radius 8 (67167/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (16053926689/7812500000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67167/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1094_exp_radius
  have hrNumeric : (984113679453/1000000000000 : ℝ) ≤ Real.exp (-67167/4194304 : ℝ) ∧ Real.exp (-67167/4194304 : ℝ) ≤ (492056839727/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984113679453/1000000000000 : ℝ) ≤ (radius 8 (67167/524288 : ℝ)) ∧ (radius 8 (67167/524288 : ℝ)) ≤ (492056839727/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67167/524288 : ℝ)) (984113679453/1000000000000 : ℝ) (492056839727/500000000000 : ℝ) (3550789541/20000000000 : ℝ) (177539477057/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67167/524288 : ℝ)) (984113679453/1000000000000 : ℝ) (492056839727/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984113679453/1000000000000 : ℝ) (492056839727/500000000000 : ℝ) (496028419863/500000000000 : ℝ) (992056839727/1000000000000 : ℝ) (99202503973/100000000000 : ℝ) (248006259933/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 1 (496028419863/500000000000 : ℝ) (992056839727/1000000000000 : ℝ) (99202503973/100000000000 : ℝ) (248006259933/250000000000 : ℝ) (62002558733/62500000000 : ℝ) (99204093973/100000000000 : ℝ) (2480102349/2500000000 : ℝ) (992040939603/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 2 (62002558733/62500000000 : ℝ) (99204093973/100000000000 : ℝ) (2480102349/2500000000 : ℝ) (992040939603/1000000000000 : ℝ) (62002558729/62500000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 3 (62002558729/62500000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 4 (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 5 (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 6 (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67167/524288 : ℝ)) 7 (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67167/524288 : ℝ))) (3550789541/20000000000 : ℝ) (177539477057/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3550789541/20000000000 : ℝ) (177539477057/1000000000000 : ℝ) (23550789541/40000000000 : ℝ) (588769738529/1000000000000 : ℝ) (421354336693/1000000000000 : ℝ) (210677168351/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 1 (23550789541/40000000000 : ℝ) (588769738529/1000000000000 : ℝ) (421354336693/1000000000000 : ℝ) (210677168351/500000000000 : ℝ) (505062037609/1000000000000 : ℝ) (31566377351/62500000000 : ℝ) (498076984653/1000000000000 : ℝ) (498076984661/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 2 (505062037609/1000000000000 : ℝ) (31566377351/62500000000 : ℝ) (498076984653/1000000000000 : ℝ) (498076984661/1000000000000 : ℝ) (501569511131/1000000000000 : ℝ) (501569511139/1000000000000 : ℝ) (501557351411/1000000000000 : ℝ) (25077867571/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 3 (501569511131/1000000000000 : ℝ) (501569511139/1000000000000 : ℝ) (501557351411/1000000000000 : ℝ) (25077867571/50000000000 : ℝ) (501563431271/1000000000000 : ℝ) (6269542891/12500000000 : ℝ) (250781715617/500000000000 : ℝ) (501563431243/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 4 (501563431271/1000000000000 : ℝ) (6269542891/12500000000 : ℝ) (250781715617/500000000000 : ℝ) (501563431243/1000000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 5 (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 6 (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67167/524288 : ℝ))) 7 (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67167/524288 : ℝ)) hmem 8 (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67167/524288 : ℝ))) hcmem 8 (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67167/524288 : ℝ)) (992040939663/1000000000000 : ℝ) (992040939667/1000000000000 : ℝ) (125390857813/250000000000 : ℝ) (250781715631/500000000000 : ℝ) (39708744063/50000000000 : ℝ) (310224563/390625000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1094_exp_lower
  have heNumeric : (16053926689/7812500000 : ℝ)/4 ≤ Real.exp (-8525643558509/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16053926689/7812500000 : ℝ)/4 ≤ Real.exp ((33583/262144 : ℝ)-(310224563/390625000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33583/262144 : ℝ) (67167/524288 : ℝ) (310224563/390625000 : ℝ) (16053926689/7812500000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1095; no trusted numerical premise.
theorem cover8_leaf1095_exp_radius : (199600047960000819/200000000000000000 : ℝ) ≤ Real.exp ((-2099/131072 : ℝ)/8) ∧ Real.exp ((-2099/131072 : ℝ)/8) ≤ (1949219218359383/1953125000000000 : ℝ) := by
  have h := exp_small_bounds ((-2099/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1095_exp_lower : (7360908071198363/8000000000000000 : ℝ) ≤ Real.exp ((-85256435006193/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256435006193/128000000000000 : ℝ)/8) ≤ (57507094306237211/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256435006193/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1095_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451312743/500000000000 : ℝ) ≤ 4*Real.exp (67167/524288 : ℝ)*Real.exp (-mu (radius 8 (2099/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451312743/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2099/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1095_exp_radius
  have hrNumeric : (492056722411/500000000000 : ℝ) ≤ Real.exp (-2099/131072 : ℝ) ∧ Real.exp (-2099/131072 : ℝ) ≤ (984113444823/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492056722411/500000000000 : ℝ) ≤ (radius 8 (2099/16384 : ℝ)) ∧ (radius 8 (2099/16384 : ℝ)) ≤ (984113444823/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2099/16384 : ℝ)) (492056722411/500000000000 : ℝ) (984113444823/1000000000000 : ℝ) (177540777621/1000000000000 : ℝ) (44385194407/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2099/16384 : ℝ)) (492056722411/500000000000 : ℝ) (984113444823/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492056722411/500000000000 : ℝ) (984113444823/1000000000000 : ℝ) (992056722411/1000000000000 : ℝ) (248014180603/250000000000 : ℝ) (7750194699/7812500000 : ℝ) (992024921473/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 1 (992056722411/1000000000000 : ℝ) (248014180603/250000000000 : ℝ) (7750194699/7812500000 : ℝ) (992024921473/1000000000000 : ℝ) (992040821941/1000000000000 : ℝ) (992040821943/1000000000000 : ℝ) (496020410907/500000000000 : ℝ) (124005102727/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 2 (992040821941/1000000000000 : ℝ) (992040821943/1000000000000 : ℝ) (496020410907/500000000000 : ℝ) (124005102727/125000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 3 (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 4 (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 5 (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 6 (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2099/16384 : ℝ)) 7 (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2099/16384 : ℝ))) (177540777621/1000000000000 : ℝ) (44385194407/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177540777621/1000000000000 : ℝ) (44385194407/250000000000 : ℝ) (58877038881/100000000000 : ℝ) (294385194407/500000000000 : ℝ) (105338970003/250000000000 : ℝ) (421355880021/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 1 (58877038881/100000000000 : ℝ) (294385194407/500000000000 : ℝ) (105338970003/250000000000 : ℝ) (421355880021/1000000000000 : ℝ) (505063134411/1000000000000 : ℝ) (252531567209/500000000000 : ℝ) (249039085939/500000000000 : ℝ) (249039085943/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 2 (505063134411/1000000000000 : ℝ) (252531567209/500000000000 : ℝ) (249039085939/500000000000 : ℝ) (249039085943/500000000000 : ℝ) (62696331643/125000000000 : ℝ) (15674082911/31250000000 : ℝ) (501558493767/1000000000000 : ℝ) (31347405861/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 3 (62696331643/125000000000 : ℝ) (15674082911/31250000000 : ℝ) (501558493767/1000000000000 : ℝ) (31347405861/62500000000 : ℝ) (100312914691/200000000000 : ℝ) (62695571683/125000000000 : ℝ) (250782286709/500000000000 : ℝ) (125391143357/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 4 (100312914691/200000000000 : ℝ) (62695571683/125000000000 : ℝ) (250782286709/500000000000 : ℝ) (125391143357/250000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 5 (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 6 (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2099/16384 : ℝ))) 7 (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2099/16384 : ℝ)) hmem 8 (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2099/16384 : ℝ))) hcmem 8 (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2099/16384 : ℝ)) (992040821877/1000000000000 : ℝ) (24801020547/25000000000 : ℝ) (125391143359/250000000000 : ℝ) (250782286723/500000000000 : ℝ) (794176784087/1000000000000 : ℝ) (397088392053/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1095_exp_lower
  have heNumeric : (1027451312743/500000000000 : ℝ)/4 ≤ Real.exp (-85256435006193/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451312743/500000000000 : ℝ)/4 ≤ Real.exp ((67167/524288 : ℝ)-(397088392053/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67167/524288 : ℝ) (2099/16384 : ℝ) (397088392053/500000000000 : ℝ) (1027451312743/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1096; no trusted numerical premise.
theorem cover8_leaf1096_exp_radius : (998000210057279649/1000000000000000000 : ℝ) ≤ Real.exp ((-67169/4194304 : ℝ)/8) ∧ Real.exp ((-67169/4194304 : ℝ)/8) ≤ (19960004201145593/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67169/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1096_exp_lower : (460056754710901273/500000000000000000 : ℝ) ≤ Real.exp ((-2664263575789/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664263575789/4000000000000 : ℝ)/8) ≤ (920113509421802547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664263575789/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1096_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725658703/250000000000 : ℝ) ≤ 4*Real.exp (2099/16384 : ℝ)*Real.exp (-mu (radius 8 (67169/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725658703/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67169/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1096_exp_radius
  have hrNumeric : (984113210191/1000000000000 : ℝ) ≤ Real.exp (-67169/4194304 : ℝ) ∧ Real.exp (-67169/4194304 : ℝ) ≤ (61507075637/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984113210191/1000000000000 : ℝ) ≤ (radius 8 (67169/524288 : ℝ)) ∧ (radius 8 (67169/524288 : ℝ)) ≤ (61507075637/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67169/524288 : ℝ)) (984113210191/1000000000000 : ℝ) (61507075637/62500000000 : ℝ) (177542078183/1000000000000 : ℝ) (177542078189/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67169/524288 : ℝ)) (984113210191/1000000000000 : ℝ) (61507075637/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984113210191/1000000000000 : ℝ) (61507075637/62500000000 : ℝ) (198411321019/200000000000 : ℝ) (124007075637/125000000000 : ℝ) (992024803213/1000000000000 : ℝ) (198404960643/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 1 (198411321019/200000000000 : ℝ) (124007075637/125000000000 : ℝ) (992024803213/1000000000000 : ℝ) (198404960643/200000000000 : ℝ) (496020352077/500000000000 : ℝ) (248010176039/250000000000 : ℝ) (496020352013/500000000000 : ℝ) (992040704029/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 2 (496020352077/500000000000 : ℝ) (248010176039/250000000000 : ℝ) (496020352013/500000000000 : ℝ) (992040704029/1000000000000 : ℝ) (99204070409/100000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 3 (99204070409/100000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 4 (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 5 (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 6 (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67169/524288 : ℝ)) 7 (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67169/524288 : ℝ))) (177542078183/1000000000000 : ℝ) (177542078189/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177542078183/1000000000000 : ℝ) (177542078189/1000000000000 : ℝ) (588771039091/1000000000000 : ℝ) (117754207819/200000000000 : ℝ) (84271484663/200000000000 : ℝ) (421357423323/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 1 (588771039091/1000000000000 : ℝ) (117754207819/200000000000 : ℝ) (84271484663/200000000000 : ℝ) (421357423323/1000000000000 : ℝ) (505064231203/1000000000000 : ℝ) (505064231209/1000000000000 : ℝ) (124519839773/250000000000 : ℝ) (498079359099/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 2 (505064231203/1000000000000 : ℝ) (505064231209/1000000000000 : ℝ) (124519839773/250000000000 : ℝ) (498079359099/1000000000000 : ℝ) (501571795147/1000000000000 : ℝ) (250785897577/500000000000 : ℝ) (501559636113/1000000000000 : ℝ) (12538990903/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 3 (501571795147/1000000000000 : ℝ) (250785897577/500000000000 : ℝ) (501559636113/1000000000000 : ℝ) (12538990903/25000000000 : ℝ) (50156571563/100000000000 : ℝ) (501565715637/1000000000000 : ℝ) (501565715593/1000000000000 : ℝ) (501565715601/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 4 (50156571563/100000000000 : ℝ) (501565715637/1000000000000 : ℝ) (501565715593/1000000000000 : ℝ) (501565715601/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 5 (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 6 (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67169/524288 : ℝ))) 7 (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67169/524288 : ℝ)) hmem 8 (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67169/524288 : ℝ))) hcmem 8 (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67169/524288 : ℝ)) (992040704089/1000000000000 : ℝ) (992040704093/1000000000000 : ℝ) (501565715611/1000000000000 : ℝ) (501565715619/1000000000000 : ℝ) (7941786869/10000000000 : ℝ) (198544671729/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1096_exp_lower
  have heNumeric : (513725658703/250000000000 : ℝ)/4 ≤ Real.exp (-2664263575789/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725658703/250000000000 : ℝ)/4 ≤ Real.exp ((2099/16384 : ℝ)-(198544671729/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2099/16384 : ℝ) (67169/524288 : ℝ) (198544671729/250000000000 : ℝ) (513725658703/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1097; no trusted numerical premise.
theorem cover8_leaf1097_exp_radius : (998000180314556089/1000000000000000000 : ℝ) ≤ Real.exp ((-33585/2097152 : ℝ)/8) ∧ Real.exp ((-33585/2097152 : ℝ)/8) ≤ (99800018031455609/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33585/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1097_exp_lower : (920113509946685071/1000000000000000000 : ℝ) ≤ Real.exp ((-85256433841103/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256433841103/128000000000000 : ℝ)/8) ≤ (57507094371667817/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256433841103/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1097_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490264419/100000000000 : ℝ) ≤ 4*Real.exp (67169/524288 : ℝ)*Real.exp (-mu (radius 8 (33585/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490264419/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33585/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1097_exp_radius
  have hrNumeric : (984112975561/1000000000000 : ℝ) ≤ Real.exp (-33585/2097152 : ℝ) ∧ Real.exp (-33585/2097152 : ℝ) ≤ (492056487781/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984112975561/1000000000000 : ℝ) ≤ (radius 8 (33585/262144 : ℝ)) ∧ (radius 8 (33585/262144 : ℝ)) ≤ (492056487781/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33585/262144 : ℝ)) (984112975561/1000000000000 : ℝ) (492056487781/500000000000 : ℝ) (22192922341/125000000000 : ℝ) (35508675747/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33585/262144 : ℝ)) (984112975561/1000000000000 : ℝ) (492056487781/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984112975561/1000000000000 : ℝ) (492056487781/500000000000 : ℝ) (49602824389/50000000000 : ℝ) (992056487781/1000000000000 : ℝ) (198404936991/200000000000 : ℝ) (248006171239/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 1 (49602824389/50000000000 : ℝ) (992056487781/1000000000000 : ℝ) (198404936991/200000000000 : ℝ) (248006171239/250000000000 : ℝ) (992040586367/1000000000000 : ℝ) (992040586369/1000000000000 : ℝ) (193757927/195312500 : ℝ) (496020293121/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 2 (992040586367/1000000000000 : ℝ) (992040586369/1000000000000 : ℝ) (193757927/195312500 : ℝ) (496020293121/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 3 (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 4 (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 5 (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 6 (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33585/262144 : ℝ)) 7 (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33585/262144 : ℝ))) (22192922341/125000000000 : ℝ) (35508675747/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22192922341/125000000000 : ℝ) (35508675747/200000000000 : ℝ) (147192922341/250000000000 : ℝ) (73596461171/125000000000 : ℝ) (6583733853/15625000000 : ℝ) (421358966601/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 1 (147192922341/250000000000 : ℝ) (73596461171/125000000000 : ℝ) (6583733853/15625000000 : ℝ) (421358966601/1000000000000 : ℝ) (252532663989/500000000000 : ℝ) (101013065597/200000000000 : ℝ) (249040273143/500000000000 : ℝ) (249040273147/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 2 (252532663989/500000000000 : ℝ) (101013065597/200000000000 : ℝ) (249040273143/500000000000 : ℝ) (249040273147/500000000000 : ℝ) (125393234283/250000000000 : ℝ) (25078646857/50000000000 : ℝ) (12539019461/25000000000 : ℝ) (31347548653/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 3 (125393234283/250000000000 : ℝ) (25078646857/50000000000 : ℝ) (12539019461/25000000000 : ℝ) (31347548653/62500000000 : ℝ) (250783428893/500000000000 : ℝ) (250783428897/500000000000 : ℝ) (501566857749/1000000000000 : ℝ) (250783428879/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 4 (250783428893/500000000000 : ℝ) (250783428897/500000000000 : ℝ) (501566857749/1000000000000 : ℝ) (250783428879/500000000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 5 (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 6 (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33585/262144 : ℝ))) 7 (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33585/262144 : ℝ)) hmem 8 (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33585/262144 : ℝ))) hcmem 8 (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33585/262144 : ℝ)) (992040586303/1000000000000 : ℝ) (496020293153/500000000000 : ℝ) (501566857767/1000000000000 : ℝ) (31347928611/62500000000 : ℝ) (794180589683/1000000000000 : ℝ) (794180589701/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1097_exp_lower
  have heNumeric : (205490264419/100000000000 : ℝ)/4 ≤ Real.exp (-85256433841103/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490264419/100000000000 : ℝ)/4 ≤ Real.exp ((67169/524288 : ℝ)-(794180589701/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67169/524288 : ℝ) (33585/262144 : ℝ) (794180589701/1000000000000 : ℝ) (205490264419/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1098; no trusted numerical premise.
theorem cover8_leaf1098_exp_radius : (199600030114366683/200000000000000000 : ℝ) ≤ Real.exp ((-67171/4194304 : ℝ)/8) ∧ Real.exp ((-67171/4194304 : ℝ)/8) ≤ (124750018821479177/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67171/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1098_exp_lower : (920113510472832753/1000000000000000000 : ℝ) ≤ Real.exp ((-1705128665111/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705128665111/2560000000000 : ℝ)/8) ≤ (460056755236416377/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705128665111/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1098_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902653591/1000000000000 : ℝ) ≤ 4*Real.exp (33585/262144 : ℝ)*Real.exp (-mu (radius 8 (67171/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902653591/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67171/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1098_exp_radius
  have hrNumeric : (98411274093/100000000000 : ℝ) ≤ Real.exp (-67171/4194304 : ℝ) ∧ Real.exp (-67171/4194304 : ℝ) ≤ (984112740931/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98411274093/100000000000 : ℝ) ≤ (radius 8 (67171/524288 : ℝ)) ∧ (radius 8 (67171/524288 : ℝ)) ≤ (984112740931/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67171/524288 : ℝ)) (98411274093/100000000000 : ℝ) (984112740931/1000000000000 : ℝ) (17754467927/100000000000 : ℝ) (177544679277/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67171/524288 : ℝ)) (98411274093/100000000000 : ℝ) (984112740931/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98411274093/100000000000 : ℝ) (984112740931/1000000000000 : ℝ) (198411274093/200000000000 : ℝ) (496028185233/500000000000 : ℝ) (124003070837/125000000000 : ℝ) (496012283349/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 1 (198411274093/200000000000 : ℝ) (496028185233/500000000000 : ℝ) (124003070837/125000000000 : ℝ) (496012283349/500000000000 : ℝ) (49602023429/50000000000 : ℝ) (496020234291/500000000000 : ℝ) (992040468453/1000000000000 : ℝ) (198408093691/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 2 (49602023429/50000000000 : ℝ) (496020234291/500000000000 : ℝ) (992040468453/1000000000000 : ℝ) (198408093691/200000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 3 (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 4 (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 5 (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 6 (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67171/524288 : ℝ)) 7 (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67171/524288 : ℝ))) (17754467927/100000000000 : ℝ) (177544679277/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17754467927/100000000000 : ℝ) (177544679277/1000000000000 : ℝ) (117754467927/200000000000 : ℝ) (588772339639/1000000000000 : ℝ) (21068025493/50000000000 : ℝ) (421360509869/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 1 (117754467927/200000000000 : ℝ) (588772339639/1000000000000 : ℝ) (21068025493/50000000000 : ℝ) (421360509869/1000000000000 : ℝ) (505066424747/1000000000000 : ℝ) (252533212377/500000000000 : ℝ) (498081733473/1000000000000 : ℝ) (498081733481/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 2 (505066424747/1000000000000 : ℝ) (252533212377/500000000000 : ℝ) (498081733473/1000000000000 : ℝ) (498081733481/1000000000000 : ℝ) (50157407911/100000000000 : ℝ) (250787039559/500000000000 : ℝ) (12539048019/25000000000 : ℝ) (501561920769/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 3 (50157407911/100000000000 : ℝ) (250787039559/500000000000 : ℝ) (12539048019/25000000000 : ℝ) (501561920769/1000000000000 : ℝ) (100313599987/200000000000 : ℝ) (62695999993/125000000000 : ℝ) (250783999949/500000000000 : ℝ) (501567999907/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 4 (100313599987/200000000000 : ℝ) (62695999993/125000000000 : ℝ) (250783999949/500000000000 : ℝ) (501567999907/1000000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 5 (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 6 (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67171/524288 : ℝ))) 7 (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67171/524288 : ℝ)) hmem 8 (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67171/524288 : ℝ))) hcmem 8 (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67171/524288 : ℝ)) (248010117129/250000000000 : ℝ) (992040468519/1000000000000 : ℝ) (125391999979/250000000000 : ℝ) (250783999963/500000000000 : ℝ) (99272811557/125000000000 : ℝ) (31767299699/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1098_exp_lower
  have heNumeric : (2054902653591/1000000000000 : ℝ)/4 ≤ Real.exp (-1705128665111/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902653591/1000000000000 : ℝ)/4 ≤ Real.exp ((33585/262144 : ℝ)-(31767299699/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33585/262144 : ℝ) (67171/524288 : ℝ) (31767299699/40000000000 : ℝ) (2054902653591/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1099; no trusted numerical premise.
theorem cover8_leaf1099_exp_radius : (249500030207277907/250000000000000000 : ℝ) ≤ Real.exp ((-16793/1048576 : ℝ)/8) ∧ Real.exp ((-16793/1048576 : ℝ)/8) ≤ (998000120829111629/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16793/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1099_exp_lower : (920113511001395733/1000000000000000000 : ℝ) ≤ Real.exp ((-85256432667309/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256432667309/128000000000000 : ℝ)/8) ≤ (460056755500697867/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256432667309/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1099_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451331517/500000000000 : ℝ) ≤ 4*Real.exp (67171/524288 : ℝ)*Real.exp (-mu (radius 8 (16793/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451331517/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16793/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1099_exp_radius
  have hrNumeric : (984112506299/1000000000000 : ℝ) ≤ Real.exp (-16793/1048576 : ℝ) ∧ Real.exp (-16793/1048576 : ℝ) ≤ (9841125063/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984112506299/1000000000000 : ℝ) ≤ (radius 8 (16793/131072 : ℝ)) ∧ (radius 8 (16793/131072 : ℝ)) ≤ (9841125063/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16793/131072 : ℝ)) (984112506299/1000000000000 : ℝ) (9841125063/10000000000 : ℝ) (88772989901/500000000000 : ℝ) (5548311869/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16793/131072 : ℝ)) (984112506299/1000000000000 : ℝ) (9841125063/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984112506299/1000000000000 : ℝ) (9841125063/10000000000 : ℝ) (992056253149/1000000000000 : ℝ) (19841125063/20000000000 : ℝ) (496012224219/500000000000 : ℝ) (992024448439/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 1 (992056253149/1000000000000 : ℝ) (19841125063/20000000000 : ℝ) (496012224219/500000000000 : ℝ) (992024448439/1000000000000 : ℝ) (992040350793/1000000000000 : ℝ) (198408070159/200000000000 : ℝ) (496020175333/500000000000 : ℝ) (248010087667/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 2 (992040350793/1000000000000 : ℝ) (198408070159/200000000000 : ℝ) (496020175333/500000000000 : ℝ) (248010087667/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 3 (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 4 (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 5 (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 6 (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16793/131072 : ℝ)) 7 (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16793/131072 : ℝ))) (88772989901/500000000000 : ℝ) (5548311869/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88772989901/500000000000 : ℝ) (5548311869/31250000000 : ℝ) (588772989901/1000000000000 : ℝ) (36798311869/62500000000 : ℝ) (421362053111/1000000000000 : ℝ) (421362053119/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 1 (588772989901/1000000000000 : ℝ) (36798311869/62500000000 : ℝ) (421362053111/1000000000000 : ℝ) (421362053119/1000000000000 : ℝ) (252533760753/500000000000 : ℝ) (63133440189/125000000000 : ℝ) (498082920647/1000000000000 : ℝ) (249041460327/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 2 (252533760753/500000000000 : ℝ) (63133440189/125000000000 : ℝ) (498082920647/1000000000000 : ℝ) (249041460327/500000000000 : ℝ) (125393805269/250000000000 : ℝ) (501575221083/1000000000000 : ℝ) (501563063069/1000000000000 : ℝ) (125390765769/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 3 (125393805269/250000000000 : ℝ) (501575221083/1000000000000 : ℝ) (501563063069/1000000000000 : ℝ) (125390765769/250000000000 : ℝ) (62696142759/125000000000 : ℝ) (1567403569/3125000000 : ℝ) (100313828407/200000000000 : ℝ) (501569142043/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 4 (62696142759/125000000000 : ℝ) (1567403569/3125000000 : ℝ) (100313828407/200000000000 : ℝ) (501569142043/1000000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 5 (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 6 (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16793/131072 : ℝ))) 7 (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16793/131072 : ℝ)) hmem 8 (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16793/131072 : ℝ))) hcmem 8 (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16793/131072 : ℝ)) (992040350729/1000000000000 : ℝ) (248010087683/250000000000 : ℝ) (501569142053/1000000000000 : ℝ) (250784571031/500000000000 : ℝ) (79418439521/100000000000 : ℝ) (198546098807/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1099_exp_lower
  have heNumeric : (1027451331517/500000000000 : ℝ)/4 ≤ Real.exp (-85256432667309/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451331517/500000000000 : ℝ)/4 ≤ Real.exp ((67171/524288 : ℝ)-(198546098807/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67171/524288 : ℝ) (16793/131072 : ℝ) (198546098807/250000000000 : ℝ) (1027451331517/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1075_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1075_certificate
#check SmaleRate.Proofs.cover8_leaf1076_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1076_certificate
#check SmaleRate.Proofs.cover8_leaf1077_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1077_certificate
#check SmaleRate.Proofs.cover8_leaf1078_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1078_certificate
#check SmaleRate.Proofs.cover8_leaf1079_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1079_certificate
#check SmaleRate.Proofs.cover8_leaf1080_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1080_certificate
#check SmaleRate.Proofs.cover8_leaf1081_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1081_certificate
#check SmaleRate.Proofs.cover8_leaf1082_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1082_certificate
#check SmaleRate.Proofs.cover8_leaf1083_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1083_certificate
#check SmaleRate.Proofs.cover8_leaf1084_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1084_certificate
#check SmaleRate.Proofs.cover8_leaf1085_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1085_certificate
#check SmaleRate.Proofs.cover8_leaf1086_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1086_certificate
#check SmaleRate.Proofs.cover8_leaf1087_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1087_certificate
#check SmaleRate.Proofs.cover8_leaf1088_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1088_certificate
#check SmaleRate.Proofs.cover8_leaf1089_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1089_certificate
#check SmaleRate.Proofs.cover8_leaf1090_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1090_certificate
#check SmaleRate.Proofs.cover8_leaf1091_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1091_certificate
#check SmaleRate.Proofs.cover8_leaf1092_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1092_certificate
#check SmaleRate.Proofs.cover8_leaf1093_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1093_certificate
#check SmaleRate.Proofs.cover8_leaf1094_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1094_certificate
#check SmaleRate.Proofs.cover8_leaf1095_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1095_certificate
#check SmaleRate.Proofs.cover8_leaf1096_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1096_certificate
#check SmaleRate.Proofs.cover8_leaf1097_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1097_certificate
#check SmaleRate.Proofs.cover8_leaf1098_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1098_certificate
#check SmaleRate.Proofs.cover8_leaf1099_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1099_certificate
