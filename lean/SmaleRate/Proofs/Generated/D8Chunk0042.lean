/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1050; no trusted numerical premise.
theorem cover8_leaf1050_exp_radius : (499000789111760803/500000000000000000 : ℝ) ≤ Real.exp ((-67123/4194304 : ℝ)/8) ∧ Real.exp ((-67123/4194304 : ℝ)/8) ≤ (998001578223521607/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67123/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1050_exp_lower : (184022697539306019/200000000000000000 : ℝ) ≤ Real.exp ((-42628229301719/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628229301719/64000000000000 : ℝ)/8) ≤ (57507092981033131/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628229301719/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1050_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451123329/500000000000 : ℝ) ≤ 4*Real.exp (33561/262144 : ℝ)*Real.exp (-mu (radius 8 (67123/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451123329/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67123/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1050_exp_radius
  have hrNumeric : (984124003271/1000000000000 : ℝ) ≤ Real.exp (-67123/4194304 : ℝ) ∧ Real.exp (-67123/4194304 : ℝ) ≤ (123015500409/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984124003271/1000000000000 : ℝ) ≤ (radius 8 (67123/524288 : ℝ)) ∧ (radius 8 (67123/524288 : ℝ)) ≤ (123015500409/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67123/524288 : ℝ)) (984124003271/1000000000000 : ℝ) (123015500409/125000000000 : ℝ) (177482241883/1000000000000 : ℝ) (177482241889/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67123/524288 : ℝ)) (984124003271/1000000000000 : ℝ) (123015500409/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984124003271/1000000000000 : ℝ) (123015500409/125000000000 : ℝ) (198412400327/200000000000 : ℝ) (248015500409/250000000000 : ℝ) (992030243123/1000000000000 : ℝ) (248007560781/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 1 (198412400327/200000000000 : ℝ) (248015500409/250000000000 : ℝ) (992030243123/1000000000000 : ℝ) (248007560781/250000000000 : ℝ) (992046122379/1000000000000 : ℝ) (49602306119/50000000000 : ℝ) (992046122251/1000000000000 : ℝ) (992046122253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 2 (992046122379/1000000000000 : ℝ) (49602306119/50000000000 : ℝ) (992046122251/1000000000000 : ℝ) (992046122253/1000000000000 : ℝ) (198409224463/200000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 3 (198409224463/200000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 4 (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 5 (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 6 (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67123/524288 : ℝ)) 7 (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67123/524288 : ℝ))) (177482241883/1000000000000 : ℝ) (177482241889/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177482241883/1000000000000 : ℝ) (177482241889/1000000000000 : ℝ) (588741120941/1000000000000 : ℝ) (117748224189/200000000000 : ℝ) (105321603281/250000000000 : ℝ) (105321603283/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 1 (588741120941/1000000000000 : ℝ) (117748224189/200000000000 : ℝ) (105321603281/250000000000 : ℝ) (105321603283/250000000000 : ℝ) (63126720879/125000000000 : ℝ) (505013767039/1000000000000 : ℝ) (498024733421/1000000000000 : ℝ) (498024733429/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 2 (63126720879/125000000000 : ℝ) (505013767039/1000000000000 : ℝ) (498024733421/1000000000000 : ℝ) (498024733429/1000000000000 : ℝ) (250759625113/500000000000 : ℝ) (250759625117/500000000000 : ℝ) (501507075423/1000000000000 : ℝ) (62688384429/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 3 (250759625113/500000000000 : ℝ) (250759625117/500000000000 : ℝ) (501507075423/1000000000000 : ℝ) (62688384429/125000000000 : ℝ) (62689145353/125000000000 : ℝ) (501513162833/1000000000000 : ℝ) (501513162787/1000000000000 : ℝ) (501513162797/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 4 (62689145353/125000000000 : ℝ) (501513162833/1000000000000 : ℝ) (501513162787/1000000000000 : ℝ) (501513162797/1000000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 5 (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 6 (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67123/524288 : ℝ))) 7 (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67123/524288 : ℝ)) hmem 8 (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67123/524288 : ℝ))) hcmem 8 (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67123/524288 : ℝ)) (496023061157/500000000000 : ℝ) (992046122317/1000000000000 : ℝ) (100302632561/200000000000 : ℝ) (100302632563/200000000000 : ℝ) (99261392219/125000000000 : ℝ) (794091137771/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1050_exp_lower
  have heNumeric : (1027451123329/500000000000 : ℝ)/4 ≤ Real.exp (-42628229301719/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451123329/500000000000 : ℝ)/4 ≤ Real.exp ((33561/262144 : ℝ)-(794091137771/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33561/262144 : ℝ) (67123/524288 : ℝ) (794091137771/1000000000000 : ℝ) (1027451123329/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1051; no trusted numerical premise.
theorem cover8_leaf1051_exp_radius : (124750193560094659/125000000000000000 : ℝ) ≤ Real.exp ((-16781/1048576 : ℝ)/8) ∧ Real.exp ((-16781/1048576 : ℝ)/8) ≤ (998001548480757273/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16781/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1051_exp_lower : (460056744059294963/500000000000000000 : ℝ) ≤ Real.exp ((-3410258325349/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410258325349/5120000000000 : ℝ)/8) ≤ (920113488118589927/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410258325349/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1051_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451127099/500000000000 : ℝ) ≤ 4*Real.exp (67123/524288 : ℝ)*Real.exp (-mu (radius 8 (16781/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451127099/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16781/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1051_exp_radius
  have hrNumeric : (984123768637/1000000000000 : ℝ) ≤ Real.exp (-16781/1048576 : ℝ) ∧ Real.exp (-16781/1048576 : ℝ) ≤ (492061884319/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984123768637/1000000000000 : ℝ) ≤ (radius 8 (16781/131072 : ℝ)) ∧ (radius 8 (16781/131072 : ℝ)) ≤ (492061884319/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16781/131072 : ℝ)) (984123768637/1000000000000 : ℝ) (492061884319/500000000000 : ℝ) (177483542903/1000000000000 : ℝ) (17748354291/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16781/131072 : ℝ)) (984123768637/1000000000000 : ℝ) (492061884319/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984123768637/1000000000000 : ℝ) (492061884319/500000000000 : ℝ) (496030942159/500000000000 : ℝ) (992061884319/1000000000000 : ℝ) (992030124863/1000000000000 : ℝ) (198406024973/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 1 (496030942159/500000000000 : ℝ) (992061884319/1000000000000 : ℝ) (992030124863/1000000000000 : ℝ) (198406024973/200000000000 : ℝ) (99204600459/100000000000 : ℝ) (62002875287/62500000000 : ℝ) (992046004463/1000000000000 : ℝ) (198409200893/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 2 (99204600459/100000000000 : ℝ) (62002875287/62500000000 : ℝ) (992046004463/1000000000000 : ℝ) (198409200893/200000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 3 (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 4 (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 5 (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 6 (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16781/131072 : ℝ)) 7 (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16781/131072 : ℝ))) (177483542903/1000000000000 : ℝ) (17748354291/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177483542903/1000000000000 : ℝ) (17748354291/100000000000 : ℝ) (588741771451/1000000000000 : ℝ) (117748354291/200000000000 : ℝ) (16851518289/40000000000 : ℝ) (210643978617/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 1 (588741771451/1000000000000 : ℝ) (117748354291/200000000000 : ℝ) (16851518289/40000000000 : ℝ) (210643978617/500000000000 : ℝ) (252507432169/500000000000 : ℝ) (101002972869/200000000000 : ℝ) (12450648031/25000000000 : ℝ) (15563310039/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 2 (252507432169/500000000000 : ℝ) (101002972869/200000000000 : ℝ) (12450648031/25000000000 : ℝ) (15563310039/31250000000 : ℝ) (501520392789/1000000000000 : ℝ) (501520392797/1000000000000 : ℝ) (501508218329/1000000000000 : ℝ) (501508218337/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 3 (501520392789/1000000000000 : ℝ) (501520392797/1000000000000 : ℝ) (501508218329/1000000000000 : ℝ) (501508218337/1000000000000 : ℝ) (501514305559/1000000000000 : ℝ) (501514305567/1000000000000 : ℝ) (250757152761/500000000000 : ℝ) (501514305531/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 4 (501514305559/1000000000000 : ℝ) (501514305567/1000000000000 : ℝ) (250757152761/500000000000 : ℝ) (501514305531/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 5 (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 6 (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16781/131072 : ℝ))) 7 (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16781/131072 : ℝ)) hmem 8 (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16781/131072 : ℝ))) hcmem 8 (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16781/131072 : ℝ)) (496023002263/500000000000 : ℝ) (992046004529/1000000000000 : ℝ) (25075715277/50000000000 : ℝ) (501514305549/1000000000000 : ℝ) (99261630179/125000000000 : ℝ) (15881860829/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1051_exp_lower
  have heNumeric : (1027451127099/500000000000 : ℝ)/4 ≤ Real.exp (-3410258325349/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451127099/500000000000 : ℝ)/4 ≤ Real.exp ((67123/524288 : ℝ)-(15881860829/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67123/524288 : ℝ) (16781/131072 : ℝ) (15881860829/20000000000 : ℝ) (1027451127099/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1052; no trusted numerical premise.
theorem cover8_leaf1052_exp_radius : (31187547460562307/31250000000000000 : ℝ) ≤ Real.exp ((-67125/4194304 : ℝ)/8) ∧ Real.exp ((-67125/4194304 : ℝ)/8) ≤ (39920060749519753/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67125/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1052_exp_lower : (460056744271820063/500000000000000000 : ℝ) ≤ Real.exp ((-21314114415171/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314114415171/32000000000000 : ℝ)/8) ≤ (920113488543640127/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314114415171/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1052_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215695681/31250000000 : ℝ) ≤ 4*Real.exp (16781/131072 : ℝ)*Real.exp (-mu (radius 8 (67125/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (64215695681/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67125/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1052_exp_radius
  have hrNumeric : (246030883501/250000000000 : ℝ) ≤ Real.exp (-67125/4194304 : ℝ) ∧ Real.exp (-67125/4194304 : ℝ) ≤ (196824706801/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246030883501/250000000000 : ℝ) ≤ (radius 8 (67125/524288 : ℝ)) ∧ (radius 8 (67125/524288 : ℝ)) ≤ (196824706801/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67125/524288 : ℝ)) (246030883501/250000000000 : ℝ) (196824706801/200000000000 : ℝ) (177484843909/1000000000000 : ℝ) (35496968783/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67125/524288 : ℝ)) (246030883501/250000000000 : ℝ) (196824706801/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246030883501/250000000000 : ℝ) (196824706801/200000000000 : ℝ) (496030883501/500000000000 : ℝ) (992061767003/1000000000000 : ℝ) (248007501651/250000000000 : ℝ) (496015003303/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 1 (496030883501/500000000000 : ℝ) (992061767003/1000000000000 : ℝ) (248007501651/250000000000 : ℝ) (496015003303/500000000000 : ℝ) (992045886803/1000000000000 : ℝ) (198409177361/200000000000 : ℝ) (39681835467/40000000000 : ℝ) (496022943339/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 2 (992045886803/1000000000000 : ℝ) (198409177361/200000000000 : ℝ) (39681835467/40000000000 : ℝ) (496022943339/500000000000 : ℝ) (992045886739/1000000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 3 (992045886739/1000000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 4 (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 5 (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 6 (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67125/524288 : ℝ)) 7 (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67125/524288 : ℝ))) (177484843909/1000000000000 : ℝ) (35496968783/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177484843909/1000000000000 : ℝ) (35496968783/200000000000 : ℝ) (294371210977/500000000000 : ℝ) (294371210979/500000000000 : ℝ) (52661187663/125000000000 : ℝ) (3291324229/7812500000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 1 (294371210977/500000000000 : ℝ) (294371210979/500000000000 : ℝ) (52661187663/125000000000 : ℝ) (3291324229/7812500000 : ℝ) (505015961629/1000000000000 : ℝ) (101003192327/200000000000 : ℝ) (249013554521/500000000000 : ℝ) (9960542181/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 2 (505015961629/1000000000000 : ℝ) (101003192327/200000000000 : ℝ) (249013554521/500000000000 : ℝ) (9960542181/20000000000 : ℝ) (100304307067/200000000000 : ℝ) (501521535343/1000000000000 : ℝ) (250754680609/500000000000 : ℝ) (250754680613/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 3 (100304307067/200000000000 : ℝ) (501521535343/1000000000000 : ℝ) (250754680609/500000000000 : ℝ) (250754680613/500000000000 : ℝ) (125378862069/250000000000 : ℝ) (100303089657/200000000000 : ℝ) (501515448239/1000000000000 : ℝ) (62689431031/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 4 (125378862069/250000000000 : ℝ) (100303089657/200000000000 : ℝ) (501515448239/1000000000000 : ℝ) (62689431031/125000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 5 (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 6 (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67125/524288 : ℝ))) 7 (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67125/524288 : ℝ)) hmem 8 (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67125/524288 : ℝ))) hcmem 8 (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67125/524288 : ℝ)) (496022943369/500000000000 : ℝ) (496022943371/500000000000 : ℝ) (501515448257/1000000000000 : ℝ) (501515448267/1000000000000 : ℝ) (794094945083/1000000000000 : ℝ) (794094945103/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1052_exp_lower
  have heNumeric : (64215695681/31250000000 : ℝ)/4 ≤ Real.exp (-21314114415171/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215695681/31250000000 : ℝ)/4 ≤ Real.exp ((16781/131072 : ℝ)-(794094945103/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16781/131072 : ℝ) (67125/524288 : ℝ) (794094945103/1000000000000 : ℝ) (64215695681/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1053; no trusted numerical premise.
theorem cover8_leaf1053_exp_radius : (499000744497615631/500000000000000000 : ℝ) ≤ Real.exp ((-33563/2097152 : ℝ)/8) ∧ Real.exp ((-33563/2097152 : ℝ)/8) ≤ (998001488995231263/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33563/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1053_exp_lower : (184022697794175119/200000000000000000 : ℝ) ≤ Real.exp ((-85256457185211/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256457185211/128000000000000 : ℝ)/8) ≤ (230028372242718899/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256457185211/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1053_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451134713/500000000000 : ℝ) ≤ 4*Real.exp (67125/524288 : ℝ)*Real.exp (-mu (radius 8 (33563/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451134713/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33563/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1053_exp_radius
  have hrNumeric : (984123299371/1000000000000 : ℝ) ≤ Real.exp (-33563/2097152 : ℝ) ∧ Real.exp (-33563/2097152 : ℝ) ≤ (246030824843/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984123299371/1000000000000 : ℝ) ≤ (radius 8 (33563/262144 : ℝ)) ∧ (radius 8 (33563/262144 : ℝ)) ≤ (246030824843/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33563/262144 : ℝ)) (984123299371/1000000000000 : ℝ) (246030824843/250000000000 : ℝ) (22185768113/125000000000 : ℝ) (177486144911/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33563/262144 : ℝ)) (984123299371/1000000000000 : ℝ) (246030824843/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984123299371/1000000000000 : ℝ) (246030824843/250000000000 : ℝ) (198412329937/200000000000 : ℝ) (496030824843/500000000000 : ℝ) (198405977669/200000000000 : ℝ) (992029888347/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 1 (198412329937/200000000000 : ℝ) (496030824843/500000000000 : ℝ) (198405977669/200000000000 : ℝ) (992029888347/1000000000000 : ℝ) (198409153803/200000000000 : ℝ) (992045769017/1000000000000 : ℝ) (992045768887/1000000000000 : ℝ) (99204576889/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 2 (198409153803/200000000000 : ℝ) (992045769017/1000000000000 : ℝ) (992045768887/1000000000000 : ℝ) (99204576889/100000000000 : ℝ) (992045768951/1000000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 3 (992045768951/1000000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 4 (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 5 (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 6 (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33563/262144 : ℝ)) 7 (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33563/262144 : ℝ))) (22185768113/125000000000 : ℝ) (177486144911/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22185768113/125000000000 : ℝ) (177486144911/1000000000000 : ℝ) (147185768113/250000000000 : ℝ) (73592884057/125000000000 : ℝ) (105322761341/250000000000 : ℝ) (421291045373/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 1 (147185768113/250000000000 : ℝ) (73592884057/125000000000 : ℝ) (105322761341/250000000000 : ℝ) (421291045373/1000000000000 : ℝ) (126254264727/250000000000 : ℝ) (101003411783/200000000000 : ℝ) (49802829683/100000000000 : ℝ) (249014148419/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 2 (126254264727/250000000000 : ℝ) (101003411783/200000000000 : ℝ) (49802829683/100000000000 : ℝ) (249014148419/500000000000 : ℝ) (501522677869/1000000000000 : ℝ) (501522677877/1000000000000 : ℝ) (100302100819/200000000000 : ℝ) (501510504103/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 3 (501522677869/1000000000000 : ℝ) (501522677877/1000000000000 : ℝ) (100302100819/200000000000 : ℝ) (501510504103/1000000000000 : ℝ) (250758295491/500000000000 : ℝ) (50151659099/100000000000 : ℝ) (100303318189/200000000000 : ℝ) (250758295477/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 4 (250758295491/500000000000 : ℝ) (50151659099/100000000000 : ℝ) (100303318189/200000000000 : ℝ) (250758295477/500000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 5 (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 6 (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33563/262144 : ℝ))) 7 (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33563/262144 : ℝ)) hmem 8 (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33563/262144 : ℝ))) hcmem 8 (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33563/262144 : ℝ)) (19840915379/20000000000 : ℝ) (496022884477/500000000000 : ℝ) (501516590963/1000000000000 : ℝ) (125379147743/250000000000 : ℝ) (397048424359/500000000000 : ℝ) (794096848737/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1053_exp_lower
  have heNumeric : (1027451134713/500000000000 : ℝ)/4 ≤ Real.exp (-85256457185211/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451134713/500000000000 : ℝ)/4 ≤ Real.exp ((67125/524288 : ℝ)-(794096848737/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67125/524288 : ℝ) (33563/262144 : ℝ) (794096848737/1000000000000 : ℝ) (1027451134713/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1054; no trusted numerical premise.
theorem cover8_leaf1054_exp_radius : (998001459252469587/1000000000000000000 : ℝ) ≤ Real.exp ((-67127/4194304 : ℝ)/8) ∧ Real.exp ((-67127/4194304 : ℝ)/8) ≤ (249500364813117397/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67127/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1054_exp_lower : (920113489399376221/1000000000000000000 : ℝ) ≤ Real.exp ((-8525645670833/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525645670833/12800000000000 : ℝ)/8) ≤ (460056744699688111/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525645670833/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1054_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902277081/1000000000000 : ℝ) ≤ 4*Real.exp (33563/262144 : ℝ)*Real.exp (-mu (radius 8 (67127/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902277081/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67127/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1054_exp_radius
  have hrNumeric : (984123064737/1000000000000 : ℝ) ≤ Real.exp (-67127/4194304 : ℝ) ∧ Real.exp (-67127/4194304 : ℝ) ≤ (492061532369/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984123064737/1000000000000 : ℝ) ≤ (radius 8 (67127/524288 : ℝ)) ∧ (radius 8 (67127/524288 : ℝ)) ≤ (492061532369/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67127/524288 : ℝ)) (984123064737/1000000000000 : ℝ) (492061532369/500000000000 : ℝ) (22185930737/125000000000 : ℝ) (88743722951/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67127/524288 : ℝ)) (984123064737/1000000000000 : ℝ) (492061532369/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984123064737/1000000000000 : ℝ) (492061532369/500000000000 : ℝ) (62003845773/62500000000 : ℝ) (992061532369/1000000000000 : ℝ) (496014885043/500000000000 : ℝ) (992029770087/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 1 (62003845773/62500000000 : ℝ) (992061532369/1000000000000 : ℝ) (496014885043/500000000000 : ℝ) (992029770087/1000000000000 : ℝ) (992045651227/1000000000000 : ℝ) (248011412807/250000000000 : ℝ) (992045651099/1000000000000 : ℝ) (992045651101/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 2 (992045651227/1000000000000 : ℝ) (248011412807/250000000000 : ℝ) (992045651099/1000000000000 : ℝ) (992045651101/1000000000000 : ℝ) (992045651163/1000000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 3 (992045651163/1000000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 4 (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 5 (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 6 (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67127/524288 : ℝ)) 7 (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67127/524288 : ℝ))) (22185930737/125000000000 : ℝ) (88743722951/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22185930737/125000000000 : ℝ) (88743722951/500000000000 : ℝ) (147185930737/250000000000 : ℝ) (588743722951/1000000000000 : ℝ) (84258517883/200000000000 : ℝ) (421292589423/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 1 (147185930737/250000000000 : ℝ) (588743722951/1000000000000 : ℝ) (84258517883/200000000000 : ℝ) (421292589423/1000000000000 : ℝ) (505018156181/1000000000000 : ℝ) (505018156187/1000000000000 : ℝ) (498029484611/1000000000000 : ℝ) (249014742309/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 2 (505018156181/1000000000000 : ℝ) (505018156187/1000000000000 : ℝ) (498029484611/1000000000000 : ℝ) (249014742309/500000000000 : ℝ) (125380955099/250000000000 : ℝ) (501523820403/1000000000000 : ℝ) (100302329393/200000000000 : ℝ) (125377911743/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 3 (125380955099/250000000000 : ℝ) (501523820403/1000000000000 : ℝ) (100302329393/200000000000 : ℝ) (125377911743/250000000000 : ℝ) (6268971671/12500000000 : ℝ) (62689716711/125000000000 : ℝ) (501517733643/1000000000000 : ℝ) (501517733651/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 4 (6268971671/12500000000 : ℝ) (62689716711/125000000000 : ℝ) (501517733643/1000000000000 : ℝ) (501517733651/1000000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 5 (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 6 (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67127/524288 : ℝ))) 7 (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67127/524288 : ℝ)) hmem 8 (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67127/524288 : ℝ))) hcmem 8 (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67127/524288 : ℝ)) (496022825581/500000000000 : ℝ) (198409130233/200000000000 : ℝ) (501517733661/1000000000000 : ℝ) (50151773367/100000000000 : ℝ) (397049376171/500000000000 : ℝ) (19852468809/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1054_exp_lower
  have heNumeric : (2054902277081/1000000000000 : ℝ)/4 ≤ Real.exp (-8525645670833/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902277081/1000000000000 : ℝ)/4 ≤ Real.exp ((33563/262144 : ℝ)-(19852468809/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33563/262144 : ℝ) (67127/524288 : ℝ) (19852468809/25000000000 : ℝ) (2054902277081/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1055; no trusted numerical premise.
theorem cover8_leaf1055_exp_radius : (499000714754854399/500000000000000000 : ℝ) ≤ Real.exp ((-8391/524288 : ℝ)/8) ∧ Real.exp ((-8391/524288 : ℝ)/8) ≤ (998001429509708799/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8391/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1055_exp_lower : (92011348983098223/100000000000000000 : ℝ) ≤ Real.exp ((-85256456227993/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256456227993/128000000000000 : ℝ)/8) ≤ (920113489830982231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256456227993/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1055_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902284793/1000000000000 : ℝ) ≤ 4*Real.exp (67127/524288 : ℝ)*Real.exp (-mu (radius 8 (8391/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902284793/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8391/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1055_exp_radius
  have hrNumeric : (123015353763/125000000000 : ℝ) ≤ Real.exp (-8391/524288 : ℝ) ∧ Real.exp (-8391/524288 : ℝ) ≤ (196824566021/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123015353763/125000000000 : ℝ) ≤ (radius 8 (8391/65536 : ℝ)) ∧ (radius 8 (8391/65536 : ℝ)) ≤ (196824566021/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8391/65536 : ℝ)) (123015353763/125000000000 : ℝ) (196824566021/200000000000 : ℝ) (177488746871/1000000000000 : ℝ) (88744373439/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8391/65536 : ℝ)) (123015353763/125000000000 : ℝ) (196824566021/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123015353763/125000000000 : ℝ) (196824566021/200000000000 : ℝ) (248015353763/250000000000 : ℝ) (992061415053/1000000000000 : ℝ) (992029651827/1000000000000 : ℝ) (248007412957/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 1 (248015353763/250000000000 : ℝ) (992061415053/1000000000000 : ℝ) (992029651827/1000000000000 : ℝ) (248007412957/250000000000 : ℝ) (992045533439/1000000000000 : ℝ) (992045533441/1000000000000 : ℝ) (7750355729/7812500000 : ℝ) (496022766657/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 2 (992045533439/1000000000000 : ℝ) (992045533441/1000000000000 : ℝ) (7750355729/7812500000 : ℝ) (496022766657/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 3 (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 4 (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 5 (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 6 (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8391/65536 : ℝ)) 7 (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8391/65536 : ℝ))) (177488746871/1000000000000 : ℝ) (88744373439/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177488746871/1000000000000 : ℝ) (88744373439/500000000000 : ℝ) (117748874687/200000000000 : ℝ) (588744373439/1000000000000 : ℝ) (1316544167/3125000000 : ℝ) (421294133449/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 1 (117748874687/200000000000 : ℝ) (588744373439/1000000000000 : ℝ) (1316544167/3125000000 : ℝ) (421294133449/1000000000000 : ℝ) (505019253437/1000000000000 : ℝ) (126254813361/250000000000 : ℝ) (124507668093/250000000000 : ℝ) (24901533619/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 2 (505019253437/1000000000000 : ℝ) (126254813361/250000000000 : ℝ) (124507668093/250000000000 : ℝ) (24901533619/50000000000 : ℝ) (62690620363/125000000000 : ℝ) (15672655091/31250000000 : ℝ) (501512789817/1000000000000 : ℝ) (20060511593/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 3 (62690620363/125000000000 : ℝ) (15672655091/31250000000 : ℝ) (501512789817/1000000000000 : ℝ) (20060511593/40000000000 : ℝ) (12537971909/25000000000 : ℝ) (501518876369/1000000000000 : ℝ) (501518876323/1000000000000 : ℝ) (125379719083/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 4 (12537971909/25000000000 : ℝ) (501518876369/1000000000000 : ℝ) (501518876323/1000000000000 : ℝ) (125379719083/250000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 5 (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 6 (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8391/65536 : ℝ))) 7 (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8391/65536 : ℝ)) hmem 8 (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8391/65536 : ℝ))) hcmem 8 (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8391/65536 : ℝ)) (7936364267/8000000000 : ℝ) (496022766689/500000000000 : ℝ) (501518876341/1000000000000 : ℝ) (501518876351/1000000000000 : ℝ) (12407822749/15625000000 : ℝ) (198525163989/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1055_exp_lower
  have heNumeric : (2054902284793/1000000000000 : ℝ)/4 ≤ Real.exp (-85256456227993/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902284793/1000000000000 : ℝ)/4 ≤ Real.exp ((67127/524288 : ℝ)-(198525163989/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67127/524288 : ℝ) (8391/65536 : ℝ) (198525163989/250000000000 : ℝ) (2054902284793/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1056; no trusted numerical premise.
theorem cover8_leaf1056_exp_radius : (199600279953389779/200000000000000000 : ℝ) ≤ Real.exp ((-67129/4194304 : ℝ)/8) ∧ Real.exp ((-67129/4194304 : ℝ)/8) ≤ (31187543742717153/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67129/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1056_exp_lower : (184022698052931699/200000000000000000 : ℝ) ≤ Real.exp ((-10657056968169/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657056968169/16000000000000 : ℝ)/8) ≤ (14376773285385289/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657056968169/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1056_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902292541/1000000000000 : ℝ) ≤ 4*Real.exp (8391/65536 : ℝ)*Real.exp (-mu (radius 8 (67129/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902292541/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67129/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1056_exp_radius
  have hrNumeric : (984122595471/1000000000000 : ℝ) ≤ Real.exp (-67129/4194304 : ℝ) ∧ Real.exp (-67129/4194304 : ℝ) ≤ (61507662217/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984122595471/1000000000000 : ℝ) ≤ (radius 8 (67129/524288 : ℝ)) ∧ (radius 8 (67129/524288 : ℝ)) ≤ (61507662217/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67129/524288 : ℝ)) (984122595471/1000000000000 : ℝ) (61507662217/62500000000 : ℝ) (177490047837/1000000000000 : ℝ) (44372511961/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67129/524288 : ℝ)) (984122595471/1000000000000 : ℝ) (61507662217/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984122595471/1000000000000 : ℝ) (61507662217/62500000000 : ℝ) (198412259547/200000000000 : ℝ) (124007662217/125000000000 : ℝ) (992029533567/1000000000000 : ℝ) (992029533569/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 1 (198412259547/200000000000 : ℝ) (124007662217/125000000000 : ℝ) (992029533567/1000000000000 : ℝ) (992029533569/1000000000000 : ℝ) (992045415651/1000000000000 : ℝ) (992045415653/1000000000000 : ℝ) (992045415523/1000000000000 : ℝ) (496022707763/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 2 (992045415651/1000000000000 : ℝ) (992045415653/1000000000000 : ℝ) (992045415523/1000000000000 : ℝ) (496022707763/500000000000 : ℝ) (992045415587/1000000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 3 (992045415587/1000000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 4 (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 5 (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 6 (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67129/524288 : ℝ)) 7 (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67129/524288 : ℝ))) (177490047837/1000000000000 : ℝ) (44372511961/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177490047837/1000000000000 : ℝ) (44372511961/250000000000 : ℝ) (294372511959/500000000000 : ℝ) (294372511961/500000000000 : ℝ) (52661959681/125000000000 : ℝ) (210647838729/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 1 (294372511959/500000000000 : ℝ) (294372511961/500000000000 : ℝ) (52661959681/125000000000 : ℝ) (210647838729/500000000000 : ℝ) (505020350683/1000000000000 : ℝ) (50502035069/100000000000 : ℝ) (498031860121/1000000000000 : ℝ) (498031860129/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 2 (505020350683/1000000000000 : ℝ) (50502035069/100000000000 : ℝ) (498031860121/1000000000000 : ℝ) (498031860129/1000000000000 : ℝ) (250763052701/500000000000 : ℝ) (50152610541/100000000000 : ℝ) (501513932657/1000000000000 : ℝ) (250756966333/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 3 (250763052701/500000000000 : ℝ) (50152610541/100000000000 : ℝ) (501513932657/1000000000000 : ℝ) (250756966333/500000000000 : ℝ) (501520019029/1000000000000 : ℝ) (250760009519/500000000000 : ℝ) (31345001187/62500000000 : ℝ) (250760009501/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 4 (501520019029/1000000000000 : ℝ) (250760009519/500000000000 : ℝ) (31345001187/62500000000 : ℝ) (250760009501/500000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 5 (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 6 (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67129/524288 : ℝ))) 7 (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67129/524288 : ℝ)) hmem 8 (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67129/524288 : ℝ))) hcmem 8 (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67129/524288 : ℝ)) (496022707793/500000000000 : ℝ) (99204541559/100000000000 : ℝ) (50152001901/100000000000 : ℝ) (25076000951/50000000000 : ℝ) (397051279757/500000000000 : ℝ) (397051279767/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1056_exp_lower
  have heNumeric : (2054902292541/1000000000000 : ℝ)/4 ≤ Real.exp (-10657056968169/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902292541/1000000000000 : ℝ)/4 ≤ Real.exp ((8391/65536 : ℝ)-(397051279767/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8391/65536 : ℝ) (67129/524288 : ℝ) (397051279767/500000000000 : ℝ) (2054902292541/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1057; no trusted numerical premise.
theorem cover8_leaf1057_exp_radius : (998001370024189879/1000000000000000000 : ℝ) ≤ Real.exp ((-33565/2097152 : ℝ)/8) ∧ Real.exp ((-33565/2097152 : ℝ)/8) ≤ (24950034250604747/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33565/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1057_exp_lower : (920113490700520029/1000000000000000000 : ℝ) ≤ Real.exp ((-85256455260279/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256455260279/128000000000000 : ℝ)/8) ≤ (92011349070052003/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256455260279/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1057_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862787541/125000000000 : ℝ) ≤ 4*Real.exp (67129/524288 : ℝ)*Real.exp (-mu (radius 8 (33565/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862787541/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33565/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1057_exp_radius
  have hrNumeric : (492061180419/500000000000 : ℝ) ≤ Real.exp (-33565/2097152 : ℝ) ∧ Real.exp (-33565/2097152 : ℝ) ≤ (984122360839/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492061180419/500000000000 : ℝ) ≤ (radius 8 (33565/262144 : ℝ)) ∧ (radius 8 (33565/262144 : ℝ)) ≤ (984122360839/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33565/262144 : ℝ)) (492061180419/500000000000 : ℝ) (984122360839/1000000000000 : ℝ) (177491348793/1000000000000 : ℝ) (110932093/625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33565/262144 : ℝ)) (492061180419/500000000000 : ℝ) (984122360839/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492061180419/500000000000 : ℝ) (984122360839/1000000000000 : ℝ) (992061180419/1000000000000 : ℝ) (49603059021/50000000000 : ℝ) (248007353827/250000000000 : ℝ) (99202941531/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 1 (992061180419/1000000000000 : ℝ) (49603059021/50000000000 : ℝ) (248007353827/250000000000 : ℝ) (99202941531/100000000000 : ℝ) (992045297863/1000000000000 : ℝ) (198409059573/200000000000 : ℝ) (124005662217/125000000000 : ℝ) (496022648869/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 2 (992045297863/1000000000000 : ℝ) (198409059573/200000000000 : ℝ) (124005662217/125000000000 : ℝ) (496022648869/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 3 (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 4 (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 5 (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 6 (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33565/262144 : ℝ)) 7 (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33565/262144 : ℝ))) (177491348793/1000000000000 : ℝ) (110932093/625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177491348793/1000000000000 : ℝ) (110932093/625000000 : ℝ) (147186418599/250000000000 : ℝ) (735932093/1250000000 : ℝ) (421297221439/1000000000000 : ℝ) (421297221449/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 1 (147186418599/250000000000 : ℝ) (735932093/1250000000 : ℝ) (421297221439/1000000000000 : ℝ) (421297221449/1000000000000 : ℝ) (505021447917/1000000000000 : ℝ) (20200857917/40000000000 : ℝ) (31127065491/62500000000 : ℝ) (99606609573/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 2 (505021447917/1000000000000 : ℝ) (20200857917/40000000000 : ℝ) (31127065491/62500000000 : ℝ) (99606609573/200000000000 : ℝ) (250763623943/500000000000 : ℝ) (100305449579/200000000000 : ℝ) (100303015097/200000000000 : ℝ) (250757537747/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 3 (250763623943/500000000000 : ℝ) (100305449579/200000000000 : ℝ) (100303015097/200000000000 : ℝ) (250757537747/500000000000 : ℝ) (100304232337/200000000000 : ℝ) (100304232339/200000000000 : ℝ) (31345072603/62500000000 : ℝ) (250760580829/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 4 (100304232337/200000000000 : ℝ) (100304232339/200000000000 : ℝ) (31345072603/62500000000 : ℝ) (250760580829/500000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 5 (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 6 (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33565/262144 : ℝ))) 7 (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33565/262144 : ℝ)) hmem 8 (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33565/262144 : ℝ))) hcmem 8 (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33565/262144 : ℝ)) (992045297799/1000000000000 : ℝ) (496022648901/500000000000 : ℝ) (250760580833/500000000000 : ℝ) (501521161677/1000000000000 : ℝ) (24815764471/31250000000 : ℝ) (794104463093/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1057_exp_lower
  have heNumeric : (256862787541/125000000000 : ℝ)/4 ≤ Real.exp (-85256455260279/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862787541/125000000000 : ℝ)/4 ≤ Real.exp ((67129/524288 : ℝ)-(794104463093/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67129/524288 : ℝ) (33565/262144 : ℝ) (794104463093/1000000000000 : ℝ) (256862787541/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1058; no trusted numerical premise.
theorem cover8_leaf1058_exp_radius : (3992005361125727/4000000000000000 : ℝ) ≤ Real.exp ((-67131/4194304 : ℝ)/8) ∧ Real.exp ((-67131/4194304 : ℝ)/8) ≤ (998001340281431751/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67131/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1058_exp_lower : (920113491138681847/1000000000000000000 : ℝ) ≤ Real.exp ((-42628227386323/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628227386323/64000000000000 : ℝ)/8) ≤ (115014186392335231/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628227386323/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1058_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902308157/1000000000000 : ℝ) ≤ 4*Real.exp (33565/262144 : ℝ)*Real.exp (-mu (radius 8 (67131/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902308157/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67131/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1058_exp_radius
  have hrNumeric : (196824425241/200000000000 : ℝ) ≤ Real.exp (-67131/4194304 : ℝ) ∧ Real.exp (-67131/4194304 : ℝ) ≤ (492061063103/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196824425241/200000000000 : ℝ) ≤ (radius 8 (67131/524288 : ℝ)) ∧ (radius 8 (67131/524288 : ℝ)) ≤ (492061063103/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67131/524288 : ℝ)) (196824425241/200000000000 : ℝ) (492061063103/500000000000 : ℝ) (8874632487/50000000000 : ℝ) (88746324873/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67131/524288 : ℝ)) (196824425241/200000000000 : ℝ) (492061063103/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196824425241/200000000000 : ℝ) (492061063103/500000000000 : ℝ) (496030531551/500000000000 : ℝ) (992061063103/1000000000000 : ℝ) (992029297049/1000000000000 : ℝ) (992029297051/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 1 (496030531551/500000000000 : ℝ) (992061063103/1000000000000 : ℝ) (992029297049/1000000000000 : ℝ) (992029297051/1000000000000 : ℝ) (39681807203/40000000000 : ℝ) (992045180077/1000000000000 : ℝ) (248011294987/250000000000 : ℝ) (19840903599/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 2 (39681807203/40000000000 : ℝ) (992045180077/1000000000000 : ℝ) (248011294987/250000000000 : ℝ) (19840903599/20000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 3 (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 4 (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 5 (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 6 (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67131/524288 : ℝ)) 7 (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67131/524288 : ℝ))) (8874632487/50000000000 : ℝ) (88746324873/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8874632487/50000000000 : ℝ) (88746324873/500000000000 : ℝ) (58874632487/100000000000 : ℝ) (588746324873/1000000000000 : ℝ) (210649382707/500000000000 : ℝ) (210649382711/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 1 (58874632487/100000000000 : ℝ) (588746324873/1000000000000 : ℝ) (210649382707/500000000000 : ℝ) (210649382711/500000000000 : ℝ) (252511272571/500000000000 : ℝ) (126255636287/250000000000 : ℝ) (24901711779/50000000000 : ℝ) (498034235587/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 2 (252511272571/500000000000 : ℝ) (126255636287/250000000000 : ℝ) (24901711779/50000000000 : ℝ) (498034235587/1000000000000 : ℝ) (501528390361/1000000000000 : ℝ) (15672762199/31250000000 : ℝ) (250758109151/500000000000 : ℝ) (50151621831/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 3 (501528390361/1000000000000 : ℝ) (15672762199/31250000000 : ℝ) (250758109151/500000000000 : ℝ) (50151621831/100000000000 : ℝ) (501522304331/1000000000000 : ℝ) (501522304339/1000000000000 : ℝ) (250761152147/500000000000 : ℝ) (501522304303/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 4 (501522304331/1000000000000 : ℝ) (501522304339/1000000000000 : ℝ) (250761152147/500000000000 : ℝ) (501522304303/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 5 (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 6 (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67131/524288 : ℝ))) 7 (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67131/524288 : ℝ)) hmem 8 (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67131/524288 : ℝ))) hcmem 8 (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67131/524288 : ℝ)) (992045180011/1000000000000 : ℝ) (496022590007/500000000000 : ℝ) (62690288039/125000000000 : ℝ) (501522304321/1000000000000 : ℝ) (158821273323/200000000000 : ℝ) (99263295829/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1058_exp_lower
  have heNumeric : (2054902308157/1000000000000 : ℝ)/4 ≤ Real.exp (-42628227386323/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902308157/1000000000000 : ℝ)/4 ≤ Real.exp ((33565/262144 : ℝ)-(99263295829/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33565/262144 : ℝ) (67131/524288 : ℝ) (99263295829/125000000000 : ℝ) (2054902308157/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1059; no trusted numerical premise.
theorem cover8_leaf1059_exp_radius : (998001310538674507/1000000000000000000 : ℝ) ≤ Real.exp ((-16783/1048576 : ℝ)/8) ∧ Real.exp ((-16783/1048576 : ℝ)/8) ≤ (249500327634668627/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16783/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1059_exp_lower : (920113491578683893/1000000000000000000 : ℝ) ≤ Real.exp ((-17051290856593/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051290856593/25600000000000 : ℝ)/8) ≤ (460056745789341947/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051290856593/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1059_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451158009/500000000000 : ℝ) ≤ 4*Real.exp (67131/524288 : ℝ)*Real.exp (-mu (radius 8 (16783/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451158009/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16783/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1059_exp_radius
  have hrNumeric : (246030472893/250000000000 : ℝ) ≤ Real.exp (-16783/1048576 : ℝ) ∧ Real.exp (-16783/1048576 : ℝ) ≤ (984121891573/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246030472893/250000000000 : ℝ) ≤ (radius 8 (16783/131072 : ℝ)) ∧ (radius 8 (16783/131072 : ℝ)) ≤ (984121891573/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16783/131072 : ℝ)) (246030472893/250000000000 : ℝ) (984121891573/1000000000000 : ℝ) (44373487669/250000000000 : ℝ) (177493950683/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16783/131072 : ℝ)) (246030472893/250000000000 : ℝ) (984121891573/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246030472893/250000000000 : ℝ) (984121891573/1000000000000 : ℝ) (496030472893/500000000000 : ℝ) (992060945787/1000000000000 : ℝ) (99202917879/100000000000 : ℝ) (124003647349/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 1 (496030472893/500000000000 : ℝ) (992060945787/1000000000000 : ℝ) (99202917879/100000000000 : ℝ) (124003647349/125000000000 : ℝ) (62002816393/62500000000 : ℝ) (99204506229/100000000000 : ℝ) (12400563277/12500000000 : ℝ) (992045062163/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 2 (62002816393/62500000000 : ℝ) (99204506229/100000000000 : ℝ) (12400563277/12500000000 : ℝ) (992045062163/1000000000000 : ℝ) (62002816389/62500000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 3 (62002816389/62500000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 4 (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 5 (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 6 (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16783/131072 : ℝ)) 7 (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16783/131072 : ℝ))) (44373487669/250000000000 : ℝ) (177493950683/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44373487669/250000000000 : ℝ) (177493950683/1000000000000 : ℝ) (294373487669/500000000000 : ℝ) (294373487671/500000000000 : ℝ) (42130030937/100000000000 : ℝ) (21065015469/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 1 (294373487669/500000000000 : ℝ) (294373487671/500000000000 : ℝ) (42130030937/100000000000 : ℝ) (21065015469/50000000000 : ℝ) (252511821177/500000000000 : ℝ) (505023642361/1000000000000 : ℝ) (62254427911/125000000000 : ℝ) (498035423297/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 2 (252511821177/500000000000 : ℝ) (505023642361/1000000000000 : ℝ) (62254427911/125000000000 : ℝ) (498035423297/1000000000000 : ℝ) (501529532821/1000000000000 : ℝ) (501529532829/1000000000000 : ℝ) (100303472221/200000000000 : ℝ) (250758680557/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 3 (501529532821/1000000000000 : ℝ) (501529532829/1000000000000 : ℝ) (100303472221/200000000000 : ℝ) (250758680557/500000000000 : ℝ) (501523446963/1000000000000 : ℝ) (125380861743/250000000000 : ℝ) (250761723463/500000000000 : ℝ) (100304689387/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 4 (501523446963/1000000000000 : ℝ) (125380861743/250000000000 : ℝ) (250761723463/500000000000 : ℝ) (100304689387/200000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 5 (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 6 (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16783/131072 : ℝ))) 7 (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16783/131072 : ℝ)) hmem 8 (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16783/131072 : ℝ))) hcmem 8 (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16783/131072 : ℝ)) (992045062223/1000000000000 : ℝ) (992045062227/1000000000000 : ℝ) (15672607717/31250000000 : ℝ) (250761723477/500000000000 : ℝ) (158821654027/200000000000 : ℝ) (158821654031/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1059_exp_lower
  have heNumeric : (1027451158009/500000000000 : ℝ)/4 ≤ Real.exp (-17051290856593/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451158009/500000000000 : ℝ)/4 ≤ Real.exp ((67131/524288 : ℝ)-(158821654031/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67131/524288 : ℝ) (16783/131072 : ℝ) (158821654031/200000000000 : ℝ) (1027451158009/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1060; no trusted numerical premise.
theorem cover8_leaf1060_exp_radius : (19960025615918363/20000000000000000 : ℝ) ≤ Real.exp ((-67133/4194304 : ℝ)/8) ∧ Real.exp ((-67133/4194304 : ℝ)/8) ≤ (998001280795918151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67133/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1060_exp_lower : (184022698404266253/200000000000000000 : ℝ) ≤ Real.exp ((-4262822689517/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262822689517/6400000000000 : ℝ)/8) ≤ (460056746010665633/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262822689517/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1060_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902323927/1000000000000 : ℝ) ≤ 4*Real.exp (16783/131072 : ℝ)*Real.exp (-mu (radius 8 (67133/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902323927/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67133/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1060_exp_radius
  have hrNumeric : (984121656939/1000000000000 : ℝ) ≤ Real.exp (-67133/4194304 : ℝ) ∧ Real.exp (-67133/4194304 : ℝ) ≤ (49206082847/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984121656939/1000000000000 : ℝ) ≤ (radius 8 (67133/524288 : ℝ)) ∧ (radius 8 (67133/524288 : ℝ)) ≤ (49206082847/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67133/524288 : ℝ)) (984121656939/1000000000000 : ℝ) (49206082847/50000000000 : ℝ) (177495251603/1000000000000 : ℝ) (177495251609/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67133/524288 : ℝ)) (984121656939/1000000000000 : ℝ) (49206082847/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984121656939/1000000000000 : ℝ) (49206082847/50000000000 : ℝ) (992060828469/1000000000000 : ℝ) (99206082847/100000000000 : ℝ) (992029060531/1000000000000 : ℝ) (248007265133/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 1 (992060828469/1000000000000 : ℝ) (99206082847/100000000000 : ℝ) (992029060531/1000000000000 : ℝ) (248007265133/250000000000 : ℝ) (1984089889/2000000000 : ℝ) (992044944501/1000000000000 : ℝ) (248011236093/250000000000 : ℝ) (496022472187/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 2 (1984089889/2000000000 : ℝ) (992044944501/1000000000000 : ℝ) (248011236093/250000000000 : ℝ) (496022472187/500000000000 : ℝ) (248011236109/250000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 3 (248011236109/250000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 4 (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 5 (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 6 (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67133/524288 : ℝ)) 7 (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67133/524288 : ℝ))) (177495251603/1000000000000 : ℝ) (177495251609/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177495251603/1000000000000 : ℝ) (177495251609/1000000000000 : ℝ) (588747625801/1000000000000 : ℝ) (117749525161/200000000000 : ℝ) (42130185331/100000000000 : ℝ) (210650926659/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 1 (588747625801/1000000000000 : ℝ) (117749525161/200000000000 : ℝ) (42130185331/100000000000 : ℝ) (210650926659/500000000000 : ℝ) (101004947911/200000000000 : ℝ) (252512369781/500000000000 : ℝ) (99607322197/200000000000 : ℝ) (31127288187/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 2 (101004947911/200000000000 : ℝ) (252512369781/500000000000 : ℝ) (99607322197/200000000000 : ℝ) (31127288187/62500000000 : ℝ) (50153067527/100000000000 : ℝ) (501530675277/1000000000000 : ℝ) (501518503897/1000000000000 : ℝ) (100303700781/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 3 (50153067527/100000000000 : ℝ) (501530675277/1000000000000 : ℝ) (501518503897/1000000000000 : ℝ) (100303700781/200000000000 : ℝ) (501524589583/1000000000000 : ℝ) (501524589591/1000000000000 : ℝ) (250762294773/500000000000 : ℝ) (100304917911/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 4 (501524589583/1000000000000 : ℝ) (501524589591/1000000000000 : ℝ) (250762294773/500000000000 : ℝ) (100304917911/200000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 5 (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 6 (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67133/524288 : ℝ))) 7 (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67133/524288 : ℝ)) hmem 8 (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67133/524288 : ℝ))) hcmem 8 (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67133/524288 : ℝ)) (198408988887/200000000000 : ℝ) (496022472219/500000000000 : ℝ) (125381147391/250000000000 : ℝ) (501524589573/1000000000000 : ℝ) (397055086819/500000000000 : ℝ) (158822034731/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1060_exp_lower
  have heNumeric : (2054902323927/1000000000000 : ℝ)/4 ≤ Real.exp (-4262822689517/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902323927/1000000000000 : ℝ)/4 ≤ Real.exp ((16783/131072 : ℝ)-(158822034731/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16783/131072 : ℝ) (67133/524288 : ℝ) (158822034731/200000000000 : ℝ) (2054902323927/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1061; no trusted numerical premise.
theorem cover8_leaf1061_exp_radius : (998001251053162679/1000000000000000000 : ℝ) ≤ Real.exp ((-33567/2097152 : ℝ)/8) ∧ Real.exp ((-33567/2097152 : ℝ)/8) ≤ (24950031276329067/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33567/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1061_exp_lower : (18402269849314077/20000000000000000 : ℝ) ≤ Real.exp ((-17051290659159/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051290659159/25600000000000 : ℝ)/8) ≤ (920113492465703851/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051290659159/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1061_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451165933/500000000000 : ℝ) ≤ 4*Real.exp (67133/524288 : ℝ)*Real.exp (-mu (radius 8 (33567/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451165933/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33567/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1061_exp_radius
  have hrNumeric : (492060711153/500000000000 : ℝ) ≤ Real.exp (-33567/2097152 : ℝ) ∧ Real.exp (-33567/2097152 : ℝ) ≤ (984121422307/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492060711153/500000000000 : ℝ) ≤ (radius 8 (33567/262144 : ℝ)) ∧ (radius 8 (33567/262144 : ℝ)) ≤ (984121422307/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33567/262144 : ℝ)) (492060711153/500000000000 : ℝ) (984121422307/1000000000000 : ℝ) (177496552519/1000000000000 : ℝ) (88748276263/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33567/262144 : ℝ)) (492060711153/500000000000 : ℝ) (984121422307/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492060711153/500000000000 : ℝ) (984121422307/1000000000000 : ℝ) (992060711153/1000000000000 : ℝ) (496030355577/500000000000 : ℝ) (15500452223/15625000000 : ℝ) (992028942273/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 1 (992060711153/1000000000000 : ℝ) (496030355577/500000000000 : ℝ) (15500452223/15625000000 : ℝ) (992028942273/1000000000000 : ℝ) (124005603339/125000000000 : ℝ) (496022413357/500000000000 : ℝ) (198408965317/200000000000 : ℝ) (992044826587/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 2 (124005603339/125000000000 : ℝ) (496022413357/500000000000 : ℝ) (198408965317/200000000000 : ℝ) (992044826587/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 3 (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 4 (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 5 (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 6 (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33567/262144 : ℝ)) 7 (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33567/262144 : ℝ))) (177496552519/1000000000000 : ℝ) (88748276263/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177496552519/1000000000000 : ℝ) (88748276263/500000000000 : ℝ) (588748276259/1000000000000 : ℝ) (588748276263/1000000000000 : ℝ) (421303397231/1000000000000 : ℝ) (421303397241/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 1 (588748276259/1000000000000 : ℝ) (588748276263/1000000000000 : ℝ) (421303397231/1000000000000 : ℝ) (421303397241/1000000000000 : ℝ) (101005167349/200000000000 : ℝ) (31564114797/62500000000 : ℝ) (498037798667/1000000000000 : ℝ) (124509449669/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 2 (101005167349/200000000000 : ℝ) (31564114797/62500000000 : ℝ) (498037798667/1000000000000 : ℝ) (124509449669/250000000000 : ℝ) (250765908853/500000000000 : ℝ) (250765908857/500000000000 : ℝ) (125379911669/250000000000 : ℝ) (100303929337/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 3 (250765908853/500000000000 : ℝ) (250765908857/500000000000 : ℝ) (125379911669/250000000000 : ℝ) (100303929337/200000000000 : ℝ) (501525732191/1000000000000 : ℝ) (2507628661/5000000000 : ℝ) (250762866077/500000000000 : ℝ) (501525732163/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 4 (501525732191/1000000000000 : ℝ) (2507628661/5000000000 : ℝ) (250762866077/500000000000 : ℝ) (501525732163/1000000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 5 (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 6 (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33567/262144 : ℝ))) 7 (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33567/262144 : ℝ)) hmem 8 (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33567/262144 : ℝ))) hcmem 8 (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33567/262144 : ℝ)) (124005603331/125000000000 : ℝ) (992044826651/1000000000000 : ℝ) (125381433043/250000000000 : ℝ) (250762866091/500000000000 : ℝ) (2481600241/3125000000 : ℝ) (39705603857/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1061_exp_lower
  have heNumeric : (1027451165933/500000000000 : ℝ)/4 ≤ Real.exp (-17051290659159/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451165933/500000000000 : ℝ)/4 ≤ Real.exp ((67133/524288 : ℝ)-(39705603857/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67133/524288 : ℝ) (33567/262144 : ℝ) (39705603857/50000000000 : ℝ) (1027451165933/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1062; no trusted numerical premise.
theorem cover8_leaf1062_exp_radius : (199600244262081619/200000000000000000 : ℝ) ≤ Real.exp ((-67135/4194304 : ℝ)/8) ∧ Real.exp ((-67135/4194304 : ℝ)/8) ≤ (31187538165950253/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67135/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1062_exp_lower : (920113492912376719/1000000000000000000 : ℝ) ≤ Real.exp ((-8525645279869/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525645279869/12800000000000 : ℝ)/8) ≤ (11501418661404709/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525645279869/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1062_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451169923/500000000000 : ℝ) ≤ 4*Real.exp (33567/262144 : ℝ)*Real.exp (-mu (radius 8 (67135/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451169923/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67135/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1062_exp_radius
  have hrNumeric : (984121187673/1000000000000 : ℝ) ≤ Real.exp (-67135/4194304 : ℝ) ∧ Real.exp (-67135/4194304 : ℝ) ≤ (492060593837/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984121187673/1000000000000 : ℝ) ≤ (radius 8 (67135/524288 : ℝ)) ∧ (radius 8 (67135/524288 : ℝ)) ≤ (492060593837/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67135/524288 : ℝ)) (984121187673/1000000000000 : ℝ) (492060593837/500000000000 : ℝ) (88748926713/500000000000 : ℝ) (177497853433/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67135/524288 : ℝ)) (984121187673/1000000000000 : ℝ) (492060593837/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984121187673/1000000000000 : ℝ) (492060593837/500000000000 : ℝ) (248015148459/250000000000 : ℝ) (992060593837/1000000000000 : ℝ) (992028824013/1000000000000 : ℝ) (496014412007/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 1 (248015148459/250000000000 : ℝ) (992060593837/1000000000000 : ℝ) (992028824013/1000000000000 : ℝ) (496014412007/500000000000 : ℝ) (248011177231/250000000000 : ℝ) (496022354463/500000000000 : ℝ) (992044708797/1000000000000 : ℝ) (992044708799/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 2 (248011177231/250000000000 : ℝ) (496022354463/500000000000 : ℝ) (992044708797/1000000000000 : ℝ) (992044708799/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 3 (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 4 (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 5 (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 6 (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67135/524288 : ℝ)) 7 (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67135/524288 : ℝ))) (88748926713/500000000000 : ℝ) (177497853433/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88748926713/500000000000 : ℝ) (177497853433/1000000000000 : ℝ) (588748926713/1000000000000 : ℝ) (588748926717/1000000000000 : ℝ) (26331558821/62500000000 : ℝ) (84260988229/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 1 (588748926713/1000000000000 : ℝ) (588748926717/1000000000000 : ℝ) (26331558821/62500000000 : ℝ) (84260988229/200000000000 : ℝ) (126256733481/250000000000 : ℝ) (505026933931/1000000000000 : ℝ) (249019493169/500000000000 : ℝ) (249019493173/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 2 (126256733481/250000000000 : ℝ) (505026933931/1000000000000 : ℝ) (249019493169/500000000000 : ℝ) (249019493173/500000000000 : ℝ) (501532960131/1000000000000 : ℝ) (501532960139/1000000000000 : ℝ) (125380197361/250000000000 : ℝ) (125380197363/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 3 (501532960131/1000000000000 : ℝ) (501532960139/1000000000000 : ℝ) (125380197361/250000000000 : ℝ) (125380197363/250000000000 : ℝ) (501526874787/1000000000000 : ℝ) (125381718699/250000000000 : ℝ) (2006107499/4000000000 : ℝ) (501526874759/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 4 (501526874787/1000000000000 : ℝ) (125381718699/250000000000 : ℝ) (2006107499/4000000000 : ℝ) (501526874759/1000000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 5 (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 6 (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67135/524288 : ℝ))) 7 (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67135/524288 : ℝ)) hmem 8 (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67135/524288 : ℝ))) hcmem 8 (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67135/524288 : ℝ)) (49602235443/50000000000 : ℝ) (992044708863/1000000000000 : ℝ) (31345429673/62500000000 : ℝ) (250763437389/500000000000 : ℝ) (397056990293/500000000000 : ℝ) (158822796121/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1062_exp_lower
  have heNumeric : (1027451169923/500000000000 : ℝ)/4 ≤ Real.exp (-8525645279869/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451169923/500000000000 : ℝ)/4 ≤ Real.exp ((33567/262144 : ℝ)-(158822796121/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33567/262144 : ℝ) (67135/524288 : ℝ) (158822796121/200000000000 : ℝ) (1027451169923/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1063; no trusted numerical premise.
theorem cover8_leaf1063_exp_radius : (499000595783827199/500000000000000000 : ℝ) ≤ Real.exp ((-1049/65536 : ℝ)/8) ∧ Real.exp ((-1049/65536 : ℝ)/8) ≤ (998001191567654399/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1049/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1063_exp_lower : (184022698672453997/200000000000000000 : ℝ) ≤ Real.exp ((-85256452298001/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256452298001/128000000000000 : ℝ)/8) ≤ (460056746681134993/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256452298001/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1063_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980469577/200000000000 : ℝ) ≤ 4*Real.exp (67135/524288 : ℝ)*Real.exp (-mu (radius 8 (1049/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410980469577/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1049/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1063_exp_radius
  have hrNumeric : (984120953041/1000000000000 : ℝ) ≤ Real.exp (-1049/65536 : ℝ) ∧ Real.exp (-1049/65536 : ℝ) ≤ (492060476521/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984120953041/1000000000000 : ℝ) ≤ (radius 8 (1049/8192 : ℝ)) ∧ (radius 8 (1049/8192 : ℝ)) ≤ (492060476521/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1049/8192 : ℝ)) (984120953041/1000000000000 : ℝ) (492060476521/500000000000 : ℝ) (88749577159/500000000000 : ℝ) (44374788581/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1049/8192 : ℝ)) (984120953041/1000000000000 : ℝ) (492060476521/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984120953041/1000000000000 : ℝ) (492060476521/500000000000 : ℝ) (24801511913/25000000000 : ℝ) (992060476521/1000000000000 : ℝ) (496014352877/500000000000 : ℝ) (248007176439/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 1 (24801511913/25000000000 : ℝ) (992060476521/1000000000000 : ℝ) (496014352877/500000000000 : ℝ) (248007176439/250000000000 : ℝ) (992044591137/1000000000000 : ℝ) (992044591139/1000000000000 : ℝ) (992044591009/1000000000000 : ℝ) (248011147753/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 2 (992044591137/1000000000000 : ℝ) (992044591139/1000000000000 : ℝ) (992044591009/1000000000000 : ℝ) (248011147753/250000000000 : ℝ) (992044591073/1000000000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 3 (992044591073/1000000000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 4 (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 5 (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 6 (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1049/8192 : ℝ)) 7 (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1049/8192 : ℝ))) (88749577159/500000000000 : ℝ) (44374788581/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88749577159/500000000000 : ℝ) (44374788581/250000000000 : ℝ) (588749577159/1000000000000 : ℝ) (294374788581/500000000000 : ℝ) (421306485017/1000000000000 : ℝ) (16852259401/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 1 (588749577159/1000000000000 : ℝ) (294374788581/500000000000 : ℝ) (421306485017/1000000000000 : ℝ) (16852259401/40000000000 : ℝ) (31564251943/62500000000 : ℝ) (252514015547/500000000000 : ℝ) (49804017399/100000000000 : ℝ) (498040173997/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 2 (31564251943/62500000000 : ℝ) (252514015547/500000000000 : ℝ) (49804017399/100000000000 : ℝ) (498040173997/1000000000000 : ℝ) (501534102539/1000000000000 : ℝ) (250767051273/500000000000 : ℝ) (100304386439/200000000000 : ℝ) (250760966101/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 3 (501534102539/1000000000000 : ℝ) (250767051273/500000000000 : ℝ) (100304386439/200000000000 : ℝ) (250760966101/500000000000 : ℝ) (501528017367/1000000000000 : ℝ) (250764008687/500000000000 : ℝ) (50152801733/100000000000 : ℝ) (250764008669/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 4 (501528017367/1000000000000 : ℝ) (250764008687/500000000000 : ℝ) (50152801733/100000000000 : ℝ) (250764008669/500000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 5 (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 6 (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1049/8192 : ℝ))) 7 (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1049/8192 : ℝ)) hmem 8 (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1049/8192 : ℝ))) hcmem 8 (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1049/8192 : ℝ)) (31001393471/31250000000 : ℝ) (248011147769/250000000000 : ℝ) (125382004337/250000000000 : ℝ) (125382004339/250000000000 : ℝ) (31764635361/40000000000 : ℝ) (397057942021/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1063_exp_lower
  have heNumeric : (410980469577/200000000000 : ℝ)/4 ≤ Real.exp (-85256452298001/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980469577/200000000000 : ℝ)/4 ≤ Real.exp ((67135/524288 : ℝ)-(397057942021/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67135/524288 : ℝ) (1049/8192 : ℝ) (397057942021/500000000000 : ℝ) (410980469577/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1064; no trusted numerical premise.
theorem cover8_leaf1064_exp_radius : (499000580912450793/500000000000000000 : ℝ) ≤ Real.exp ((-67137/4194304 : ℝ)/8) ∧ Real.exp ((-67137/4194304 : ℝ)/8) ≤ (998001161824901587/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67137/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1064_exp_lower : (920113493813313393/1000000000000000000 : ℝ) ≤ Real.exp ((-1332132059313/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332132059313/2000000000000 : ℝ)/8) ≤ (460056746906656697/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332132059313/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1064_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902355943/1000000000000 : ℝ) ≤ 4*Real.exp (1049/8192 : ℝ)*Real.exp (-mu (radius 8 (67137/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902355943/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67137/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1064_exp_radius
  have hrNumeric : (123015089801/125000000000 : ℝ) ≤ Real.exp (-67137/4194304 : ℝ) ∧ Real.exp (-67137/4194304 : ℝ) ≤ (984120718409/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123015089801/125000000000 : ℝ) ≤ (radius 8 (67137/524288 : ℝ)) ∧ (radius 8 (67137/524288 : ℝ)) ≤ (984120718409/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67137/524288 : ℝ)) (123015089801/125000000000 : ℝ) (984120718409/1000000000000 : ℝ) (35500091041/200000000000 : ℝ) (44375113803/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67137/524288 : ℝ)) (123015089801/125000000000 : ℝ) (984120718409/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123015089801/125000000000 : ℝ) (984120718409/1000000000000 : ℝ) (248015089801/250000000000 : ℝ) (198412071841/200000000000 : ℝ) (198405717499/200000000000 : ℝ) (124003573437/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 1 (248015089801/250000000000 : ℝ) (198412071841/200000000000 : ℝ) (198405717499/200000000000 : ℝ) (124003573437/125000000000 : ℝ) (992044473349/1000000000000 : ℝ) (992044473351/1000000000000 : ℝ) (496022236611/500000000000 : ℝ) (124005559153/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 2 (992044473349/1000000000000 : ℝ) (992044473351/1000000000000 : ℝ) (496022236611/500000000000 : ℝ) (124005559153/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 3 (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 4 (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 5 (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 6 (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67137/524288 : ℝ)) 7 (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67137/524288 : ℝ))) (35500091041/200000000000 : ℝ) (44375113803/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35500091041/200000000000 : ℝ) (44375113803/250000000000 : ℝ) (294375113801/500000000000 : ℝ) (294375113803/500000000000 : ℝ) (421308028887/1000000000000 : ℝ) (13165875903/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 1 (294375113801/500000000000 : ℝ) (294375113803/500000000000 : ℝ) (421308028887/1000000000000 : ℝ) (13165875903/31250000000 : ℝ) (126257282061/250000000000 : ℝ) (505029128251/1000000000000 : ℝ) (498041361633/1000000000000 : ℝ) (498041361641/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 2 (126257282061/250000000000 : ℝ) (505029128251/1000000000000 : ℝ) (498041361633/1000000000000 : ℝ) (498041361641/1000000000000 : ℝ) (250767622469/500000000000 : ℝ) (250767622473/500000000000 : ℝ) (501523074937/1000000000000 : ℝ) (250761537473/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 3 (250767622469/500000000000 : ℝ) (250767622473/500000000000 : ℝ) (501523074937/1000000000000 : ℝ) (250761537473/500000000000 : ℝ) (501529159937/1000000000000 : ℝ) (250764579973/500000000000 : ℝ) (5015291599/10000000000 : ℝ) (50152915991/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 4 (501529159937/1000000000000 : ℝ) (250764579973/500000000000 : ℝ) (5015291599/10000000000 : ℝ) (50152915991/100000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 5 (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 6 (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67137/524288 : ℝ))) 7 (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67137/524288 : ℝ)) hmem 8 (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67137/524288 : ℝ))) hcmem 8 (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67137/524288 : ℝ)) (198408894657/200000000000 : ℝ) (124005559161/125000000000 : ℝ) (250764579959/500000000000 : ℝ) (62691144991/125000000000 : ℝ) (15882355749/20000000000 : ℝ) (794117787469/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1064_exp_lower
  have heNumeric : (2054902355943/1000000000000 : ℝ)/4 ≤ Real.exp (-1332132059313/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902355943/1000000000000 : ℝ)/4 ≤ Real.exp ((1049/8192 : ℝ)-(794117787469/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1049/8192 : ℝ) (67137/524288 : ℝ) (794117787469/1000000000000 : ℝ) (2054902355943/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1065; no trusted numerical premise.
theorem cover8_leaf1065_exp_radius : (499000566041074831/500000000000000000 : ℝ) ≤ Real.exp ((-33569/2097152 : ℝ)/8) ∧ Real.exp ((-33569/2097152 : ℝ)/8) ≤ (998001132082149663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33569/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1065_exp_lower : (460056747133213529/500000000000000000 : ℝ) ≤ Real.exp ((-85256451291759/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256451291759/128000000000000 : ℝ)/8) ≤ (920113494266427059/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256451291759/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1065_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902364039/1000000000000 : ℝ) ≤ 4*Real.exp (67137/524288 : ℝ)*Real.exp (-mu (radius 8 (33569/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902364039/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33569/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1065_exp_radius
  have hrNumeric : (39364819351/40000000000 : ℝ) ≤ Real.exp (-33569/2097152 : ℝ) ∧ Real.exp (-33569/2097152 : ℝ) ≤ (15376882559/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39364819351/40000000000 : ℝ) ≤ (radius 8 (33569/262144 : ℝ)) ∧ (radius 8 (33569/262144 : ℝ)) ≤ (15376882559/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33569/262144 : ℝ)) (39364819351/40000000000 : ℝ) (15376882559/15625000000 : ℝ) (88750878041/500000000000 : ℝ) (177501756089/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33569/262144 : ℝ)) (39364819351/40000000000 : ℝ) (15376882559/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39364819351/40000000000 : ℝ) (15376882559/15625000000 : ℝ) (992060241887/1000000000000 : ℝ) (31001882559/31250000000 : ℝ) (248007117309/250000000000 : ℝ) (992028469237/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 1 (992060241887/1000000000000 : ℝ) (31001882559/31250000000 : ℝ) (248007117309/250000000000 : ℝ) (992028469237/1000000000000 : ℝ) (992044355561/1000000000000 : ℝ) (992044355563/1000000000000 : ℝ) (496022177717/500000000000 : ℝ) (248011088859/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 2 (992044355561/1000000000000 : ℝ) (992044355563/1000000000000 : ℝ) (496022177717/500000000000 : ℝ) (248011088859/250000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 3 (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 4 (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 5 (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 6 (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33569/262144 : ℝ)) 7 (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33569/262144 : ℝ))) (88750878041/500000000000 : ℝ) (177501756089/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88750878041/500000000000 : ℝ) (177501756089/1000000000000 : ℝ) (588750878041/1000000000000 : ℝ) (117750175609/200000000000 : ℝ) (421309572739/1000000000000 : ℝ) (105327393187/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 1 (588750878041/1000000000000 : ℝ) (117750175609/200000000000 : ℝ) (421309572739/1000000000000 : ℝ) (105327393187/250000000000 : ℝ) (50503022539/100000000000 : ℝ) (505030225397/1000000000000 : ℝ) (498042549263/1000000000000 : ℝ) (498042549271/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 2 (50503022539/100000000000 : ℝ) (505030225397/1000000000000 : ℝ) (498042549263/1000000000000 : ℝ) (498042549271/1000000000000 : ℝ) (250768193663/500000000000 : ℝ) (250768193667/500000000000 : ℝ) (125381054417/250000000000 : ℝ) (501524217677/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 3 (250768193663/500000000000 : ℝ) (250768193667/500000000000 : ℝ) (125381054417/250000000000 : ℝ) (501524217677/1000000000000 : ℝ) (501530302497/1000000000000 : ℝ) (250765151253/500000000000 : ℝ) (25076515123/50000000000 : ℝ) (501530302469/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 4 (501530302497/1000000000000 : ℝ) (250765151253/500000000000 : ℝ) (25076515123/50000000000 : ℝ) (501530302469/1000000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 5 (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 6 (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33569/262144 : ℝ))) 7 (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33569/262144 : ℝ)) hmem 8 (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33569/262144 : ℝ))) hcmem 8 (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33569/262144 : ℝ)) (992044355497/1000000000000 : ℝ) (1984088711/2000000000 : ℝ) (250765151239/500000000000 : ℝ) (62691287811/125000000000 : ℝ) (794119690859/1000000000000 : ℝ) (397059845439/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1065_exp_lower
  have heNumeric : (2054902364039/1000000000000 : ℝ)/4 ≤ Real.exp (-85256451291759/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902364039/1000000000000 : ℝ)/4 ≤ Real.exp ((67137/524288 : ℝ)-(397059845439/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67137/524288 : ℝ) (33569/262144 : ℝ) (397059845439/500000000000 : ℝ) (2054902364039/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1066; no trusted numerical premise.
theorem cover8_leaf1066_exp_radius : (998001102339398623/1000000000000000000 : ℝ) ≤ Real.exp ((-67139/4194304 : ℝ)/8) ∧ Real.exp ((-67139/4194304 : ℝ)/8) ≤ (31187534448106207/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67139/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1066_exp_lower : (920113494722531091/1000000000000000000 : ℝ) ≤ Real.exp ((-42628225392079/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628225392079/64000000000000 : ℝ)/8) ≤ (230028373680632773/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628225392079/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1066_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725593047/250000000000 : ℝ) ≤ 4*Real.exp (33569/262144 : ℝ)*Real.exp (-mu (radius 8 (67139/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725593047/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67139/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1066_exp_radius
  have hrNumeric : (984120249143/1000000000000 : ℝ) ≤ Real.exp (-67139/4194304 : ℝ) ∧ Real.exp (-67139/4194304 : ℝ) ≤ (123015031143/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984120249143/1000000000000 : ℝ) ≤ (radius 8 (67139/524288 : ℝ)) ∧ (radius 8 (67139/524288 : ℝ)) ≤ (123015031143/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67139/524288 : ℝ)) (984120249143/1000000000000 : ℝ) (123015031143/125000000000 : ℝ) (11093941059/62500000000 : ℝ) (177503056951/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67139/524288 : ℝ)) (984120249143/1000000000000 : ℝ) (123015031143/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984120249143/1000000000000 : ℝ) (123015031143/125000000000 : ℝ) (992060124571/1000000000000 : ℝ) (248015031143/250000000000 : ℝ) (992028350977/1000000000000 : ℝ) (496014175489/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 1 (992060124571/1000000000000 : ℝ) (248015031143/250000000000 : ℝ) (992028350977/1000000000000 : ℝ) (496014175489/500000000000 : ℝ) (496022118887/500000000000 : ℝ) (39681769511/40000000000 : ℝ) (496022118823/500000000000 : ℝ) (62002764853/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 2 (496022118887/500000000000 : ℝ) (39681769511/40000000000 : ℝ) (496022118823/500000000000 : ℝ) (62002764853/62500000000 : ℝ) (99204423771/100000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 3 (99204423771/100000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 4 (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 5 (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 6 (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67139/524288 : ℝ)) 7 (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67139/524288 : ℝ))) (11093941059/62500000000 : ℝ) (177503056951/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11093941059/62500000000 : ℝ) (177503056951/1000000000000 : ℝ) (73593941059/125000000000 : ℝ) (147187882119/250000000000 : ℝ) (52663889571/125000000000 : ℝ) (421311116577/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 1 (73593941059/125000000000 : ℝ) (147187882119/250000000000 : ℝ) (52663889571/125000000000 : ℝ) (421311116577/1000000000000 : ℝ) (12625783063/25000000000 : ℝ) (505031322527/1000000000000 : ℝ) (124510934219/250000000000 : ℝ) (124510934221/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 2 (12625783063/25000000000 : ℝ) (505031322527/1000000000000 : ℝ) (124510934219/250000000000 : ℝ) (124510934221/250000000000 : ℝ) (250768764849/500000000000 : ℝ) (250768764853/500000000000 : ℝ) (250762680191/500000000000 : ℝ) (501525360391/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 3 (250768764849/500000000000 : ℝ) (250768764853/500000000000 : ℝ) (250762680191/500000000000 : ℝ) (501525360391/1000000000000 : ℝ) (6269143063/12500000000 : ℝ) (501531445049/1000000000000 : ℝ) (501531445003/1000000000000 : ℝ) (125382861253/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 4 (6269143063/12500000000 : ℝ) (501531445049/1000000000000 : ℝ) (501531445003/1000000000000 : ℝ) (125382861253/250000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 5 (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 6 (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67139/524288 : ℝ))) 7 (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67139/524288 : ℝ)) hmem 8 (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67139/524288 : ℝ))) hcmem 8 (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67139/524288 : ℝ)) (992044237709/1000000000000 : ℝ) (62002764857/62500000000 : ℝ) (501531445021/1000000000000 : ℝ) (501531445031/1000000000000 : ℝ) (397060797121/500000000000 : ℝ) (794121594261/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1066_exp_lower
  have heNumeric : (513725593047/250000000000 : ℝ)/4 ≤ Real.exp (-42628225392079/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725593047/250000000000 : ℝ)/4 ≤ Real.exp ((33569/262144 : ℝ)-(794121594261/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33569/262144 : ℝ) (67139/524288 : ℝ) (794121594261/1000000000000 : ℝ) (513725593047/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1067; no trusted numerical premise.
theorem cover8_leaf1067_exp_radius : (998001072596648471/1000000000000000000 : ℝ) ≤ Real.exp ((-16785/1048576 : ℝ)/8) ∧ Real.exp ((-16785/1048576 : ℝ)/8) ≤ (124750134074581059/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16785/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1067_exp_lower : (920113495180245323/1000000000000000000 : ℝ) ≤ Real.exp ((-17051290054953/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051290054953/25600000000000 : ℝ)/8) ≤ (230028373795061331/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051290054953/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1067_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980476073/200000000000 : ℝ) ≤ 4*Real.exp (67139/524288 : ℝ)*Real.exp (-mu (radius 8 (16785/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980476073/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16785/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1067_exp_radius
  have hrNumeric : (98412001451/100000000000 : ℝ) ≤ Real.exp (-16785/1048576 : ℝ) ∧ Real.exp (-16785/1048576 : ℝ) ≤ (984120014511/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98412001451/100000000000 : ℝ) ≤ (radius 8 (16785/131072 : ℝ)) ∧ (radius 8 (16785/131072 : ℝ)) ≤ (984120014511/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16785/131072 : ℝ)) (98412001451/100000000000 : ℝ) (984120014511/1000000000000 : ℝ) (88752178901/500000000000 : ℝ) (177504357809/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16785/131072 : ℝ)) (98412001451/100000000000 : ℝ) (984120014511/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98412001451/100000000000 : ℝ) (984120014511/1000000000000 : ℝ) (198412001451/200000000000 : ℝ) (124007500907/125000000000 : ℝ) (496014116359/500000000000 : ℝ) (992028232719/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 1 (198412001451/200000000000 : ℝ) (124007500907/125000000000 : ℝ) (496014116359/500000000000 : ℝ) (992028232719/1000000000000 : ℝ) (496022059993/500000000000 : ℝ) (248011029997/250000000000 : ℝ) (992044119859/1000000000000 : ℝ) (992044119861/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 2 (496022059993/500000000000 : ℝ) (248011029997/250000000000 : ℝ) (992044119859/1000000000000 : ℝ) (992044119861/1000000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 3 (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 4 (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 5 (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 6 (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16785/131072 : ℝ)) 7 (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16785/131072 : ℝ))) (88752178901/500000000000 : ℝ) (177504357809/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88752178901/500000000000 : ℝ) (177504357809/1000000000000 : ℝ) (588752178901/1000000000000 : ℝ) (117750435781/200000000000 : ℝ) (210656330193/500000000000 : ℝ) (84262532079/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 1 (588752178901/1000000000000 : ℝ) (117750435781/200000000000 : ℝ) (210656330193/500000000000 : ℝ) (84262532079/200000000000 : ℝ) (505032419643/1000000000000 : ℝ) (10100648393/20000000000 : ℝ) (1556390389/3125000000 : ℝ) (62255615561/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 2 (505032419643/1000000000000 : ℝ) (10100648393/20000000000 : ℝ) (1556390389/3125000000 : ℝ) (62255615561/125000000000 : ℝ) (501538672061/1000000000000 : ℝ) (501538672069/1000000000000 : ℝ) (501526503089/1000000000000 : ℝ) (501526503097/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 3 (501538672061/1000000000000 : ℝ) (501538672069/1000000000000 : ℝ) (501526503089/1000000000000 : ℝ) (501526503097/1000000000000 : ℝ) (20061303503/40000000000 : ℝ) (501532587583/1000000000000 : ℝ) (250766293769/500000000000 : ℝ) (501532587547/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 4 (20061303503/40000000000 : ℝ) (501532587583/1000000000000 : ℝ) (250766293769/500000000000 : ℝ) (501532587547/1000000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 5 (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 6 (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16785/131072 : ℝ))) 7 (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16785/131072 : ℝ)) hmem 8 (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16785/131072 : ℝ))) hcmem 8 (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16785/131072 : ℝ)) (496022059961/500000000000 : ℝ) (39681764797/40000000000 : ℝ) (125383146889/250000000000 : ℝ) (100306517513/200000000000 : ℝ) (198530874403/250000000000 : ℝ) (79412349763/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1067_exp_lower
  have heNumeric : (410980476073/200000000000 : ℝ)/4 ≤ Real.exp (-17051290054953/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980476073/200000000000 : ℝ)/4 ≤ Real.exp ((67139/524288 : ℝ)-(79412349763/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67139/524288 : ℝ) (16785/131072 : ℝ) (79412349763/100000000000 : ℝ) (410980476073/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1068; no trusted numerical premise.
theorem cover8_leaf1068_exp_radius : (499000521426949603/500000000000000000 : ℝ) ≤ Real.exp ((-67141/4194304 : ℝ)/8) ∧ Real.exp ((-67141/4194304 : ℝ)/8) ≤ (998001042853899207/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67141/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1068_exp_lower : (920113495640604881/1000000000000000000 : ℝ) ≤ Real.exp ((-21314112440607/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314112440607/32000000000000 : ℝ)/8) ≤ (460056747820302441/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314112440607/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1068_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490238859/100000000000 : ℝ) ≤ 4*Real.exp (16785/131072 : ℝ)*Real.exp (-mu (radius 8 (67141/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490238859/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67141/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1068_exp_radius
  have hrNumeric : (492059889939/500000000000 : ℝ) ≤ Real.exp (-67141/4194304 : ℝ) ∧ Real.exp (-67141/4194304 : ℝ) ≤ (984119779879/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492059889939/500000000000 : ℝ) ≤ (radius 8 (67141/524288 : ℝ)) ∧ (radius 8 (67141/524288 : ℝ)) ≤ (984119779879/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67141/524288 : ℝ)) (492059889939/500000000000 : ℝ) (984119779879/1000000000000 : ℝ) (44376414661/250000000000 : ℝ) (177505658651/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67141/524288 : ℝ)) (492059889939/500000000000 : ℝ) (984119779879/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492059889939/500000000000 : ℝ) (984119779879/1000000000000 : ℝ) (992059889939/1000000000000 : ℝ) (49602994497/50000000000 : ℝ) (992028114459/1000000000000 : ℝ) (49601405723/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 1 (992059889939/1000000000000 : ℝ) (49602994497/50000000000 : ℝ) (992028114459/1000000000000 : ℝ) (49601405723/50000000000 : ℝ) (992044002199/1000000000000 : ℝ) (4960220011/5000000000 : ℝ) (992044002071/1000000000000 : ℝ) (992044002073/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 2 (992044002199/1000000000000 : ℝ) (4960220011/5000000000 : ℝ) (992044002071/1000000000000 : ℝ) (992044002073/1000000000000 : ℝ) (198408800427/200000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 3 (198408800427/200000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 4 (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 5 (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 6 (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67141/524288 : ℝ)) 7 (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67141/524288 : ℝ))) (44376414661/250000000000 : ℝ) (177505658651/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44376414661/250000000000 : ℝ) (177505658651/1000000000000 : ℝ) (294376414661/500000000000 : ℝ) (294376414663/500000000000 : ℝ) (21065710209/50000000000 : ℝ) (421314204189/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 1 (294376414661/500000000000 : ℝ) (294376414663/500000000000 : ℝ) (21065710209/50000000000 : ℝ) (421314204189/1000000000000 : ℝ) (505033516751/1000000000000 : ℝ) (252516758379/500000000000 : ℝ) (249023056033/500000000000 : ℝ) (249023056037/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 2 (505033516751/1000000000000 : ℝ) (252516758379/500000000000 : ℝ) (249023056033/500000000000 : ℝ) (249023056037/500000000000 : ℝ) (62692476801/125000000000 : ℝ) (31346238401/62500000000 : ℝ) (501527645779/1000000000000 : ℝ) (501527645787/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 3 (62692476801/125000000000 : ℝ) (31346238401/62500000000 : ℝ) (501527645779/1000000000000 : ℝ) (501527645787/1000000000000 : ℝ) (501533730093/1000000000000 : ℝ) (250766865051/500000000000 : ℝ) (62691716257/125000000000 : ℝ) (100306746013/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 4 (501533730093/1000000000000 : ℝ) (250766865051/500000000000 : ℝ) (62691716257/125000000000 : ℝ) (100306746013/200000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 5 (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 6 (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67141/524288 : ℝ))) 7 (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67141/524288 : ℝ)) hmem 8 (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67141/524288 : ℝ))) hcmem 8 (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67141/524288 : ℝ)) (496022001067/500000000000 : ℝ) (992044002137/1000000000000 : ℝ) (250766865037/500000000000 : ℝ) (125383432521/250000000000 : ℝ) (198531350239/250000000000 : ℝ) (49632837561/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1068_exp_lower
  have heNumeric : (205490238859/100000000000 : ℝ)/4 ≤ Real.exp (-21314112440607/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490238859/100000000000 : ℝ)/4 ≤ Real.exp ((16785/131072 : ℝ)-(49632837561/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16785/131072 : ℝ) (67141/524288 : ℝ) (49632837561/62500000000 : ℝ) (205490238859/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1069; no trusted numerical premise.
theorem cover8_leaf1069_exp_radius : (998001013111150827/1000000000000000000 : ℝ) ≤ Real.exp ((-33571/2097152 : ℝ)/8) ∧ Real.exp ((-33571/2097152 : ℝ)/8) ≤ (249500253277787707/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33571/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1069_exp_lower : (115014187012807453/125000000000000000 : ℝ) ≤ Real.exp ((-85256449248427/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256449248427/128000000000000 : ℝ)/8) ≤ (7360907968819677/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256449248427/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1069_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451198421/500000000000 : ℝ) ≤ 4*Real.exp (67141/524288 : ℝ)*Real.exp (-mu (radius 8 (33571/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451198421/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33571/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1069_exp_radius
  have hrNumeric : (196823909049/200000000000 : ℝ) ≤ Real.exp (-33571/2097152 : ℝ) ∧ Real.exp (-33571/2097152 : ℝ) ≤ (492059772623/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196823909049/200000000000 : ℝ) ≤ (radius 8 (33571/262144 : ℝ)) ∧ (radius 8 (33571/262144 : ℝ)) ≤ (492059772623/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33571/262144 : ℝ)) (196823909049/200000000000 : ℝ) (492059772623/500000000000 : ℝ) (88753479741/500000000000 : ℝ) (177506959489/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33571/262144 : ℝ)) (196823909049/200000000000 : ℝ) (492059772623/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196823909049/200000000000 : ℝ) (492059772623/500000000000 : ℝ) (496029886311/500000000000 : ℝ) (992059772623/1000000000000 : ℝ) (4960139981/5000000000 : ℝ) (992027996201/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 1 (496029886311/500000000000 : ℝ) (992059772623/1000000000000 : ℝ) (4960139981/5000000000 : ℝ) (992027996201/1000000000000 : ℝ) (992043884411/1000000000000 : ℝ) (248010971103/250000000000 : ℝ) (992043884283/1000000000000 : ℝ) (198408776857/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 2 (992043884411/1000000000000 : ℝ) (248010971103/250000000000 : ℝ) (992043884283/1000000000000 : ℝ) (198408776857/200000000000 : ℝ) (992043884347/1000000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 3 (992043884347/1000000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 4 (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 5 (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 6 (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33571/262144 : ℝ)) 7 (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33571/262144 : ℝ))) (88753479741/500000000000 : ℝ) (177506959489/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88753479741/500000000000 : ℝ) (177506959489/1000000000000 : ℝ) (588753479741/1000000000000 : ℝ) (117750695949/200000000000 : ℝ) (421315747963/1000000000000 : ℝ) (105328936993/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 1 (588753479741/1000000000000 : ℝ) (117750695949/200000000000 : ℝ) (421315747963/1000000000000 : ℝ) (105328936993/250000000000 : ℝ) (126258653463/250000000000 : ℝ) (505034613859/1000000000000 : ℝ) (124511824911/250000000000 : ℝ) (124511824913/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 2 (126258653463/250000000000 : ℝ) (505034613859/1000000000000 : ℝ) (124511824911/250000000000 : ℝ) (124511824913/250000000000 : ℝ) (125385239187/250000000000 : ℝ) (125385239189/250000000000 : ℝ) (501528788461/1000000000000 : ℝ) (50152878847/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 3 (125385239187/250000000000 : ℝ) (125385239189/250000000000 : ℝ) (501528788461/1000000000000 : ℝ) (50152878847/100000000000 : ℝ) (125383718151/250000000000 : ℝ) (501534872613/1000000000000 : ℝ) (501534872567/1000000000000 : ℝ) (501534872577/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 4 (125383718151/250000000000 : ℝ) (501534872613/1000000000000 : ℝ) (501534872567/1000000000000 : ℝ) (501534872577/1000000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 5 (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 6 (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33571/262144 : ℝ))) 7 (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33571/262144 : ℝ)) hmem 8 (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33571/262144 : ℝ))) hcmem 8 (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33571/262144 : ℝ)) (496021942173/500000000000 : ℝ) (992043884349/1000000000000 : ℝ) (100306974517/200000000000 : ℝ) (100306974519/200000000000 : ℝ) (79412730429/100000000000 : ℝ) (794127304309/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1069_exp_lower
  have heNumeric : (1027451198421/500000000000 : ℝ)/4 ≤ Real.exp (-85256449248427/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451198421/500000000000 : ℝ)/4 ≤ Real.exp ((67141/524288 : ℝ)-(794127304309/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67141/524288 : ℝ) (33571/262144 : ℝ) (794127304309/1000000000000 : ℝ) (1027451198421/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1070; no trusted numerical premise.
theorem cover8_leaf1070_exp_radius : (499000491684201667/500000000000000000 : ℝ) ≤ Real.exp ((-67143/4194304 : ℝ)/8) ∧ Real.exp ((-67143/4194304 : ℝ)/8) ≤ (199600196673680667/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67143/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1070_exp_lower : (184022699313506953/200000000000000000 : ℝ) ≤ Real.exp ((-42628224365421/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628224365421/64000000000000 : ℝ)/8) ≤ (460056748283767383/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628224365421/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1070_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902405151/1000000000000 : ℝ) ≤ 4*Real.exp (33571/262144 : ℝ)*Real.exp (-mu (radius 8 (67143/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902405151/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67143/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1070_exp_radius
  have hrNumeric : (984119310613/1000000000000 : ℝ) ≤ Real.exp (-67143/4194304 : ℝ) ∧ Real.exp (-67143/4194304 : ℝ) ≤ (492059655307/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984119310613/1000000000000 : ℝ) ≤ (radius 8 (67143/524288 : ℝ)) ∧ (radius 8 (67143/524288 : ℝ)) ≤ (492059655307/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67143/524288 : ℝ)) (984119310613/1000000000000 : ℝ) (492059655307/500000000000 : ℝ) (35501652061/200000000000 : ℝ) (177508260311/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67143/524288 : ℝ)) (984119310613/1000000000000 : ℝ) (492059655307/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984119310613/1000000000000 : ℝ) (492059655307/500000000000 : ℝ) (496029827653/500000000000 : ℝ) (992059655307/1000000000000 : ℝ) (992027877941/1000000000000 : ℝ) (496013938971/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 1 (496029827653/500000000000 : ℝ) (992059655307/1000000000000 : ℝ) (992027877941/1000000000000 : ℝ) (496013938971/500000000000 : ℝ) (992043766623/1000000000000 : ℝ) (7936350133/8000000000 : ℝ) (31001367703/31250000000 : ℝ) (496021883249/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 2 (992043766623/1000000000000 : ℝ) (7936350133/8000000000 : ℝ) (31001367703/31250000000 : ℝ) (496021883249/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 3 (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 4 (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 5 (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 6 (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67143/524288 : ℝ)) 7 (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67143/524288 : ℝ))) (35501652061/200000000000 : ℝ) (177508260311/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35501652061/200000000000 : ℝ) (177508260311/1000000000000 : ℝ) (73594266269/125000000000 : ℝ) (147188532539/250000000000 : ℝ) (421317291723/1000000000000 : ℝ) (421317291731/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 1 (73594266269/125000000000 : ℝ) (147188532539/250000000000 : ℝ) (421317291723/1000000000000 : ℝ) (421317291731/1000000000000 : ℝ) (505035710937/1000000000000 : ℝ) (15782365967/31250000000 : ℝ) (124512121801/250000000000 : ℝ) (498048487211/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 2 (505035710937/1000000000000 : ℝ) (15782365967/31250000000 : ℝ) (124512121801/250000000000 : ℝ) (498048487211/1000000000000 : ℝ) (50154209907/100000000000 : ℝ) (250771049539/500000000000 : ℝ) (250764965563/500000000000 : ℝ) (250764965567/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 3 (50154209907/100000000000 : ℝ) (250771049539/500000000000 : ℝ) (250764965563/500000000000 : ℝ) (250764965567/500000000000 : ℝ) (250768007549/500000000000 : ℝ) (250768007553/500000000000 : ℝ) (501536015061/1000000000000 : ℝ) (50153601507/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 4 (250768007549/500000000000 : ℝ) (250768007553/500000000000 : ℝ) (501536015061/1000000000000 : ℝ) (50153601507/100000000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 5 (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 6 (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67143/524288 : ℝ))) 7 (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67143/524288 : ℝ)) hmem 8 (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67143/524288 : ℝ))) hcmem 8 (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67143/524288 : ℝ)) (992043766559/1000000000000 : ℝ) (496021883281/500000000000 : ℝ) (501536015079/1000000000000 : ℝ) (31346000943/62500000000 : ℝ) (794129207597/1000000000000 : ℝ) (397064603807/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1070_exp_lower
  have heNumeric : (2054902405151/1000000000000 : ℝ)/4 ≤ Real.exp (-42628224365421/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902405151/1000000000000 : ℝ)/4 ≤ Real.exp ((33571/262144 : ℝ)-(397064603807/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33571/262144 : ℝ) (67143/524288 : ℝ) (397064603807/500000000000 : ℝ) (2054902405151/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1071; no trusted numerical premise.
theorem cover8_leaf1071_exp_radius : (998000953625656727/1000000000000000000 : ℝ) ≤ Real.exp ((-8393/524288 : ℝ)/8) ∧ Real.exp ((-8393/524288 : ℝ)/8) ≤ (124750119203207091/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8393/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1071_exp_lower : (920113497034450133/1000000000000000000 : ℝ) ≤ Real.exp ((-85256448211209/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256448211209/128000000000000 : ℝ)/8) ≤ (460056748517225067/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256448211209/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1071_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451206747/500000000000 : ℝ) ≤ 4*Real.exp (67143/524288 : ℝ)*Real.exp (-mu (radius 8 (8393/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451206747/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8393/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1071_exp_radius
  have hrNumeric : (984119075981/1000000000000 : ℝ) ≤ Real.exp (-8393/524288 : ℝ) ∧ Real.exp (-8393/524288 : ℝ) ≤ (492059537991/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984119075981/1000000000000 : ℝ) ≤ (radius 8 (8393/65536 : ℝ)) ∧ (radius 8 (8393/65536 : ℝ)) ≤ (492059537991/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8393/65536 : ℝ)) (984119075981/1000000000000 : ℝ) (492059537991/500000000000 : ℝ) (88754780559/500000000000 : ℝ) (44377390281/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8393/65536 : ℝ)) (984119075981/1000000000000 : ℝ) (492059537991/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984119075981/1000000000000 : ℝ) (492059537991/500000000000 : ℝ) (99205953799/100000000000 : ℝ) (992059537991/1000000000000 : ℝ) (496013879841/500000000000 : ℝ) (248006939921/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 1 (99205953799/100000000000 : ℝ) (992059537991/1000000000000 : ℝ) (496013879841/500000000000 : ℝ) (248006939921/250000000000 : ℝ) (248010912209/250000000000 : ℝ) (496021824419/500000000000 : ℝ) (248010912177/250000000000 : ℝ) (992043648711/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 2 (248010912209/250000000000 : ℝ) (496021824419/500000000000 : ℝ) (248010912177/250000000000 : ℝ) (992043648711/1000000000000 : ℝ) (248010912193/250000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 3 (248010912193/250000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 4 (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 5 (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 6 (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8393/65536 : ℝ)) 7 (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8393/65536 : ℝ))) (88754780559/500000000000 : ℝ) (44377390281/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88754780559/500000000000 : ℝ) (44377390281/250000000000 : ℝ) (588754780559/1000000000000 : ℝ) (294377390281/500000000000 : ℝ) (84263767093/200000000000 : ℝ) (421318835473/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 1 (588754780559/1000000000000 : ℝ) (294377390281/500000000000 : ℝ) (84263767093/200000000000 : ℝ) (421318835473/1000000000000 : ℝ) (126259202003/250000000000 : ℝ) (252518404009/500000000000 : ℝ) (1992198699/4000000000 : ℝ) (498049674757/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 2 (126259202003/250000000000 : ℝ) (252518404009/500000000000 : ℝ) (1992198699/4000000000 : ℝ) (498049674757/1000000000000 : ℝ) (501543241381/1000000000000 : ℝ) (125385810347/250000000000 : ℝ) (25076553689/50000000000 : ℝ) (501531073787/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 3 (501543241381/1000000000000 : ℝ) (125385810347/250000000000 : ℝ) (25076553689/50000000000 : ℝ) (501531073787/1000000000000 : ℝ) (25076857879/50000000000 : ℝ) (125384289397/250000000000 : ℝ) (501537157543/1000000000000 : ℝ) (501537157551/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 4 (25076857879/50000000000 : ℝ) (125384289397/250000000000 : ℝ) (501537157543/1000000000000 : ℝ) (501537157551/1000000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 5 (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 6 (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8393/65536 : ℝ))) 7 (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8393/65536 : ℝ)) hmem 8 (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8393/65536 : ℝ))) hcmem 8 (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8393/65536 : ℝ)) (992043648771/1000000000000 : ℝ) (39681745951/40000000000 : ℝ) (501537157561/1000000000000 : ℝ) (50153715757/100000000000 : ℝ) (198532777721/250000000000 : ℝ) (794131110903/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1071_exp_lower
  have heNumeric : (1027451206747/500000000000 : ℝ)/4 ≤ Real.exp (-85256448211209/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451206747/500000000000 : ℝ)/4 ≤ Real.exp ((67143/524288 : ℝ)-(794131110903/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67143/524288 : ℝ) (8393/65536 : ℝ) (794131110903/1000000000000 : ℝ) (1027451206747/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1072; no trusted numerical premise.
theorem cover8_leaf1072_exp_radius : (998000923882911007/1000000000000000000 : ℝ) ≤ Real.exp ((-67145/4194304 : ℝ)/8) ∧ Real.exp ((-67145/4194304 : ℝ)/8) ≤ (31187528871340969/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67145/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1072_exp_lower : (184022699500733157/200000000000000000 : ℝ) ≤ Real.exp ((-10657055961127/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657055961127/16000000000000 : ℝ)/8) ≤ (460056748751832893/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657055961127/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1072_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902421877/1000000000000 : ℝ) ≤ 4*Real.exp (8393/65536 : ℝ)*Real.exp (-mu (radius 8 (67145/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902421877/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67145/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1072_exp_radius
  have hrNumeric : (984118841349/1000000000000 : ℝ) ≤ Real.exp (-67145/4194304 : ℝ) ∧ Real.exp (-67145/4194304 : ℝ) ≤ (19682376827/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984118841349/1000000000000 : ℝ) ≤ (radius 8 (67145/524288 : ℝ)) ∧ (radius 8 (67145/524288 : ℝ)) ≤ (19682376827/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67145/524288 : ℝ)) (984118841349/1000000000000 : ℝ) (19682376827/20000000000 : ℝ) (1109442887/6250000000 : ℝ) (177510861927/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67145/524288 : ℝ)) (984118841349/1000000000000 : ℝ) (19682376827/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984118841349/1000000000000 : ℝ) (19682376827/20000000000 : ℝ) (496029710337/500000000000 : ℝ) (39682376827/40000000000 : ℝ) (992027641423/1000000000000 : ℝ) (39681105657/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 1 (496029710337/500000000000 : ℝ) (39682376827/40000000000 : ℝ) (992027641423/1000000000000 : ℝ) (39681105657/40000000000 : ℝ) (124005441381/125000000000 : ℝ) (19840870621/20000000000 : ℝ) (992043530921/1000000000000 : ℝ) (992043530923/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 2 (124005441381/125000000000 : ℝ) (19840870621/20000000000 : ℝ) (992043530921/1000000000000 : ℝ) (992043530923/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 3 (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 4 (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 5 (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 6 (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67145/524288 : ℝ)) 7 (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67145/524288 : ℝ))) (1109442887/6250000000 : ℝ) (177510861927/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1109442887/6250000000 : ℝ) (177510861927/1000000000000 : ℝ) (7359442887/12500000000 : ℝ) (147188857741/250000000000 : ℝ) (421320379189/1000000000000 : ℝ) (210660189599/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 1 (7359442887/12500000000 : ℝ) (147188857741/250000000000 : ℝ) (421320379189/1000000000000 : ℝ) (210660189599/500000000000 : ℝ) (252518952537/500000000000 : ℝ) (505037905081/1000000000000 : ℝ) (498050862283/1000000000000 : ℝ) (498050862291/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 2 (252518952537/500000000000 : ℝ) (505037905081/1000000000000 : ℝ) (498050862283/1000000000000 : ℝ) (498050862291/1000000000000 : ℝ) (250772191839/500000000000 : ℝ) (250772191843/500000000000 : ℝ) (25076610821/50000000000 : ℝ) (501532216429/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 3 (250772191839/500000000000 : ℝ) (250772191843/500000000000 : ℝ) (25076610821/50000000000 : ℝ) (501532216429/1000000000000 : ℝ) (501538300049/1000000000000 : ℝ) (250769150029/500000000000 : ℝ) (125384575003/250000000000 : ℝ) (501538300021/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 4 (501538300049/1000000000000 : ℝ) (250769150029/500000000000 : ℝ) (125384575003/250000000000 : ℝ) (501538300021/1000000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 5 (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 6 (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67145/524288 : ℝ))) 7 (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67145/524288 : ℝ)) hmem 8 (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67145/524288 : ℝ))) hcmem 8 (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67145/524288 : ℝ)) (124005441373/125000000000 : ℝ) (992043530987/1000000000000 : ℝ) (50153830003/100000000000 : ℝ) (12538457501/25000000000 : ℝ) (794133014153/1000000000000 : ℝ) (198533253543/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1072_exp_lower
  have heNumeric : (2054902421877/1000000000000 : ℝ)/4 ≤ Real.exp (-10657055961127/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902421877/1000000000000 : ℝ)/4 ≤ Real.exp ((8393/65536 : ℝ)-(198533253543/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8393/65536 : ℝ) (67145/524288 : ℝ) (198533253543/250000000000 : ℝ) (2054902421877/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1073; no trusted numerical premise.
theorem cover8_leaf1073_exp_radius : (499000447070083087/500000000000000000 : ℝ) ≤ Real.exp ((-33573/2097152 : ℝ)/8) ∧ Real.exp ((-33573/2097152 : ℝ)/8) ≤ (39920035765606647/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33573/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1073_exp_lower : (230028374493479141/250000000000000000 : ℝ) ≤ Real.exp ((-85256447165671/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256447165671/128000000000000 : ℝ)/8) ≤ (184022699594783313/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256447165671/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1073_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902430279/1000000000000 : ℝ) ≤ 4*Real.exp (67145/524288 : ℝ)*Real.exp (-mu (radius 8 (33573/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902430279/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33573/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1073_exp_radius
  have hrNumeric : (246029651679/250000000000 : ℝ) ≤ Real.exp (-33573/2097152 : ℝ) ∧ Real.exp (-33573/2097152 : ℝ) ≤ (984118606717/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246029651679/250000000000 : ℝ) ≤ (radius 8 (33573/262144 : ℝ)) ∧ (radius 8 (33573/262144 : ℝ)) ≤ (984118606717/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33573/262144 : ℝ)) (246029651679/250000000000 : ℝ) (984118606717/1000000000000 : ℝ) (177512162719/1000000000000 : ℝ) (88756081363/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33573/262144 : ℝ)) (246029651679/250000000000 : ℝ) (984118606717/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246029651679/250000000000 : ℝ) (984118606717/1000000000000 : ℝ) (496029651679/500000000000 : ℝ) (992059303359/1000000000000 : ℝ) (248006880791/250000000000 : ℝ) (496013761583/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 1 (496029651679/500000000000 : ℝ) (992059303359/1000000000000 : ℝ) (248006880791/250000000000 : ℝ) (496013761583/500000000000 : ℝ) (992043413261/1000000000000 : ℝ) (992043413263/1000000000000 : ℝ) (992043413133/1000000000000 : ℝ) (62002713321/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 2 (992043413261/1000000000000 : ℝ) (992043413263/1000000000000 : ℝ) (992043413133/1000000000000 : ℝ) (62002713321/62500000000 : ℝ) (992043413197/1000000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 3 (992043413197/1000000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 4 (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 5 (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 6 (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33573/262144 : ℝ)) 7 (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33573/262144 : ℝ))) (177512162719/1000000000000 : ℝ) (88756081363/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177512162719/1000000000000 : ℝ) (88756081363/500000000000 : ℝ) (588756081359/1000000000000 : ℝ) (588756081363/1000000000000 : ℝ) (421321922903/1000000000000 : ℝ) (13166310091/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 1 (588756081359/1000000000000 : ℝ) (588756081363/1000000000000 : ℝ) (421321922903/1000000000000 : ℝ) (13166310091/31250000000 : ℝ) (505039002131/1000000000000 : ℝ) (252519501069/500000000000 : ℝ) (498052049809/1000000000000 : ℝ) (498052049817/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 2 (505039002131/1000000000000 : ℝ) (252519501069/500000000000 : ℝ) (498052049809/1000000000000 : ℝ) (498052049817/1000000000000 : ℝ) (50154552597/100000000000 : ℝ) (250772762989/500000000000 : ℝ) (250766679527/500000000000 : ℝ) (501533359063/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 3 (50154552597/100000000000 : ℝ) (250772762989/500000000000 : ℝ) (250766679527/500000000000 : ℝ) (501533359063/1000000000000 : ℝ) (31346215157/62500000000 : ℝ) (501539442521/1000000000000 : ℝ) (20061577699/40000000000 : ℝ) (125384860621/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 4 (31346215157/62500000000 : ℝ) (501539442521/1000000000000 : ℝ) (20061577699/40000000000 : ℝ) (125384860621/250000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 5 (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 6 (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33573/262144 : ℝ))) 7 (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33573/262144 : ℝ)) hmem 8 (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33573/262144 : ℝ))) hcmem 8 (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33573/262144 : ℝ)) (248010853299/250000000000 : ℝ) (2480108533/2500000000 : ℝ) (501539442493/1000000000000 : ℝ) (501539442503/1000000000000 : ℝ) (198533729353/250000000000 : ℝ) (99266864679/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1073_exp_lower
  have heNumeric : (2054902430279/1000000000000 : ℝ)/4 ≤ Real.exp (-85256447165671/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902430279/1000000000000 : ℝ)/4 ≤ Real.exp ((67145/524288 : ℝ)-(99266864679/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67145/524288 : ℝ) (33573/262144 : ℝ) (99266864679/125000000000 : ℝ) (2054902430279/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1074; no trusted numerical premise.
theorem cover8_leaf1074_exp_radius : (998000864397422227/1000000000000000000 : ℝ) ≤ Real.exp ((-67147/4194304 : ℝ)/8) ∧ Real.exp ((-67147/4194304 : ℝ)/8) ≤ (249500216099355557/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67147/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1074_exp_lower : (92011349844761777/100000000000000000 : ℝ) ≤ Real.exp ((-42628223319243/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628223319243/64000000000000 : ℝ)/8) ≤ (920113498447617771/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628223319243/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1074_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451219371/500000000000 : ℝ) ≤ 4*Real.exp (33573/262144 : ℝ)*Real.exp (-mu (radius 8 (67147/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451219371/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67147/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1074_exp_radius
  have hrNumeric : (246029593021/250000000000 : ℝ) ≤ Real.exp (-67147/4194304 : ℝ) ∧ Real.exp (-67147/4194304 : ℝ) ≤ (196823674417/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246029593021/250000000000 : ℝ) ≤ (radius 8 (67147/524288 : ℝ)) ∧ (radius 8 (67147/524288 : ℝ)) ≤ (196823674417/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67147/524288 : ℝ)) (246029593021/250000000000 : ℝ) (196823674417/200000000000 : ℝ) (88756731751/500000000000 : ℝ) (177513463509/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67147/524288 : ℝ)) (246029593021/250000000000 : ℝ) (196823674417/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246029593021/250000000000 : ℝ) (196823674417/200000000000 : ℝ) (496029593021/500000000000 : ℝ) (992059186043/1000000000000 : ℝ) (198405480981/200000000000 : ℝ) (992027404907/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 1 (496029593021/500000000000 : ℝ) (992059186043/1000000000000 : ℝ) (198405480981/200000000000 : ℝ) (992027404907/1000000000000 : ℝ) (992043295473/1000000000000 : ℝ) (39681731819/40000000000 : ℝ) (496021647673/500000000000 : ℝ) (248010823837/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 2 (992043295473/1000000000000 : ℝ) (39681731819/40000000000 : ℝ) (496021647673/500000000000 : ℝ) (248010823837/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 3 (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 4 (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 5 (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 6 (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67147/524288 : ℝ)) 7 (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67147/524288 : ℝ))) (88756731751/500000000000 : ℝ) (177513463509/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88756731751/500000000000 : ℝ) (177513463509/1000000000000 : ℝ) (588756731751/1000000000000 : ℝ) (117751346351/200000000000 : ℝ) (421323466593/1000000000000 : ℝ) (210661733301/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 1 (588756731751/1000000000000 : ℝ) (117751346351/200000000000 : ℝ) (421323466593/1000000000000 : ℝ) (210661733301/500000000000 : ℝ) (126260024793/250000000000 : ℝ) (505040099179/1000000000000 : ℝ) (124513309329/250000000000 : ℝ) (124513309331/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 2 (126260024793/250000000000 : ℝ) (505040099179/1000000000000 : ℝ) (124513309329/250000000000 : ℝ) (124513309331/250000000000 : ℝ) (125386667061/250000000000 : ℝ) (125386667063/250000000000 : ℝ) (501534501671/1000000000000 : ℝ) (6269181271/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 3 (125386667061/250000000000 : ℝ) (125386667063/250000000000 : ℝ) (501534501671/1000000000000 : ℝ) (6269181271/12500000000 : ℝ) (501540584957/1000000000000 : ℝ) (250770292483/500000000000 : ℝ) (12538514623/25000000000 : ℝ) (50154058493/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 4 (501540584957/1000000000000 : ℝ) (250770292483/500000000000 : ℝ) (12538514623/25000000000 : ℝ) (50154058493/100000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 5 (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 6 (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67147/524288 : ℝ))) 7 (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67147/524288 : ℝ)) hmem 8 (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67147/524288 : ℝ))) hcmem 8 (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67147/524288 : ℝ)) (992043295409/1000000000000 : ℝ) (248010823853/250000000000 : ℝ) (250770292469/500000000000 : ℝ) (125385146237/250000000000 : ℝ) (794136820643/1000000000000 : ℝ) (397068410331/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1074_exp_lower
  have heNumeric : (1027451219371/500000000000 : ℝ)/4 ≤ Real.exp (-42628223319243/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451219371/500000000000 : ℝ)/4 ≤ Real.exp ((33573/262144 : ℝ)-(397068410331/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33573/262144 : ℝ) (67147/524288 : ℝ) (397068410331/500000000000 : ℝ) (1027451219371/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1050_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1050_certificate
#check SmaleRate.Proofs.cover8_leaf1051_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1051_certificate
#check SmaleRate.Proofs.cover8_leaf1052_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1052_certificate
#check SmaleRate.Proofs.cover8_leaf1053_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1053_certificate
#check SmaleRate.Proofs.cover8_leaf1054_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1054_certificate
#check SmaleRate.Proofs.cover8_leaf1055_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1055_certificate
#check SmaleRate.Proofs.cover8_leaf1056_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1056_certificate
#check SmaleRate.Proofs.cover8_leaf1057_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1057_certificate
#check SmaleRate.Proofs.cover8_leaf1058_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1058_certificate
#check SmaleRate.Proofs.cover8_leaf1059_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1059_certificate
#check SmaleRate.Proofs.cover8_leaf1060_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1060_certificate
#check SmaleRate.Proofs.cover8_leaf1061_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1061_certificate
#check SmaleRate.Proofs.cover8_leaf1062_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1062_certificate
#check SmaleRate.Proofs.cover8_leaf1063_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1063_certificate
#check SmaleRate.Proofs.cover8_leaf1064_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1064_certificate
#check SmaleRate.Proofs.cover8_leaf1065_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1065_certificate
#check SmaleRate.Proofs.cover8_leaf1066_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1066_certificate
#check SmaleRate.Proofs.cover8_leaf1067_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1067_certificate
#check SmaleRate.Proofs.cover8_leaf1068_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1068_certificate
#check SmaleRate.Proofs.cover8_leaf1069_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1069_certificate
#check SmaleRate.Proofs.cover8_leaf1070_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1070_certificate
#check SmaleRate.Proofs.cover8_leaf1071_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1071_certificate
#check SmaleRate.Proofs.cover8_leaf1072_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1072_certificate
#check SmaleRate.Proofs.cover8_leaf1073_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1073_certificate
#check SmaleRate.Proofs.cover8_leaf1074_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1074_certificate
