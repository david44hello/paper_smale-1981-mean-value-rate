/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1100; no trusted numerical premise.
theorem cover8_leaf1100_exp_radius : (998000091086390727/1000000000000000000 : ℝ) ≤ Real.exp ((-67173/4194304 : ℝ)/8) ∧ Real.exp ((-67173/4194304 : ℝ)/8) ≤ (124750011385798841/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67173/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1100_exp_lower : (920113511532028969/1000000000000000000 : ℝ) ≤ Real.exp ((-21314108019191/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314108019191/32000000000000 : ℝ)/8) ≤ (92011351153202897/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314108019191/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1100_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980534503/200000000000 : ℝ) ≤ 4*Real.exp (16793/131072 : ℝ)*Real.exp (-mu (radius 8 (67173/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980534503/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67173/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1100_exp_radius
  have hrNumeric : (246028067917/250000000000 : ℝ) ≤ Real.exp (-67173/4194304 : ℝ) ∧ Real.exp (-67173/4194304 : ℝ) ≤ (984112271669/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246028067917/250000000000 : ℝ) ≤ (radius 8 (67173/524288 : ℝ)) ∧ (radius 8 (67173/524288 : ℝ)) ≤ (984112271669/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67173/524288 : ℝ)) (246028067917/250000000000 : ℝ) (984112271669/1000000000000 : ℝ) (44386820081/250000000000 : ℝ) (17754728033/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67173/524288 : ℝ)) (246028067917/250000000000 : ℝ) (984112271669/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246028067917/250000000000 : ℝ) (984112271669/1000000000000 : ℝ) (496028067917/500000000000 : ℝ) (198411227167/200000000000 : ℝ) (992024330179/1000000000000 : ℝ) (49601216509/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 1 (496028067917/500000000000 : ℝ) (198411227167/200000000000 : ℝ) (992024330179/1000000000000 : ℝ) (49601216509/50000000000 : ℝ) (496020116503/500000000000 : ℝ) (62002514563/62500000000 : ℝ) (992040232879/1000000000000 : ℝ) (992040232881/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 2 (496020116503/500000000000 : ℝ) (62002514563/62500000000 : ℝ) (992040232879/1000000000000 : ℝ) (992040232881/1000000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 3 (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 4 (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 5 (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 6 (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67173/524288 : ℝ)) 7 (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67173/524288 : ℝ))) (44386820081/250000000000 : ℝ) (17754728033/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44386820081/250000000000 : ℝ) (17754728033/100000000000 : ℝ) (294386820081/500000000000 : ℝ) (117754728033/200000000000 : ℝ) (52670449543/125000000000 : ℝ) (6583806193/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 1 (294386820081/500000000000 : ℝ) (117754728033/200000000000 : ℝ) (52670449543/125000000000 : ℝ) (6583806193/15625000000 : ℝ) (505068618253/1000000000000 : ℝ) (505068618259/1000000000000 : ℝ) (15565128369/31250000000 : ℝ) (99616821563/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 2 (505068618253/1000000000000 : ℝ) (505068618259/1000000000000 : ℝ) (15565128369/31250000000 : ℝ) (99616821563/200000000000 : ℝ) (50157636303/100000000000 : ℝ) (501576363037/1000000000000 : ℝ) (100312841073/200000000000 : ℝ) (501564205373/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 3 (50157636303/100000000000 : ℝ) (501576363037/1000000000000 : ℝ) (100312841073/200000000000 : ℝ) (501564205373/1000000000000 : ℝ) (501570284197/1000000000000 : ℝ) (100314056841/200000000000 : ℝ) (783703569/1562500000 : ℝ) (501570284169/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 4 (501570284197/1000000000000 : ℝ) (100314056841/200000000000 : ℝ) (783703569/1562500000 : ℝ) (501570284169/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 5 (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 6 (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67173/524288 : ℝ))) 7 (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67173/524288 : ℝ)) hmem 8 (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67173/524288 : ℝ))) hcmem 8 (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67173/524288 : ℝ)) (496020116471/500000000000 : ℝ) (198408046589/200000000000 : ℝ) (250785142089/500000000000 : ℝ) (501570284187/1000000000000 : ℝ) (397093148973/500000000000 : ℝ) (794186297963/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1100_exp_lower
  have heNumeric : (410980534503/200000000000 : ℝ)/4 ≤ Real.exp (-21314108019191/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980534503/200000000000 : ℝ)/4 ≤ Real.exp ((16793/131072 : ℝ)-(794186297963/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16793/131072 : ℝ) (67173/524288 : ℝ) (794186297963/1000000000000 : ℝ) (410980534503/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1101; no trusted numerical premise.
theorem cover8_leaf1101_exp_radius : (998000061343670713/1000000000000000000 : ℝ) ≤ Real.exp ((-33587/2097152 : ℝ)/8) ∧ Real.exp ((-33587/2097152 : ℝ)/8) ≤ (499000030671835357/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33587/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1101_exp_lower : (23002837801638439/25000000000000000 : ℝ) ≤ Real.exp ((-85256431483019/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256431483019/128000000000000 : ℝ)/8) ≤ (920113512065537561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256431483019/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1101_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902682047/1000000000000 : ℝ) ≤ 4*Real.exp (67173/524288 : ℝ)*Real.exp (-mu (radius 8 (33587/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902682047/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33587/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1101_exp_radius
  have hrNumeric : (492056018519/500000000000 : ℝ) ≤ Real.exp (-33587/2097152 : ℝ) ∧ Real.exp (-33587/2097152 : ℝ) ≤ (984112037039/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492056018519/500000000000 : ℝ) ≤ (radius 8 (33587/262144 : ℝ)) ∧ (radius 8 (33587/262144 : ℝ)) ≤ (984112037039/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33587/262144 : ℝ)) (492056018519/500000000000 : ℝ) (984112037039/1000000000000 : ℝ) (17754858083/100000000000 : ℝ) (177548580837/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33587/262144 : ℝ)) (492056018519/500000000000 : ℝ) (984112037039/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492056018519/500000000000 : ℝ) (984112037039/1000000000000 : ℝ) (992056018519/1000000000000 : ℝ) (24801400463/25000000000 : ℝ) (992024211921/1000000000000 : ℝ) (496012105961/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 1 (992056018519/1000000000000 : ℝ) (24801400463/25000000000 : ℝ) (992024211921/1000000000000 : ℝ) (496012105961/500000000000 : ℝ) (49602005761/50000000000 : ℝ) (992040115221/1000000000000 : ℝ) (248010028773/250000000000 : ℝ) (496020057547/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 2 (49602005761/50000000000 : ℝ) (992040115221/1000000000000 : ℝ) (248010028773/250000000000 : ℝ) (496020057547/500000000000 : ℝ) (248010028789/250000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 3 (248010028789/250000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 4 (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 5 (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 6 (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33587/262144 : ℝ)) 7 (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33587/262144 : ℝ))) (17754858083/100000000000 : ℝ) (177548580837/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17754858083/100000000000 : ℝ) (177548580837/1000000000000 : ℝ) (117754858083/200000000000 : ℝ) (588774290419/1000000000000 : ℝ) (13167660611/31250000000 : ℝ) (421365139561/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 1 (117754858083/200000000000 : ℝ) (588774290419/1000000000000 : ℝ) (13167660611/31250000000 : ℝ) (421365139561/1000000000000 : ℝ) (505069714983/1000000000000 : ℝ) (50506971499/100000000000 : ℝ) (498085294949/1000000000000 : ℝ) (498085294957/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 2 (505069714983/1000000000000 : ℝ) (50506971499/100000000000 : ℝ) (498085294949/1000000000000 : ℝ) (498085294957/1000000000000 : ℝ) (250788752483/500000000000 : ℝ) (250788752487/500000000000 : ℝ) (501565347643/1000000000000 : ℝ) (125391336913/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 3 (250788752483/500000000000 : ℝ) (250788752487/500000000000 : ℝ) (501565347643/1000000000000 : ℝ) (125391336913/250000000000 : ℝ) (244907923/488281250 : ℝ) (501571426313/1000000000000 : ℝ) (501571426267/1000000000000 : ℝ) (501571426277/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 4 (244907923/488281250 : ℝ) (501571426313/1000000000000 : ℝ) (501571426267/1000000000000 : ℝ) (501571426277/1000000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 5 (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 6 (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33587/262144 : ℝ))) 7 (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33587/262144 : ℝ)) hmem 8 (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33587/262144 : ℝ))) hcmem 8 (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33587/262144 : ℝ)) (198408023031/200000000000 : ℝ) (496020057579/500000000000 : ℝ) (100314285257/200000000000 : ℝ) (100314285259/200000000000 : ℝ) (794188200653/1000000000000 : ℝ) (794188200673/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1101_exp_lower
  have heNumeric : (2054902682047/1000000000000 : ℝ)/4 ≤ Real.exp (-85256431483019/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902682047/1000000000000 : ℝ)/4 ≤ Real.exp ((67173/524288 : ℝ)-(794188200673/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67173/524288 : ℝ) (33587/262144 : ℝ) (794188200673/1000000000000 : ℝ) (2054902682047/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1102; no trusted numerical premise.
theorem cover8_leaf1102_exp_radius : (199600006320190317/200000000000000000 : ℝ) ≤ Real.exp ((-67175/4194304 : ℝ)/8) ∧ Real.exp ((-67175/4194304 : ℝ)/8) ≤ (499000015800475793/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67175/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1102_exp_lower : (460056756300213161/500000000000000000 : ℝ) ≤ Real.exp ((-42628215443869/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628215443869/64000000000000 : ℝ)/8) ≤ (920113512600426323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628215443869/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1102_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902691603/1000000000000 : ℝ) ≤ 4*Real.exp (33587/262144 : ℝ)*Real.exp (-mu (radius 8 (67175/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902691603/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67175/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1102_exp_radius
  have hrNumeric : (984111802407/1000000000000 : ℝ) ≤ Real.exp (-67175/4194304 : ℝ) ∧ Real.exp (-67175/4194304 : ℝ) ≤ (123013975301/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984111802407/1000000000000 : ℝ) ≤ (radius 8 (67175/524288 : ℝ)) ∧ (radius 8 (67175/524288 : ℝ)) ≤ (123013975301/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67175/524288 : ℝ)) (984111802407/1000000000000 : ℝ) (123013975301/125000000000 : ℝ) (44387470333/250000000000 : ℝ) (177549881339/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67175/524288 : ℝ)) (984111802407/1000000000000 : ℝ) (123013975301/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984111802407/1000000000000 : ℝ) (123013975301/125000000000 : ℝ) (992055901203/1000000000000 : ℝ) (248013975301/250000000000 : ℝ) (496012046831/500000000000 : ℝ) (31000752927/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 1 (992055901203/1000000000000 : ℝ) (248013975301/250000000000 : ℝ) (496012046831/500000000000 : ℝ) (31000752927/31250000000 : ℝ) (124004999679/125000000000 : ℝ) (496019998717/500000000000 : ℝ) (198407999461/200000000000 : ℝ) (992039997307/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 2 (124004999679/125000000000 : ℝ) (496019998717/500000000000 : ℝ) (198407999461/200000000000 : ℝ) (992039997307/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 3 (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 4 (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 5 (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 6 (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67175/524288 : ℝ)) 7 (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67175/524288 : ℝ))) (44387470333/250000000000 : ℝ) (177549881339/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44387470333/250000000000 : ℝ) (177549881339/1000000000000 : ℝ) (294387470333/500000000000 : ℝ) (58877494067/100000000000 : ℝ) (1685466731/4000000000 : ℝ) (421366682759/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 1 (294387470333/500000000000 : ℝ) (58877494067/100000000000 : ℝ) (1685466731/4000000000 : ℝ) (421366682759/1000000000000 : ℝ) (126267702927/250000000000 : ℝ) (101014162343/200000000000 : ℝ) (498086482083/1000000000000 : ℝ) (498086482091/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 2 (126267702927/250000000000 : ℝ) (101014162343/200000000000 : ℝ) (498086482083/1000000000000 : ℝ) (498086482091/1000000000000 : ℝ) (100315729379/200000000000 : ℝ) (501578646903/1000000000000 : ℝ) (100313297983/200000000000 : ℝ) (125391622481/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 3 (100315729379/200000000000 : ℝ) (501578646903/1000000000000 : ℝ) (100313297983/200000000000 : ℝ) (125391622481/250000000000 : ℝ) (100314513681/200000000000 : ℝ) (250786284207/500000000000 : ℝ) (31348285523/62500000000 : ℝ) (501572568377/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 4 (100314513681/200000000000 : ℝ) (250786284207/500000000000 : ℝ) (31348285523/62500000000 : ℝ) (501572568377/1000000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 5 (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 6 (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67175/524288 : ℝ))) 7 (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67175/524288 : ℝ)) hmem 8 (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67175/524288 : ℝ))) hcmem 8 (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67175/524288 : ℝ)) (124004999671/125000000000 : ℝ) (992039997371/1000000000000 : ℝ) (250786284193/500000000000 : ℝ) (125393142099/250000000000 : ℝ) (99273762919/125000000000 : ℝ) (794190103371/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1102_exp_lower
  have heNumeric : (2054902691603/1000000000000 : ℝ)/4 ≤ Real.exp (-42628215443869/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902691603/1000000000000 : ℝ)/4 ≤ Real.exp ((33587/262144 : ℝ)-(794190103371/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33587/262144 : ℝ) (67175/524288 : ℝ) (794190103371/1000000000000 : ℝ) (2054902691603/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1103; no trusted numerical premise.
theorem cover8_leaf1103_exp_radius : (974609376814681/976562500000000 : ℝ) ≤ Real.exp ((-8397/524288 : ℝ)/8) ∧ Real.exp ((-8397/524288 : ℝ)/8) ≤ (199600000371646669/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8397/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1103_exp_lower : (230028378284576363/250000000000000000 : ℝ) ≤ Real.exp ((-85256430289129/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256430289129/128000000000000 : ℝ)/8) ≤ (920113513138305453/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256430289129/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1103_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902701213/1000000000000 : ℝ) ≤ 4*Real.exp (67175/524288 : ℝ)*Real.exp (-mu (radius 8 (8397/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902701213/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8397/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1103_exp_radius
  have hrNumeric : (984111567777/1000000000000 : ℝ) ≤ Real.exp (-8397/524288 : ℝ) ∧ Real.exp (-8397/524288 : ℝ) ≤ (492055783889/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984111567777/1000000000000 : ℝ) ≤ (radius 8 (8397/65536 : ℝ)) ∧ (radius 8 (8397/65536 : ℝ)) ≤ (492055783889/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8397/65536 : ℝ)) (984111567777/1000000000000 : ℝ) (492055783889/500000000000 : ℝ) (177551181819/1000000000000 : ℝ) (88775590913/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8397/65536 : ℝ)) (984111567777/1000000000000 : ℝ) (492055783889/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984111567777/1000000000000 : ℝ) (492055783889/500000000000 : ℝ) (62003486493/62500000000 : ℝ) (992055783889/1000000000000 : ℝ) (248005993851/250000000000 : ℝ) (198404795081/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 1 (62003486493/62500000000 : ℝ) (992055783889/1000000000000 : ℝ) (248005993851/250000000000 : ℝ) (198404795081/200000000000 : ℝ) (496019939823/500000000000 : ℝ) (992039879647/1000000000000 : ℝ) (496019939759/500000000000 : ℝ) (6200249247/6250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 2 (496019939823/500000000000 : ℝ) (992039879647/1000000000000 : ℝ) (496019939759/500000000000 : ℝ) (6200249247/6250000000 : ℝ) (496019939791/500000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 3 (496019939791/500000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 4 (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 5 (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 6 (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8397/65536 : ℝ)) 7 (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8397/65536 : ℝ))) (177551181819/1000000000000 : ℝ) (88775590913/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177551181819/1000000000000 : ℝ) (88775590913/500000000000 : ℝ) (588775590909/1000000000000 : ℝ) (588775590913/1000000000000 : ℝ) (105342056481/250000000000 : ℝ) (210684112967/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 1 (588775590909/1000000000000 : ℝ) (588775590913/1000000000000 : ℝ) (105342056481/250000000000 : ℝ) (210684112967/500000000000 : ℝ) (7891748569/15625000000 : ℝ) (63133988553/125000000000 : ℝ) (498087669199/1000000000000 : ℝ) (62260958651/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 2 (7891748569/15625000000 : ℝ) (63133988553/125000000000 : ℝ) (498087669199/1000000000000 : ℝ) (62260958651/125000000000 : ℝ) (501579788807/1000000000000 : ℝ) (31348736801/62500000000 : ℝ) (50156763217/100000000000 : ℝ) (501567632179/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 3 (501579788807/1000000000000 : ℝ) (31348736801/62500000000 : ℝ) (50156763217/100000000000 : ℝ) (501567632179/1000000000000 : ℝ) (62696713811/125000000000 : ℝ) (250786855249/500000000000 : ℝ) (501573710451/1000000000000 : ℝ) (501573710461/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 4 (62696713811/125000000000 : ℝ) (250786855249/500000000000 : ℝ) (501573710451/1000000000000 : ℝ) (501573710461/1000000000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 5 (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 6 (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8397/65536 : ℝ))) 7 (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8397/65536 : ℝ)) hmem 8 (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8397/65536 : ℝ))) hcmem 8 (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8397/65536 : ℝ)) (992039879581/1000000000000 : ℝ) (31001246237/31250000000 : ℝ) (501573710469/1000000000000 : ℝ) (6269671381/12500000000 : ℝ) (397096003011/500000000000 : ℝ) (794192006043/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1103_exp_lower
  have heNumeric : (2054902701213/1000000000000 : ℝ)/4 ≤ Real.exp (-85256430289129/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902701213/1000000000000 : ℝ)/4 ≤ Real.exp ((67175/524288 : ℝ)-(794192006043/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67175/524288 : ℝ) (8397/65536 : ℝ) (794192006043/1000000000000 : ℝ) (2054902701213/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1104; no trusted numerical premise.
theorem cover8_leaf1104_exp_radius : (997999972115515989/1000000000000000000 : ℝ) ≤ Real.exp ((-67177/4194304 : ℝ)/8) ∧ Real.exp ((-67177/4194304 : ℝ)/8) ≤ (99799997211551599/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67177/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1104_exp_lower : (115014189209709971/125000000000000000 : ℝ) ≤ Real.exp ((-10657053711107/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657053711107/16000000000000 : ℝ)/8) ≤ (920113513677679769/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657053711107/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1104_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098054217/20000000000 : ℝ) ≤ 4*Real.exp (8397/65536 : ℝ)*Real.exp (-mu (radius 8 (67177/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (41098054217/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67177/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1104_exp_radius
  have hrNumeric : (492055666573/500000000000 : ℝ) ≤ Real.exp (-67177/4194304 : ℝ) ∧ Real.exp (-67177/4194304 : ℝ) ≤ (984111333147/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492055666573/500000000000 : ℝ) ≤ (radius 8 (67177/524288 : ℝ)) ∧ (radius 8 (67177/524288 : ℝ)) ≤ (984111333147/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67177/524288 : ℝ)) (492055666573/500000000000 : ℝ) (984111333147/1000000000000 : ℝ) (88776241151/500000000000 : ℝ) (44388120577/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67177/524288 : ℝ)) (492055666573/500000000000 : ℝ) (984111333147/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492055666573/500000000000 : ℝ) (984111333147/1000000000000 : ℝ) (992055666573/1000000000000 : ℝ) (496027833287/500000000000 : ℝ) (198404771429/200000000000 : ℝ) (992023857147/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 1 (992055666573/1000000000000 : ℝ) (496027833287/500000000000 : ℝ) (198404771429/200000000000 : ℝ) (992023857147/1000000000000 : ℝ) (992039761859/1000000000000 : ℝ) (992039761861/1000000000000 : ℝ) (992039761731/1000000000000 : ℝ) (496019880867/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 2 (992039761859/1000000000000 : ℝ) (992039761861/1000000000000 : ℝ) (992039761731/1000000000000 : ℝ) (496019880867/500000000000 : ℝ) (198407952359/200000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 3 (198407952359/200000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 4 (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 5 (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 6 (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67177/524288 : ℝ)) 7 (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67177/524288 : ℝ))) (88776241151/500000000000 : ℝ) (44388120577/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88776241151/500000000000 : ℝ) (44388120577/250000000000 : ℝ) (588776241151/1000000000000 : ℝ) (294388120577/500000000000 : ℝ) (3291951321/7812500000 : ℝ) (52671221137/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 1 (588776241151/1000000000000 : ℝ) (294388120577/500000000000 : ℝ) (3291951321/7812500000 : ℝ) (52671221137/125000000000 : ℝ) (505073005119/1000000000000 : ℝ) (4040584041/8000000000 : ℝ) (124522214077/250000000000 : ℝ) (99617771263/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 2 (505073005119/1000000000000 : ℝ) (4040584041/8000000000 : ℝ) (124522214077/250000000000 : ℝ) (99617771263/200000000000 : ℝ) (501580930713/1000000000000 : ℝ) (3134880817/6250000000 : ℝ) (250784387209/500000000000 : ℝ) (250784387213/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 3 (501580930713/1000000000000 : ℝ) (3134880817/6250000000 : ℝ) (250784387209/500000000000 : ℝ) (250784387213/500000000000 : ℝ) (100314970513/200000000000 : ℝ) (501574852573/1000000000000 : ℝ) (31348428283/62500000000 : ℝ) (501574852537/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 4 (100314970513/200000000000 : ℝ) (501574852573/1000000000000 : ℝ) (31348428283/62500000000 : ℝ) (501574852537/1000000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 5 (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 6 (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67177/524288 : ℝ))) 7 (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67177/524288 : ℝ)) hmem 8 (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67177/524288 : ℝ))) hcmem 8 (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67177/524288 : ℝ)) (496019880897/500000000000 : ℝ) (496019880899/500000000000 : ℝ) (250787426273/500000000000 : ℝ) (100314970511/200000000000 : ℝ) (794193908683/1000000000000 : ℝ) (397096954351/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1104_exp_lower
  have heNumeric : (41098054217/20000000000 : ℝ)/4 ≤ Real.exp (-10657053711107/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098054217/20000000000 : ℝ)/4 ≤ Real.exp ((8397/65536 : ℝ)-(397096954351/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8397/65536 : ℝ) (67177/524288 : ℝ) (397096954351/500000000000 : ℝ) (41098054217/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1105; no trusted numerical premise.
theorem cover8_leaf1105_exp_radius : (6237499639829997/6250000000000000 : ℝ) ≤ Real.exp ((-33589/2097152 : ℝ)/8) ∧ Real.exp ((-33589/2097152 : ℝ)/8) ≤ (997999942372799521/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33589/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1105_exp_lower : (115014189277476803/125000000000000000 : ℝ) ≤ Real.exp ((-85256429085511/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256429085511/128000000000000 : ℝ)/8) ≤ (36804540568792577/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256429085511/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1105_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862840067/125000000000 : ℝ) ≤ 4*Real.exp (67177/524288 : ℝ)*Real.exp (-mu (radius 8 (33589/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862840067/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33589/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1105_exp_radius
  have hrNumeric : (246027774629/250000000000 : ℝ) ≤ Real.exp (-33589/2097152 : ℝ) ∧ Real.exp (-33589/2097152 : ℝ) ≤ (984111098517/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246027774629/250000000000 : ℝ) ≤ (radius 8 (33589/262144 : ℝ)) ∧ (radius 8 (33589/262144 : ℝ)) ≤ (984111098517/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33589/262144 : ℝ)) (246027774629/250000000000 : ℝ) (984111098517/1000000000000 : ℝ) (177553782769/1000000000000 : ℝ) (7102151311/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33589/262144 : ℝ)) (246027774629/250000000000 : ℝ) (984111098517/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246027774629/250000000000 : ℝ) (984111098517/1000000000000 : ℝ) (496027774629/500000000000 : ℝ) (992055549259/1000000000000 : ℝ) (992023738887/1000000000000 : ℝ) (124002967361/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 1 (496027774629/500000000000 : ℝ) (992055549259/1000000000000 : ℝ) (992023738887/1000000000000 : ℝ) (124002967361/125000000000 : ℝ) (124004955509/125000000000 : ℝ) (496019822037/500000000000 : ℝ) (124004955493/125000000000 : ℝ) (496019821973/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 2 (124004955509/125000000000 : ℝ) (496019822037/500000000000 : ℝ) (124004955493/125000000000 : ℝ) (496019821973/500000000000 : ℝ) (124004955501/125000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 3 (124004955501/125000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 4 (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 5 (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 6 (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33589/262144 : ℝ)) 7 (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33589/262144 : ℝ))) (177553782769/1000000000000 : ℝ) (7102151311/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177553782769/1000000000000 : ℝ) (7102151311/40000000000 : ℝ) (73597111423/125000000000 : ℝ) (147194222847/250000000000 : ℝ) (105342828057/250000000000 : ℝ) (105342828059/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 1 (73597111423/125000000000 : ℝ) (147194222847/250000000000 : ℝ) (105342828057/250000000000 : ℝ) (105342828059/250000000000 : ℝ) (252537050903/500000000000 : ℝ) (126268525453/250000000000 : ℝ) (498090043397/1000000000000 : ℝ) (99618008681/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 2 (252537050903/500000000000 : ℝ) (126268525453/250000000000 : ℝ) (498090043397/1000000000000 : ℝ) (99618008681/200000000000 : ℝ) (501582072601/1000000000000 : ℝ) (501582072609/1000000000000 : ℝ) (62696239581/125000000000 : ℝ) (31348119791/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 3 (501582072601/1000000000000 : ℝ) (501582072609/1000000000000 : ℝ) (62696239581/125000000000 : ℝ) (31348119791/62500000000 : ℝ) (1959281229/3906250000 : ℝ) (501575994633/1000000000000 : ℝ) (501575994587/1000000000000 : ℝ) (125393998649/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 4 (1959281229/3906250000 : ℝ) (501575994633/1000000000000 : ℝ) (501575994587/1000000000000 : ℝ) (125393998649/250000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 5 (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 6 (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33589/262144 : ℝ))) 7 (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33589/262144 : ℝ)) hmem 8 (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33589/262144 : ℝ))) hcmem 8 (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33589/262144 : ℝ)) (992039644007/1000000000000 : ℝ) (99203964401/100000000000 : ℝ) (100315198921/200000000000 : ℝ) (100315198923/200000000000 : ℝ) (794195811317/1000000000000 : ℝ) (794195811337/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1105_exp_lower
  have heNumeric : (256862840067/125000000000 : ℝ)/4 ≤ Real.exp (-85256429085511/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862840067/125000000000 : ℝ)/4 ≤ Real.exp ((67177/524288 : ℝ)-(794195811337/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67177/524288 : ℝ) (33589/262144 : ℝ) (794195811337/1000000000000 : ℝ) (256862840067/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1106; no trusted numerical premise.
theorem cover8_leaf1106_exp_radius : (498999956315041969/500000000000000000 : ℝ) ≤ Real.exp ((-67179/4194304 : ℝ)/8) ∧ Real.exp ((-67179/4194304 : ℝ)/8) ≤ (997999912630083939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67179/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1106_exp_lower : (920113514764364379/1000000000000000000 : ℝ) ≤ Real.exp ((-42628214239739/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628214239739/64000000000000 : ℝ)/8) ≤ (46005675738218219/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628214239739/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1106_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980546053/200000000000 : ℝ) ≤ 4*Real.exp (33589/262144 : ℝ)*Real.exp (-mu (radius 8 (67179/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980546053/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67179/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1106_exp_radius
  have hrNumeric : (492055431943/500000000000 : ℝ) ≤ Real.exp (-67179/4194304 : ℝ) ∧ Real.exp (-67179/4194304 : ℝ) ≤ (984110863887/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492055431943/500000000000 : ℝ) ≤ (radius 8 (67179/524288 : ℝ)) ∧ (radius 8 (67179/524288 : ℝ)) ≤ (984110863887/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67179/524288 : ℝ)) (492055431943/500000000000 : ℝ) (984110863887/1000000000000 : ℝ) (88777541613/500000000000 : ℝ) (177555083233/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67179/524288 : ℝ)) (492055431943/500000000000 : ℝ) (984110863887/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492055431943/500000000000 : ℝ) (984110863887/1000000000000 : ℝ) (992055431943/1000000000000 : ℝ) (124006928993/125000000000 : ℝ) (992023620629/1000000000000 : ℝ) (99202362063/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 1 (992055431943/1000000000000 : ℝ) (124006928993/125000000000 : ℝ) (992023620629/1000000000000 : ℝ) (99202362063/100000000000 : ℝ) (496019763143/500000000000 : ℝ) (992039526287/1000000000000 : ℝ) (496019763079/500000000000 : ℝ) (12400494077/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 2 (496019763143/500000000000 : ℝ) (992039526287/1000000000000 : ℝ) (496019763079/500000000000 : ℝ) (12400494077/12500000000 : ℝ) (496019763111/500000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 3 (496019763111/500000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 4 (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 5 (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 6 (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67179/524288 : ℝ)) 7 (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67179/524288 : ℝ))) (88777541613/500000000000 : ℝ) (177555083233/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88777541613/500000000000 : ℝ) (177555083233/1000000000000 : ℝ) (588777541613/1000000000000 : ℝ) (588777541617/1000000000000 : ℝ) (8427457107/20000000000 : ℝ) (421372855359/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 1 (588777541613/1000000000000 : ℝ) (588777541617/1000000000000 : ℝ) (8427457107/20000000000 : ℝ) (421372855359/1000000000000 : ℝ) (505075198481/1000000000000 : ℝ) (63134399811/125000000000 : ℝ) (249045615237/500000000000 : ℝ) (249045615241/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 2 (505075198481/1000000000000 : ℝ) (63134399811/125000000000 : ℝ) (249045615237/500000000000 : ℝ) (249045615241/500000000000 : ℝ) (501583214477/1000000000000 : ℝ) (100316642897/200000000000 : ℝ) (501571058867/1000000000000 : ℝ) (4012568471/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 3 (501583214477/1000000000000 : ℝ) (100316642897/200000000000 : ℝ) (501571058867/1000000000000 : ℝ) (4012568471/8000000000 : ℝ) (15674285521/31250000000 : ℝ) (12539428417/25000000000 : ℝ) (100315427327/200000000000 : ℝ) (125394284161/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 4 (15674285521/31250000000 : ℝ) (12539428417/25000000000 : ℝ) (100315427327/200000000000 : ℝ) (125394284161/250000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 5 (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 6 (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67179/524288 : ℝ))) 7 (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67179/524288 : ℝ)) hmem 8 (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67179/524288 : ℝ))) hcmem 8 (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67179/524288 : ℝ)) (992039526221/1000000000000 : ℝ) (62002470389/62500000000 : ℝ) (501577136653/1000000000000 : ℝ) (250788568331/500000000000 : ℝ) (794197713933/1000000000000 : ℝ) (794197713951/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1106_exp_lower
  have heNumeric : (410980546053/200000000000 : ℝ)/4 ≤ Real.exp (-42628214239739/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980546053/200000000000 : ℝ)/4 ≤ Real.exp ((33589/262144 : ℝ)-(794197713951/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33589/262144 : ℝ) (67179/524288 : ℝ) (794197713951/1000000000000 : ℝ) (410980546053/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1107; no trusted numerical premise.
theorem cover8_leaf1107_exp_radius : (498999941443684621/500000000000000000 : ℝ) ≤ Real.exp ((-16795/1048576 : ℝ)/8) ∧ Real.exp ((-16795/1048576 : ℝ)/8) ≤ (997999882887369243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16795/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1107_exp_lower : (920113515309949461/1000000000000000000 : ℝ) ≤ Real.exp ((-85256427872293/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256427872293/128000000000000 : ℝ)/8) ≤ (460056757654974731/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256427872293/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1107_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902740013/1000000000000 : ℝ) ≤ 4*Real.exp (67179/524288 : ℝ)*Real.exp (-mu (radius 8 (16795/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902740013/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16795/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1107_exp_radius
  have hrNumeric : (196822125851/200000000000 : ℝ) ≤ Real.exp (-16795/1048576 : ℝ) ∧ Real.exp (-16795/1048576 : ℝ) ≤ (123013828657/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196822125851/200000000000 : ℝ) ≤ (radius 8 (16795/131072 : ℝ)) ∧ (radius 8 (16795/131072 : ℝ)) ≤ (123013828657/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16795/131072 : ℝ)) (196822125851/200000000000 : ℝ) (123013828657/125000000000 : ℝ) (177556383679/1000000000000 : ℝ) (88778191843/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16795/131072 : ℝ)) (196822125851/200000000000 : ℝ) (123013828657/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196822125851/200000000000 : ℝ) (123013828657/125000000000 : ℝ) (992055314627/1000000000000 : ℝ) (248013828657/250000000000 : ℝ) (99202350237/100000000000 : ℝ) (992023502371/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 1 (992055314627/1000000000000 : ℝ) (248013828657/250000000000 : ℝ) (99202350237/100000000000 : ℝ) (992023502371/1000000000000 : ℝ) (496019704249/500000000000 : ℝ) (1984078817/2000000000 : ℝ) (99203940837/100000000000 : ℝ) (248009852093/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 2 (496019704249/500000000000 : ℝ) (1984078817/2000000000 : ℝ) (99203940837/100000000000 : ℝ) (248009852093/250000000000 : ℝ) (496019704217/500000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 3 (496019704217/500000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 4 (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 5 (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 6 (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16795/131072 : ℝ)) 7 (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16795/131072 : ℝ))) (177556383679/1000000000000 : ℝ) (88778191843/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177556383679/1000000000000 : ℝ) (88778191843/500000000000 : ℝ) (588778191839/1000000000000 : ℝ) (588778191843/1000000000000 : ℝ) (421374398461/1000000000000 : ℝ) (421374398471/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 1 (588778191839/1000000000000 : ℝ) (588778191843/1000000000000 : ℝ) (421374398461/1000000000000 : ℝ) (421374398471/1000000000000 : ℝ) (10101525903/20000000000 : ℝ) (505076295157/1000000000000 : ℝ) (249046208771/500000000000 : ℝ) (9961848351/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 2 (10101525903/20000000000 : ℝ) (505076295157/1000000000000 : ℝ) (249046208771/500000000000 : ℝ) (9961848351/20000000000 : ℝ) (250792178173/500000000000 : ℝ) (250792178177/500000000000 : ℝ) (250786100539/500000000000 : ℝ) (250786100543/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 3 (250792178173/500000000000 : ℝ) (250792178177/500000000000 : ℝ) (250786100539/500000000000 : ℝ) (250786100543/500000000000 : ℝ) (62697284839/125000000000 : ℝ) (1567432121/3125000000 : ℝ) (20063131147/40000000000 : ℝ) (125394569671/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 4 (62697284839/125000000000 : ℝ) (1567432121/3125000000 : ℝ) (20063131147/40000000000 : ℝ) (125394569671/250000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 5 (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 6 (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16795/131072 : ℝ))) 7 (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16795/131072 : ℝ)) hmem 8 (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16795/131072 : ℝ))) hcmem 8 (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16795/131072 : ℝ)) (992039408433/1000000000000 : ℝ) (248009852109/250000000000 : ℝ) (501578278693/1000000000000 : ℝ) (250789139351/500000000000 : ℝ) (397099808269/500000000000 : ℝ) (198549904139/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1107_exp_lower
  have heNumeric : (2054902740013/1000000000000 : ℝ)/4 ≤ Real.exp (-85256427872293/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902740013/1000000000000 : ℝ)/4 ≤ Real.exp ((67179/524288 : ℝ)-(198549904139/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67179/524288 : ℝ) (16795/131072 : ℝ) (198549904139/250000000000 : ℝ) (2054902740013/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1108; no trusted numerical premise.
theorem cover8_leaf1108_exp_radius : (124749981643081929/125000000000000000 : ℝ) ≤ Real.exp ((-67181/4194304 : ℝ)/8) ∧ Real.exp ((-67181/4194304 : ℝ)/8) ≤ (997999853144655433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67181/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1108_exp_lower : (920113515858639927/1000000000000000000 : ℝ) ≤ Real.exp ((-21314106815413/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314106815413/32000000000000 : ℝ)/8) ≤ (115014189482329991/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314106815413/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1108_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862843727/125000000000 : ℝ) ≤ 4*Real.exp (16795/131072 : ℝ)*Real.exp (-mu (radius 8 (67181/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862843727/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67181/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1108_exp_radius
  have hrNumeric : (7872883157/8000000000 : ℝ) ≤ Real.exp (-67181/4194304 : ℝ) ∧ Real.exp (-67181/4194304 : ℝ) ≤ (492055197313/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7872883157/8000000000 : ℝ) ≤ (radius 8 (67181/524288 : ℝ)) ∧ (radius 8 (67181/524288 : ℝ)) ≤ (492055197313/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67181/524288 : ℝ)) (7872883157/8000000000 : ℝ) (492055197313/500000000000 : ℝ) (177557684117/1000000000000 : ℝ) (177557684123/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67181/524288 : ℝ)) (7872883157/8000000000 : ℝ) (492055197313/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7872883157/8000000000 : ℝ) (492055197313/500000000000 : ℝ) (7750431229/7812500000 : ℝ) (992055197313/1000000000000 : ℝ) (992023384111/1000000000000 : ℝ) (992023384113/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 1 (7750431229/7812500000 : ℝ) (992055197313/1000000000000 : ℝ) (992023384111/1000000000000 : ℝ) (992023384113/1000000000000 : ℝ) (992039290711/1000000000000 : ℝ) (992039290713/1000000000000 : ℝ) (992039290583/1000000000000 : ℝ) (496019645293/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 2 (992039290711/1000000000000 : ℝ) (992039290713/1000000000000 : ℝ) (992039290583/1000000000000 : ℝ) (496019645293/500000000000 : ℝ) (992039290647/1000000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 3 (992039290647/1000000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 4 (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 5 (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 6 (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67181/524288 : ℝ)) 7 (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67181/524288 : ℝ))) (177557684117/1000000000000 : ℝ) (177557684123/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177557684117/1000000000000 : ℝ) (177557684123/1000000000000 : ℝ) (294389421029/500000000000 : ℝ) (294389421031/500000000000 : ℝ) (421375941549/1000000000000 : ℝ) (421375941557/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 1 (294389421029/500000000000 : ℝ) (294389421031/500000000000 : ℝ) (421375941549/1000000000000 : ℝ) (421375941557/1000000000000 : ℝ) (505077391803/1000000000000 : ℝ) (50507739181/100000000000 : ℝ) (31130850287/62500000000 : ℝ) (2490468023/5000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 2 (505077391803/1000000000000 : ℝ) (50507739181/100000000000 : ℝ) (31130850287/62500000000 : ℝ) (2490468023/5000000000 : ℝ) (501585498197/1000000000000 : ℝ) (100317099641/200000000000 : ℝ) (62696667909/125000000000 : ℝ) (6269666791/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 3 (501585498197/1000000000000 : ℝ) (100317099641/200000000000 : ℝ) (62696667909/125000000000 : ℝ) (6269666791/12500000000 : ℝ) (250789710367/500000000000 : ℝ) (501579420743/1000000000000 : ℝ) (501579420697/1000000000000 : ℝ) (250789710353/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 4 (250789710367/500000000000 : ℝ) (501579420743/1000000000000 : ℝ) (501579420697/1000000000000 : ℝ) (250789710353/500000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 5 (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 6 (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67181/524288 : ℝ))) 7 (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67181/524288 : ℝ)) hmem 8 (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67181/524288 : ℝ))) hcmem 8 (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67181/524288 : ℝ)) (496019645323/500000000000 : ℝ) (19840785813/20000000000 : ℝ) (100315884143/200000000000 : ℝ) (20063176829/40000000000 : ℝ) (397100759557/500000000000 : ℝ) (397100759567/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1108_exp_lower
  have heNumeric : (256862843727/125000000000 : ℝ)/4 ≤ Real.exp (-21314106815413/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862843727/125000000000 : ℝ)/4 ≤ Real.exp ((16795/131072 : ℝ)-(397100759567/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16795/131072 : ℝ) (67181/524288 : ℝ) (397100759567/500000000000 : ℝ) (256862843727/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1109; no trusted numerical premise.
theorem cover8_leaf1109_exp_radius : (997999823401942509/1000000000000000000 : ℝ) ≤ Real.exp ((-33591/2097152 : ℝ)/8) ∧ Real.exp ((-33591/2097152 : ℝ)/8) ≤ (99799982340194251/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33591/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1109_exp_lower : (460056758204815339/500000000000000000 : ℝ) ≤ Real.exp ((-85256426648451/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256426648451/128000000000000 : ℝ)/8) ≤ (920113516409630679/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256426648451/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1109_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902759661/1000000000000 : ℝ) ≤ 4*Real.exp (67181/524288 : ℝ)*Real.exp (-mu (radius 8 (33591/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902759661/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33591/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1109_exp_radius
  have hrNumeric : (196822031999/200000000000 : ℝ) ≤ Real.exp (-33591/2097152 : ℝ) ∧ Real.exp (-33591/2097152 : ℝ) ≤ (246027539999/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196822031999/200000000000 : ℝ) ≤ (radius 8 (33591/262144 : ℝ)) ∧ (radius 8 (33591/262144 : ℝ)) ≤ (246027539999/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33591/262144 : ℝ)) (196822031999/200000000000 : ℝ) (246027539999/250000000000 : ℝ) (5548718267/31250000000 : ℝ) (177558984551/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33591/262144 : ℝ)) (196822031999/200000000000 : ℝ) (246027539999/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196822031999/200000000000 : ℝ) (246027539999/250000000000 : ℝ) (992055079997/1000000000000 : ℝ) (496027539999/500000000000 : ℝ) (992023265853/1000000000000 : ℝ) (198404653171/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 1 (992055079997/1000000000000 : ℝ) (496027539999/500000000000 : ℝ) (992023265853/1000000000000 : ℝ) (198404653171/200000000000 : ℝ) (39681566917/40000000000 : ℝ) (992039172927/1000000000000 : ℝ) (992039172797/1000000000000 : ℝ) (992039172799/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 2 (39681566917/40000000000 : ℝ) (992039172927/1000000000000 : ℝ) (992039172797/1000000000000 : ℝ) (992039172799/1000000000000 : ℝ) (992039172861/1000000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 3 (992039172861/1000000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 4 (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 5 (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 6 (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33591/262144 : ℝ)) 7 (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33591/262144 : ℝ))) (5548718267/31250000000 : ℝ) (177558984551/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5548718267/31250000000 : ℝ) (177558984551/1000000000000 : ℝ) (36798718267/62500000000 : ℝ) (147194873069/250000000000 : ℝ) (421377484619/1000000000000 : ℝ) (105344371157/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 1 (36798718267/62500000000 : ℝ) (147194873069/250000000000 : ℝ) (421377484619/1000000000000 : ℝ) (105344371157/250000000000 : ℝ) (101015697689/200000000000 : ℝ) (126269622113/250000000000 : ℝ) (498094791629/1000000000000 : ℝ) (498094791637/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 2 (101015697689/200000000000 : ℝ) (126269622113/250000000000 : ℝ) (498094791629/1000000000000 : ℝ) (498094791637/1000000000000 : ℝ) (501586640037/1000000000000 : ℝ) (100317328009/200000000000 : ℝ) (501574485453/1000000000000 : ℝ) (250787242731/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 3 (501586640037/1000000000000 : ℝ) (100317328009/200000000000 : ℝ) (501574485453/1000000000000 : ℝ) (250787242731/500000000000 : ℝ) (100316112549/200000000000 : ℝ) (250790281377/500000000000 : ℝ) (125395140677/250000000000 : ℝ) (501580562717/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 4 (100316112549/200000000000 : ℝ) (250790281377/500000000000 : ℝ) (125395140677/250000000000 : ℝ) (501580562717/1000000000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 5 (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 6 (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33591/262144 : ℝ))) 7 (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33591/262144 : ℝ)) hmem 8 (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33591/262144 : ℝ))) hcmem 8 (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33591/262144 : ℝ)) (49601958643/50000000000 : ℝ) (992039172863/1000000000000 : ℝ) (250790281363/500000000000 : ℝ) (31348785171/62500000000 : ℝ) (794203421673/1000000000000 : ℝ) (198550855423/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1109_exp_lower
  have heNumeric : (2054902759661/1000000000000 : ℝ)/4 ≤ Real.exp (-85256426648451/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902759661/1000000000000 : ℝ)/4 ≤ Real.exp ((67181/524288 : ℝ)-(198550855423/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67181/524288 : ℝ) (33591/262144 : ℝ) (198550855423/250000000000 : ℝ) (2054902759661/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1110; no trusted numerical premise.
theorem cover8_leaf1110_exp_radius : (997999793659230473/1000000000000000000 : ℝ) ≤ Real.exp ((-67183/4194304 : ℝ)/8) ∧ Real.exp ((-67183/4194304 : ℝ)/8) ≤ (498999896829615237/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67183/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1110_exp_lower : (460056758481403349/500000000000000000 : ℝ) ≤ Real.exp ((-42628213016409/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628213016409/64000000000000 : ℝ)/8) ≤ (920113516962806699/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628213016409/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1110_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862846193/125000000000 : ℝ) ≤ 4*Real.exp (33591/262144 : ℝ)*Real.exp (-mu (radius 8 (67183/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862846193/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67183/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1110_exp_radius
  have hrNumeric : (196821985073/200000000000 : ℝ) ≤ Real.exp (-67183/4194304 : ℝ) ∧ Real.exp (-67183/4194304 : ℝ) ≤ (492054962683/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196821985073/200000000000 : ℝ) ≤ (radius 8 (67183/524288 : ℝ)) ∧ (radius 8 (67183/524288 : ℝ)) ≤ (492054962683/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67183/524288 : ℝ)) (196821985073/200000000000 : ℝ) (492054962683/500000000000 : ℝ) (88780142481/500000000000 : ℝ) (177560284969/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67183/524288 : ℝ)) (196821985073/200000000000 : ℝ) (492054962683/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196821985073/200000000000 : ℝ) (492054962683/500000000000 : ℝ) (496027481341/500000000000 : ℝ) (992054962683/1000000000000 : ℝ) (198404629519/200000000000 : ℝ) (248005786899/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 1 (496027481341/500000000000 : ℝ) (992054962683/1000000000000 : ℝ) (198404629519/200000000000 : ℝ) (248005786899/250000000000 : ℝ) (496019527569/500000000000 : ℝ) (49601952757/50000000000 : ℝ) (99203905501/100000000000 : ℝ) (248009763753/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 2 (496019527569/500000000000 : ℝ) (49601952757/50000000000 : ℝ) (99203905501/100000000000 : ℝ) (248009763753/250000000000 : ℝ) (496019527537/500000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 3 (496019527537/500000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 4 (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 5 (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 6 (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67183/524288 : ℝ)) 7 (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67183/524288 : ℝ))) (88780142481/500000000000 : ℝ) (177560284969/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88780142481/500000000000 : ℝ) (177560284969/1000000000000 : ℝ) (588780142481/1000000000000 : ℝ) (117756028497/200000000000 : ℝ) (52672378459/125000000000 : ℝ) (421379027681/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 1 (588780142481/1000000000000 : ℝ) (117756028497/200000000000 : ℝ) (52672378459/125000000000 : ℝ) (421379027681/1000000000000 : ℝ) (126269896269/250000000000 : ℝ) (505079585083/1000000000000 : ℝ) (498095978653/1000000000000 : ℝ) (498095978661/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 2 (126269896269/250000000000 : ℝ) (505079585083/1000000000000 : ℝ) (498095978653/1000000000000 : ℝ) (498095978661/1000000000000 : ℝ) (62698472733/125000000000 : ℝ) (31349236367/62500000000 : ℝ) (501575627623/1000000000000 : ℝ) (31348476727/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 3 (62698472733/125000000000 : ℝ) (31349236367/62500000000 : ℝ) (501575627623/1000000000000 : ℝ) (31348476727/62500000000 : ℝ) (501581704743/1000000000000 : ℝ) (31348856547/62500000000 : ℝ) (250790852353/500000000000 : ℝ) (125395426179/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 4 (501581704743/1000000000000 : ℝ) (31348856547/62500000000 : ℝ) (250790852353/500000000000 : ℝ) (125395426179/250000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 5 (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 6 (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67183/524288 : ℝ))) 7 (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67183/524288 : ℝ)) hmem 8 (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67183/524288 : ℝ))) hcmem 8 (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67183/524288 : ℝ)) (992039055073/1000000000000 : ℝ) (248009763769/250000000000 : ℝ) (125395426181/250000000000 : ℝ) (250790852367/500000000000 : ℝ) (198551331053/250000000000 : ℝ) (794205324231/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1110_exp_lower
  have heNumeric : (256862846193/125000000000 : ℝ)/4 ≤ Real.exp (-42628213016409/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862846193/125000000000 : ℝ)/4 ≤ Real.exp ((33591/262144 : ℝ)-(794205324231/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33591/262144 : ℝ) (67183/524288 : ℝ) (794205324231/1000000000000 : ℝ) (256862846193/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1111; no trusted numerical premise.
theorem cover8_leaf1111_exp_radius : (498999881958259661/500000000000000000 : ℝ) ≤ Real.exp ((-4199/262144 : ℝ)/8) ∧ Real.exp ((-4199/262144 : ℝ)/8) ≤ (997999763916519323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4199/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1111_exp_lower : (460056758759026487/500000000000000000 : ℝ) ≤ Real.exp ((-85256425414881/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256425414881/128000000000000 : ℝ)/8) ≤ (36804540700722119/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256425414881/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1111_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862847433/125000000000 : ℝ) ≤ 4*Real.exp (67183/524288 : ℝ)*Real.exp (-mu (radius 8 (4199/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (256862847433/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4199/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1111_exp_radius
  have hrNumeric : (196821938147/200000000000 : ℝ) ≤ Real.exp (-4199/262144 : ℝ) ∧ Real.exp (-4199/262144 : ℝ) ≤ (61506855671/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196821938147/200000000000 : ℝ) ≤ (radius 8 (4199/32768 : ℝ)) ∧ (radius 8 (4199/32768 : ℝ)) ≤ (61506855671/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4199/32768 : ℝ)) (196821938147/200000000000 : ℝ) (61506855671/62500000000 : ℝ) (177561585371/1000000000000 : ℝ) (177561585377/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4199/32768 : ℝ)) (196821938147/200000000000 : ℝ) (61506855671/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196821938147/200000000000 : ℝ) (61506855671/62500000000 : ℝ) (992054845367/1000000000000 : ℝ) (124006855671/125000000000 : ℝ) (992023029337/1000000000000 : ℝ) (496011514669/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 1 (992054845367/1000000000000 : ℝ) (124006855671/125000000000 : ℝ) (992023029337/1000000000000 : ℝ) (496011514669/500000000000 : ℝ) (124004867169/125000000000 : ℝ) (992038937353/1000000000000 : ℝ) (124004867153/125000000000 : ℝ) (496019468613/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 2 (124004867169/125000000000 : ℝ) (992038937353/1000000000000 : ℝ) (124004867153/125000000000 : ℝ) (496019468613/500000000000 : ℝ) (124004867161/125000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 3 (124004867161/125000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 4 (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 5 (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 6 (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4199/32768 : ℝ)) 7 (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4199/32768 : ℝ))) (177561585371/1000000000000 : ℝ) (177561585377/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177561585371/1000000000000 : ℝ) (177561585377/1000000000000 : ℝ) (117756158537/200000000000 : ℝ) (588780792689/1000000000000 : ℝ) (105345142677/250000000000 : ℝ) (421380570717/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 1 (117756158537/200000000000 : ℝ) (588780792689/1000000000000 : ℝ) (105345142677/250000000000 : ℝ) (421380570717/1000000000000 : ℝ) (15783771303/31250000000 : ℝ) (505080681703/1000000000000 : ℝ) (99619433133/200000000000 : ℝ) (498097165673/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 2 (15783771303/31250000000 : ℝ) (505080681703/1000000000000 : ℝ) (99619433133/200000000000 : ℝ) (498097165673/1000000000000 : ℝ) (3134930773/6250000000 : ℝ) (62698615461/125000000000 : ℝ) (501576769781/1000000000000 : ℝ) (50157676979/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 3 (3134930773/6250000000 : ℝ) (62698615461/125000000000 : ℝ) (501576769781/1000000000000 : ℝ) (50157676979/100000000000 : ℝ) (50158284673/100000000000 : ℝ) (501582846739/1000000000000 : ℝ) (501582846693/1000000000000 : ℝ) (501582846703/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 4 (50158284673/100000000000 : ℝ) (501582846739/1000000000000 : ℝ) (501582846693/1000000000000 : ℝ) (501582846703/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 5 (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 6 (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4199/32768 : ℝ))) 7 (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4199/32768 : ℝ)) hmem 8 (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4199/32768 : ℝ))) hcmem 8 (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4199/32768 : ℝ)) (992038937287/1000000000000 : ℝ) (99203893729/100000000000 : ℝ) (501582846711/1000000000000 : ℝ) (501582846721/1000000000000 : ℝ) (794207226733/1000000000000 : ℝ) (6204743959/7812500000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1111_exp_lower
  have heNumeric : (256862847433/125000000000 : ℝ)/4 ≤ Real.exp (-85256425414881/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862847433/125000000000 : ℝ)/4 ≤ Real.exp ((67183/524288 : ℝ)-(6204743959/7812500000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67183/524288 : ℝ) (4199/32768 : ℝ) (6204743959/7812500000 : ℝ) (256862847433/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1112; no trusted numerical premise.
theorem cover8_leaf1112_exp_radius : (498999867086904529/500000000000000000 : ℝ) ≤ Real.exp ((-67185/4194304 : ℝ)/8) ∧ Real.exp ((-67185/4194304 : ℝ)/8) ≤ (997999734173809059/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67185/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1112_exp_lower : (920113518075484519/1000000000000000000 : ℝ) ≤ Real.exp ((-5328526549657/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328526549657/8000000000000 : ℝ)/8) ≤ (23002837951887113/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328526549657/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1112_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431424339/62500000000 : ℝ) ≤ 4*Real.exp (4199/32768 : ℝ)*Real.exp (-mu (radius 8 (67185/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431424339/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67185/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1112_exp_radius
  have hrNumeric : (196821891221/200000000000 : ℝ) ≤ Real.exp (-67185/4194304 : ℝ) ∧ Real.exp (-67185/4194304 : ℝ) ≤ (492054728053/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196821891221/200000000000 : ℝ) ≤ (radius 8 (67185/524288 : ℝ)) ∧ (radius 8 (67185/524288 : ℝ)) ≤ (492054728053/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67185/524288 : ℝ)) (196821891221/200000000000 : ℝ) (492054728053/500000000000 : ℝ) (177562885769/1000000000000 : ℝ) (7102515431/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67185/524288 : ℝ)) (196821891221/200000000000 : ℝ) (492054728053/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196821891221/200000000000 : ℝ) (492054728053/500000000000 : ℝ) (248013682013/250000000000 : ℝ) (992054728053/1000000000000 : ℝ) (496011455539/500000000000 : ℝ) (24800572777/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 1 (248013682013/250000000000 : ℝ) (992054728053/1000000000000 : ℝ) (496011455539/500000000000 : ℝ) (24800572777/25000000000 : ℝ) (198407763913/200000000000 : ℝ) (992038819567/1000000000000 : ℝ) (992038819437/1000000000000 : ℝ) (992038819439/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 2 (198407763913/200000000000 : ℝ) (992038819567/1000000000000 : ℝ) (992038819437/1000000000000 : ℝ) (992038819439/1000000000000 : ℝ) (992038819501/1000000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 3 (992038819501/1000000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 4 (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 5 (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 6 (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67185/524288 : ℝ)) 7 (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67185/524288 : ℝ))) (177562885769/1000000000000 : ℝ) (7102515431/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177562885769/1000000000000 : ℝ) (7102515431/40000000000 : ℝ) (147195360721/250000000000 : ℝ) (73597680361/125000000000 : ℝ) (210691056863/500000000000 : ℝ) (84276422747/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 1 (147195360721/250000000000 : ℝ) (73597680361/125000000000 : ℝ) (210691056863/500000000000 : ℝ) (84276422747/200000000000 : ℝ) (101016355661/200000000000 : ℝ) (63135222289/125000000000 : ℝ) (249049176331/500000000000 : ℝ) (49809835267/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 2 (101016355661/200000000000 : ℝ) (63135222289/125000000000 : ℝ) (249049176331/500000000000 : ℝ) (49809835267/100000000000 : ℝ) (501590065483/1000000000000 : ℝ) (501590065491/1000000000000 : ℝ) (501577911927/1000000000000 : ℝ) (100315582387/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 3 (501590065483/1000000000000 : ℝ) (501590065491/1000000000000 : ℝ) (501577911927/1000000000000 : ℝ) (100315582387/200000000000 : ℝ) (100316797741/200000000000 : ℝ) (501583988713/1000000000000 : ℝ) (125395997167/250000000000 : ℝ) (501583988677/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 4 (100316797741/200000000000 : ℝ) (501583988713/1000000000000 : ℝ) (125395997167/250000000000 : ℝ) (501583988677/1000000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 5 (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 6 (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67185/524288 : ℝ))) 7 (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67185/524288 : ℝ)) hmem 8 (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67185/524288 : ℝ))) hcmem 8 (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67185/524288 : ℝ)) (1984077639/2000000000 : ℝ) (992038819503/1000000000000 : ℝ) (250791994343/500000000000 : ℝ) (100316797739/200000000000 : ℝ) (794209129237/1000000000000 : ℝ) (397104564627/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1112_exp_lower
  have heNumeric : (128431424339/62500000000 : ℝ)/4 ≤ Real.exp (-5328526549657/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431424339/62500000000 : ℝ)/4 ≤ Real.exp ((4199/32768 : ℝ)-(397104564627/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4199/32768 : ℝ) (67185/524288 : ℝ) (397104564627/500000000000 : ℝ) (128431424339/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1113; no trusted numerical premise.
theorem cover8_leaf1113_exp_radius : (997999704431099681/1000000000000000000 : ℝ) ≤ Real.exp ((-33593/2097152 : ℝ)/8) ∧ Real.exp ((-33593/2097152 : ℝ)/8) ≤ (498999852215549841/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33593/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1113_exp_lower : (920113518634756293/1000000000000000000 : ℝ) ≤ Real.exp ((-17051284834419/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051284834419/25600000000000 : ℝ)/8) ≤ (460056759317378147/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051284834419/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1113_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862849927/125000000000 : ℝ) ≤ 4*Real.exp (67185/524288 : ℝ)*Real.exp (-mu (radius 8 (33593/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862849927/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33593/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1113_exp_radius
  have hrNumeric : (39364368859/40000000000 : ℝ) ≤ Real.exp (-33593/2097152 : ℝ) ∧ Real.exp (-33593/2097152 : ℝ) ≤ (246027305369/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39364368859/40000000000 : ℝ) ≤ (radius 8 (33593/262144 : ℝ)) ∧ (radius 8 (33593/262144 : ℝ)) ≤ (246027305369/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33593/262144 : ℝ)) (39364368859/40000000000 : ℝ) (246027305369/250000000000 : ℝ) (177564186157/1000000000000 : ℝ) (44391046541/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33593/262144 : ℝ)) (39364368859/40000000000 : ℝ) (246027305369/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39364368859/40000000000 : ℝ) (246027305369/250000000000 : ℝ) (992054610737/1000000000000 : ℝ) (496027305369/500000000000 : ℝ) (49601139641/50000000000 : ℝ) (992022792821/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 1 (992054610737/1000000000000 : ℝ) (496027305369/500000000000 : ℝ) (49601139641/50000000000 : ℝ) (992022792821/1000000000000 : ℝ) (496019350889/500000000000 : ℝ) (49601935089/50000000000 : ℝ) (19840774033/20000000000 : ℝ) (248009675413/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 2 (496019350889/500000000000 : ℝ) (49601935089/50000000000 : ℝ) (19840774033/20000000000 : ℝ) (248009675413/250000000000 : ℝ) (496019350857/500000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 3 (496019350857/500000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 4 (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 5 (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 6 (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33593/262144 : ℝ)) 7 (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33593/262144 : ℝ))) (177564186157/1000000000000 : ℝ) (44391046541/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177564186157/1000000000000 : ℝ) (44391046541/250000000000 : ℝ) (294391046539/500000000000 : ℝ) (294391046541/500000000000 : ℝ) (421383656727/1000000000000 : ℝ) (13168239273/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 1 (294391046539/500000000000 : ℝ) (294391046541/500000000000 : ℝ) (421383656727/1000000000000 : ℝ) (13168239273/31250000000 : ℝ) (252541437451/500000000000 : ℝ) (505082874909/1000000000000 : ℝ) (498099539647/1000000000000 : ℝ) (99619907931/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 2 (252541437451/500000000000 : ℝ) (505082874909/1000000000000 : ℝ) (498099539647/1000000000000 : ℝ) (99619907931/200000000000 : ℝ) (250795603637/500000000000 : ℝ) (250795603641/500000000000 : ℝ) (25078952703/50000000000 : ℝ) (501579054069/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 3 (250795603637/500000000000 : ℝ) (250795603641/500000000000 : ℝ) (25078952703/50000000000 : ℝ) (501579054069/1000000000000 : ℝ) (501585130667/1000000000000 : ℝ) (125396282669/250000000000 : ℝ) (50158513063/100000000000 : ℝ) (501585130639/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 4 (501585130667/1000000000000 : ℝ) (125396282669/250000000000 : ℝ) (50158513063/100000000000 : ℝ) (501585130639/1000000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 5 (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 6 (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33593/262144 : ℝ))) 7 (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33593/262144 : ℝ)) hmem 8 (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33593/262144 : ℝ))) hcmem 8 (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33593/262144 : ℝ)) (992038701713/1000000000000 : ℝ) (248009675429/250000000000 : ℝ) (62698141331/125000000000 : ℝ) (250792565329/500000000000 : ℝ) (19855275793/25000000000 : ℝ) (39710551587/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1113_exp_lower
  have heNumeric : (256862849927/125000000000 : ℝ)/4 ≤ Real.exp (-17051284834419/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862849927/125000000000 : ℝ)/4 ≤ Real.exp ((67185/524288 : ℝ)-(39710551587/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67185/524288 : ℝ) (33593/262144 : ℝ) (39710551587/50000000000 : ℝ) (256862849927/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1114; no trusted numerical premise.
theorem cover8_leaf1114_exp_radius : (99799967468839119/100000000000000000 : ℝ) ≤ Real.exp ((-67187/4194304 : ℝ)/8) ∧ Real.exp ((-67187/4194304 : ℝ)/8) ≤ (997999674688391191/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67187/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1114_exp_lower : (460056759598279189/500000000000000000 : ℝ) ≤ Real.exp ((-42628211773431/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628211773431/64000000000000 : ℝ)/8) ≤ (920113519196558379/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628211773431/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1114_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902809453/1000000000000 : ℝ) ≤ 4*Real.exp (33593/262144 : ℝ)*Real.exp (-mu (radius 8 (67187/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902809453/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67187/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1114_exp_radius
  have hrNumeric : (196821797369/200000000000 : ℝ) ≤ Real.exp (-67187/4194304 : ℝ) ∧ Real.exp (-67187/4194304 : ℝ) ≤ (492054493423/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196821797369/200000000000 : ℝ) ≤ (radius 8 (67187/524288 : ℝ)) ∧ (radius 8 (67187/524288 : ℝ)) ≤ (492054493423/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67187/524288 : ℝ)) (196821797369/200000000000 : ℝ) (492054493423/500000000000 : ℝ) (22195685817/125000000000 : ℝ) (177565486543/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67187/524288 : ℝ)) (196821797369/200000000000 : ℝ) (492054493423/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196821797369/200000000000 : ℝ) (492054493423/500000000000 : ℝ) (496027246711/500000000000 : ℝ) (992054493423/1000000000000 : ℝ) (992022674561/1000000000000 : ℝ) (992022674563/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 1 (496027246711/500000000000 : ℝ) (992054493423/1000000000000 : ℝ) (992022674561/1000000000000 : ℝ) (992022674563/1000000000000 : ℝ) (992038583991/1000000000000 : ℝ) (992038583993/1000000000000 : ℝ) (992038583863/1000000000000 : ℝ) (496019291933/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 2 (992038583991/1000000000000 : ℝ) (992038583993/1000000000000 : ℝ) (992038583863/1000000000000 : ℝ) (496019291933/500000000000 : ℝ) (992038583927/1000000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 3 (992038583927/1000000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 4 (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 5 (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 6 (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67187/524288 : ℝ)) 7 (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67187/524288 : ℝ))) (22195685817/125000000000 : ℝ) (177565486543/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22195685817/125000000000 : ℝ) (177565486543/1000000000000 : ℝ) (147195685817/250000000000 : ℝ) (73597842909/125000000000 : ℝ) (421385199711/1000000000000 : ℝ) (10534629993/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 1 (147195685817/250000000000 : ℝ) (73597842909/125000000000 : ℝ) (421385199711/1000000000000 : ℝ) (10534629993/25000000000 : ℝ) (505083971489/1000000000000 : ℝ) (63135496437/125000000000 : ℝ) (498100726619/1000000000000 : ℝ) (498100726627/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 2 (505083971489/1000000000000 : ℝ) (63135496437/125000000000 : ℝ) (498100726619/1000000000000 : ℝ) (498100726627/1000000000000 : ℝ) (250796174527/500000000000 : ℝ) (250796174531/500000000000 : ℝ) (250790098091/500000000000 : ℝ) (50158019619/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 3 (250796174527/500000000000 : ℝ) (250796174531/500000000000 : ℝ) (250790098091/500000000000 : ℝ) (50158019619/100000000000 : ℝ) (250793136309/500000000000 : ℝ) (250793136313/500000000000 : ℝ) (501586272581/1000000000000 : ℝ) (50158627259/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 4 (250793136309/500000000000 : ℝ) (250793136313/500000000000 : ℝ) (501586272581/1000000000000 : ℝ) (50158627259/100000000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 5 (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 6 (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67187/524288 : ℝ))) 7 (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67187/524288 : ℝ)) hmem 8 (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67187/524288 : ℝ))) hcmem 8 (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67187/524288 : ℝ)) (496019291963/500000000000 : ℝ) (99203858393/100000000000 : ℝ) (501586272599/1000000000000 : ℝ) (15674571019/31250000000 : ℝ) (397106467093/500000000000 : ℝ) (198553233551/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1114_exp_lower
  have heNumeric : (2054902809453/1000000000000 : ℝ)/4 ≤ Real.exp (-42628211773431/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902809453/1000000000000 : ℝ)/4 ≤ Real.exp ((33593/262144 : ℝ)-(198553233551/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33593/262144 : ℝ) (67187/524288 : ℝ) (198553233551/250000000000 : ℝ) (2054902809453/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1115; no trusted numerical premise.
theorem cover8_leaf1115_exp_radius : (199599928989136717/200000000000000000 : ℝ) ≤ Real.exp ((-16797/1048576 : ℝ)/8) ∧ Real.exp ((-16797/1048576 : ℝ)/8) ≤ (498999822472841793/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16797/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1115_exp_lower : (1437677374625673/1562500000000000 : ℝ) ≤ Real.exp ((-3410256916773/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410256916773/5120000000000 : ℝ)/8) ≤ (920113519760430721/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410256916773/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1115_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862852441/125000000000 : ℝ) ≤ 4*Real.exp (67187/524288 : ℝ)*Real.exp (-mu (radius 8 (16797/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862852441/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16797/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1115_exp_radius
  have hrNumeric : (196821750443/200000000000 : ℝ) ≤ Real.exp (-16797/1048576 : ℝ) ∧ Real.exp (-16797/1048576 : ℝ) ≤ (123013594027/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196821750443/200000000000 : ℝ) ≤ (radius 8 (16797/131072 : ℝ)) ∧ (radius 8 (16797/131072 : ℝ)) ≤ (123013594027/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16797/131072 : ℝ)) (196821750443/200000000000 : ℝ) (123013594027/125000000000 : ℝ) (35513357381/200000000000 : ℝ) (177566786911/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16797/131072 : ℝ)) (196821750443/200000000000 : ℝ) (123013594027/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196821750443/200000000000 : ℝ) (123013594027/125000000000 : ℝ) (992054376107/1000000000000 : ℝ) (248013594027/250000000000 : ℝ) (992022556303/1000000000000 : ℝ) (198404511261/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 1 (992054376107/1000000000000 : ℝ) (248013594027/250000000000 : ℝ) (992022556303/1000000000000 : ℝ) (198404511261/200000000000 : ℝ) (198407693241/200000000000 : ℝ) (992038466207/1000000000000 : ℝ) (992038466077/1000000000000 : ℝ) (992038466079/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 2 (198407693241/200000000000 : ℝ) (992038466207/1000000000000 : ℝ) (992038466077/1000000000000 : ℝ) (992038466079/1000000000000 : ℝ) (992038466141/1000000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 3 (992038466141/1000000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 4 (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 5 (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 6 (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16797/131072 : ℝ)) 7 (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16797/131072 : ℝ))) (35513357381/200000000000 : ℝ) (177566786911/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35513357381/200000000000 : ℝ) (177566786911/1000000000000 : ℝ) (147195848363/250000000000 : ℝ) (36798962091/62500000000 : ℝ) (210693371339/500000000000 : ℝ) (210693371343/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 1 (147195848363/250000000000 : ℝ) (36798962091/62500000000 : ℝ) (210693371339/500000000000 : ℝ) (210693371343/500000000000 : ℝ) (101017013613/200000000000 : ℝ) (505085068071/1000000000000 : ℝ) (498101913577/1000000000000 : ℝ) (31131369599/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 2 (101017013613/200000000000 : ℝ) (505085068071/1000000000000 : ℝ) (498101913577/1000000000000 : ℝ) (31131369599/62500000000 : ℝ) (501593490821/1000000000000 : ℝ) (125398372707/250000000000 : ℝ) (501581338291/1000000000000 : ℝ) (501581338299/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 3 (501593490821/1000000000000 : ℝ) (125398372707/250000000000 : ℝ) (501581338291/1000000000000 : ℝ) (501581338299/1000000000000 : ℝ) (125396853639/250000000000 : ℝ) (125396853641/250000000000 : ℝ) (501587414519/1000000000000 : ℝ) (501587414527/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 4 (125396853639/250000000000 : ℝ) (125396853641/250000000000 : ℝ) (501587414519/1000000000000 : ℝ) (501587414527/1000000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 5 (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 6 (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16797/131072 : ℝ))) 7 (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16797/131072 : ℝ)) hmem 8 (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16797/131072 : ℝ))) hcmem 8 (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16797/131072 : ℝ)) (49601923307/50000000000 : ℝ) (992038466143/1000000000000 : ℝ) (501587414537/1000000000000 : ℝ) (250793707273/500000000000 : ℝ) (99276854579/125000000000 : ℝ) (15884296733/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1115_exp_lower
  have heNumeric : (256862852441/125000000000 : ℝ)/4 ≤ Real.exp (-3410256916773/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862852441/125000000000 : ℝ)/4 ≤ Real.exp ((67187/524288 : ℝ)-(15884296733/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67187/524288 : ℝ) (16797/131072 : ℝ) (15884296733/20000000000 : ℝ) (256862852441/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1116; no trusted numerical premise.
theorem cover8_leaf1116_exp_radius : (997999615202976867/1000000000000000000 : ℝ) ≤ Real.exp ((-67189/4194304 : ℝ)/8) ∧ Real.exp ((-67189/4194304 : ℝ)/8) ≤ (249499903800744217/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67189/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1116_exp_lower : (460056760163301673/500000000000000000 : ℝ) ≤ Real.exp ((-21314105572307/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314105572307/32000000000000 : ℝ)/8) ≤ (920113520326603347/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314105572307/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1116_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902829643/1000000000000 : ℝ) ≤ 4*Real.exp (16797/131072 : ℝ)*Real.exp (-mu (radius 8 (67189/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902829643/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67189/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1116_exp_radius
  have hrNumeric : (196821703517/200000000000 : ℝ) ≤ Real.exp (-67189/4194304 : ℝ) ∧ Real.exp (-67189/4194304 : ℝ) ≤ (492054258793/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196821703517/200000000000 : ℝ) ≤ (radius 8 (67189/524288 : ℝ)) ∧ (radius 8 (67189/524288 : ℝ)) ≤ (492054258793/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67189/524288 : ℝ)) (196821703517/200000000000 : ℝ) (492054258793/500000000000 : ℝ) (5549002727/31250000000 : ℝ) (17756808727/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67189/524288 : ℝ)) (196821703517/200000000000 : ℝ) (492054258793/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196821703517/200000000000 : ℝ) (492054258793/500000000000 : ℝ) (124006782349/125000000000 : ℝ) (992054258793/1000000000000 : ℝ) (198404487609/200000000000 : ℝ) (496011219023/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 1 (124006782349/125000000000 : ℝ) (992054258793/1000000000000 : ℝ) (198404487609/200000000000 : ℝ) (496011219023/500000000000 : ℝ) (496019174209/500000000000 : ℝ) (49601917421/50000000000 : ℝ) (99203834829/100000000000 : ℝ) (248009587073/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 2 (496019174209/500000000000 : ℝ) (49601917421/50000000000 : ℝ) (99203834829/100000000000 : ℝ) (248009587073/250000000000 : ℝ) (496019174177/500000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 3 (496019174177/500000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 4 (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 5 (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 6 (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67189/524288 : ℝ)) 7 (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67189/524288 : ℝ))) (5549002727/31250000000 : ℝ) (17756808727/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5549002727/31250000000 : ℝ) (17756808727/100000000000 : ℝ) (36799002727/62500000000 : ℝ) (117756808727/200000000000 : ℝ) (421388285627/1000000000000 : ℝ) (84277657127/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 1 (36799002727/62500000000 : ℝ) (117756808727/200000000000 : ℝ) (421388285627/1000000000000 : ℝ) (84277657127/200000000000 : ℝ) (505086164629/1000000000000 : ℝ) (101017232927/200000000000 : ℝ) (249051550261/500000000000 : ℝ) (498103100529/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 2 (505086164629/1000000000000 : ℝ) (101017232927/200000000000 : ℝ) (249051550261/500000000000 : ℝ) (498103100529/1000000000000 : ℝ) (20063785303/40000000000 : ℝ) (250797316291/500000000000 : ℝ) (125395620097/250000000000 : ℝ) (100316496079/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 3 (20063785303/40000000000 : ℝ) (250797316291/500000000000 : ℝ) (125395620097/250000000000 : ℝ) (100316496079/200000000000 : ℝ) (501588556481/1000000000000 : ℝ) (501588556489/1000000000000 : ℝ) (125397139111/250000000000 : ℝ) (125397139113/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 4 (501588556481/1000000000000 : ℝ) (501588556489/1000000000000 : ℝ) (125397139111/250000000000 : ℝ) (125397139113/250000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 5 (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 6 (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67189/524288 : ℝ))) 7 (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67189/524288 : ℝ)) hmem 8 (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67189/524288 : ℝ))) hcmem 8 (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67189/524288 : ℝ)) (992038348353/1000000000000 : ℝ) (248009587089/250000000000 : ℝ) (250794278231/500000000000 : ℝ) (501588556471/1000000000000 : ℝ) (794216739059/1000000000000 : ℝ) (198554184769/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1116_exp_lower
  have heNumeric : (2054902829643/1000000000000 : ℝ)/4 ≤ Real.exp (-21314105572307/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902829643/1000000000000 : ℝ)/4 ≤ Real.exp ((16797/131072 : ℝ)-(198554184769/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16797/131072 : ℝ) (67189/524288 : ℝ) (198554184769/250000000000 : ℝ) (2054902829643/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1117; no trusted numerical premise.
theorem cover8_leaf1117_exp_radius : (199599917092054207/200000000000000000 : ℝ) ≤ Real.exp ((-33595/2097152 : ℝ)/8) ∧ Real.exp ((-33595/2097152 : ℝ)/8) ≤ (249499896365067759/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33595/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1117_exp_lower : (14376773763976581/15625000000000000 : ℝ) ≤ Real.exp ((-85256421657211/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256421657211/128000000000000 : ℝ)/8) ≤ (184022704178900237/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256421657211/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1117_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490283979/100000000000 : ℝ) ≤ 4*Real.exp (67189/524288 : ℝ)*Real.exp (-mu (radius 8 (33595/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490283979/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33595/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1117_exp_radius
  have hrNumeric : (196821656591/200000000000 : ℝ) ≤ Real.exp (-33595/2097152 : ℝ) ∧ Real.exp (-33595/2097152 : ℝ) ≤ (246027070739/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196821656591/200000000000 : ℝ) ≤ (radius 8 (33595/262144 : ℝ)) ∧ (radius 8 (33595/262144 : ℝ)) ≤ (246027070739/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33595/262144 : ℝ)) (196821656591/200000000000 : ℝ) (246027070739/250000000000 : ℝ) (177569387613/1000000000000 : ℝ) (177569387619/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33595/262144 : ℝ)) (196821656591/200000000000 : ℝ) (246027070739/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196821656591/200000000000 : ℝ) (246027070739/250000000000 : ℝ) (992054141477/1000000000000 : ℝ) (496027070739/500000000000 : ℝ) (496011159893/500000000000 : ℝ) (248005579947/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 1 (992054141477/1000000000000 : ℝ) (496027070739/500000000000 : ℝ) (496011159893/500000000000 : ℝ) (248005579947/250000000000 : ℝ) (992038230631/1000000000000 : ℝ) (992038230633/1000000000000 : ℝ) (992038230503/1000000000000 : ℝ) (496019115253/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 2 (992038230631/1000000000000 : ℝ) (992038230633/1000000000000 : ℝ) (992038230503/1000000000000 : ℝ) (496019115253/500000000000 : ℝ) (992038230567/1000000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 3 (992038230567/1000000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 4 (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 5 (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 6 (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33595/262144 : ℝ)) 7 (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33595/262144 : ℝ))) (177569387613/1000000000000 : ℝ) (177569387619/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177569387613/1000000000000 : ℝ) (177569387619/1000000000000 : ℝ) (294392346903/500000000000 : ℝ) (58878469381/100000000000 : ℝ) (421389828559/1000000000000 : ℝ) (421389828567/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 1 (294392346903/500000000000 : ℝ) (58878469381/100000000000 : ℝ) (421389828559/1000000000000 : ℝ) (421389828567/1000000000000 : ℝ) (252543630591/500000000000 : ℝ) (505087261189/1000000000000 : ℝ) (99620857491/200000000000 : ℝ) (249052143731/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 2 (252543630591/500000000000 : ℝ) (505087261189/1000000000000 : ℝ) (99620857491/200000000000 : ℝ) (249052143731/500000000000 : ℝ) (250797887159/500000000000 : ℝ) (250797887163/500000000000 : ℝ) (501583622473/1000000000000 : ℝ) (501583622481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 3 (250797887159/500000000000 : ℝ) (250797887163/500000000000 : ℝ) (501583622473/1000000000000 : ℝ) (501583622481/1000000000000 : ℝ) (100317939679/200000000000 : ℝ) (125397424601/250000000000 : ℝ) (250794849179/500000000000 : ℝ) (501589698367/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 4 (100317939679/200000000000 : ℝ) (125397424601/250000000000 : ℝ) (250794849179/500000000000 : ℝ) (501589698367/1000000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 5 (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 6 (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33595/262144 : ℝ))) 7 (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33595/262144 : ℝ)) hmem 8 (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33595/262144 : ℝ))) hcmem 8 (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33595/262144 : ℝ)) (496019115283/500000000000 : ℝ) (99203823057/100000000000 : ℝ) (62698712297/125000000000 : ℝ) (250794849193/500000000000 : ℝ) (794218641467/1000000000000 : ℝ) (794218641487/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1117_exp_lower
  have heNumeric : (205490283979/100000000000 : ℝ)/4 ≤ Real.exp (-85256421657211/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490283979/100000000000 : ℝ)/4 ≤ Real.exp ((67189/524288 : ℝ)-(794218641487/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67189/524288 : ℝ) (33595/262144 : ℝ) (794218641487/1000000000000 : ℝ) (205490283979/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1118; no trusted numerical premise.
theorem cover8_leaf1118_exp_radius : (997999555717566089/1000000000000000000 : ℝ) ≤ Real.exp ((-67191/4194304 : ℝ)/8) ∧ Real.exp ((-67191/4194304 : ℝ)/8) ≤ (99799955571756609/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67191/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1118_exp_lower : (920113521465849449/1000000000000000000 : ℝ) ≤ Real.exp ((-42628210510677/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628210510677/64000000000000 : ℝ)/8) ≤ (18402270429316989/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628210510677/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1118_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451424999/500000000000 : ℝ) ≤ 4*Real.exp (33595/262144 : ℝ)*Real.exp (-mu (radius 8 (67191/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451424999/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67191/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1118_exp_radius
  have hrNumeric : (492054024163/500000000000 : ℝ) ≤ Real.exp (-67191/4194304 : ℝ) ∧ Real.exp (-67191/4194304 : ℝ) ≤ (984108048327/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492054024163/500000000000 : ℝ) ≤ (radius 8 (67191/524288 : ℝ)) ∧ (radius 8 (67191/524288 : ℝ)) ≤ (984108048327/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67191/524288 : ℝ)) (492054024163/500000000000 : ℝ) (984108048327/1000000000000 : ℝ) (177570687947/1000000000000 : ℝ) (177570687953/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67191/524288 : ℝ)) (492054024163/500000000000 : ℝ) (984108048327/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492054024163/500000000000 : ℝ) (984108048327/1000000000000 : ℝ) (992054024163/1000000000000 : ℝ) (248013506041/250000000000 : ℝ) (124002775191/125000000000 : ℝ) (99202220153/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 1 (992054024163/1000000000000 : ℝ) (248013506041/250000000000 : ℝ) (124002775191/125000000000 : ℝ) (99202220153/100000000000 : ℝ) (198407622569/200000000000 : ℝ) (992038112847/1000000000000 : ℝ) (992038112717/1000000000000 : ℝ) (12400476409/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 2 (198407622569/200000000000 : ℝ) (992038112847/1000000000000 : ℝ) (992038112717/1000000000000 : ℝ) (12400476409/12500000000 : ℝ) (992038112781/1000000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 3 (992038112781/1000000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 4 (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 5 (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 6 (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67191/524288 : ℝ)) 7 (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67191/524288 : ℝ))) (177570687947/1000000000000 : ℝ) (177570687953/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177570687947/1000000000000 : ℝ) (177570687953/1000000000000 : ℝ) (588785343973/1000000000000 : ℝ) (588785343977/1000000000000 : ℝ) (421391371467/1000000000000 : ℝ) (16855654859/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 1 (588785343973/1000000000000 : ℝ) (588785343977/1000000000000 : ℝ) (421391371467/1000000000000 : ℝ) (16855654859/40000000000 : ℝ) (12627208943/25000000000 : ℝ) (252544178863/500000000000 : ℝ) (498105474369/1000000000000 : ℝ) (62263184297/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 2 (12627208943/25000000000 : ℝ) (252544178863/500000000000 : ℝ) (498105474369/1000000000000 : ℝ) (62263184297/125000000000 : ℝ) (125399229011/250000000000 : ℝ) (501596916051/1000000000000 : ℝ) (501584764541/1000000000000 : ℝ) (501584764549/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 3 (125399229011/250000000000 : ℝ) (501596916051/1000000000000 : ℝ) (501584764541/1000000000000 : ℝ) (501584764549/1000000000000 : ℝ) (125397710073/250000000000 : ℝ) (5015908403/10000000000 : ℝ) (100318168051/200000000000 : ℝ) (62698855033/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 4 (125397710073/250000000000 : ℝ) (5015908403/10000000000 : ℝ) (100318168051/200000000000 : ℝ) (62698855033/125000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 5 (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 6 (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67191/524288 : ℝ))) 7 (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67191/524288 : ℝ)) hmem 8 (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67191/524288 : ℝ))) hcmem 8 (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67191/524288 : ℝ)) (49601905639/50000000000 : ℝ) (62002382049/62500000000 : ℝ) (501590840273/1000000000000 : ℝ) (250795420141/500000000000 : ℝ) (794220543849/1000000000000 : ℝ) (198555135967/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1118_exp_lower
  have heNumeric : (1027451424999/500000000000 : ℝ)/4 ≤ Real.exp (-42628210510677/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451424999/500000000000 : ℝ)/4 ≤ Real.exp ((33595/262144 : ℝ)-(198555135967/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33595/262144 : ℝ) (67191/524288 : ℝ) (198555135967/250000000000 : ℝ) (1027451424999/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1119; no trusted numerical premise.
theorem cover8_leaf1119_exp_radius : (99799952597486203/100000000000000000 : ℝ) ≤ Real.exp ((-8399/524288 : ℝ)/8) ∧ Real.exp ((-8399/524288 : ℝ)/8) ≤ (997999525974862031/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8399/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1119_exp_lower : (460056761019116421/500000000000000000 : ℝ) ≤ Real.exp ((-17051284076869/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051284076869/25600000000000 : ℝ)/8) ≤ (920113522038232843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051284076869/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1119_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32107857191/15625000000 : ℝ) ≤ 4*Real.exp (67191/524288 : ℝ)*Real.exp (-mu (radius 8 (8399/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (32107857191/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8399/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1119_exp_radius
  have hrNumeric : (15376684589/15625000000 : ℝ) ≤ Real.exp (-8399/524288 : ℝ) ∧ Real.exp (-8399/524288 : ℝ) ≤ (984107813697/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15376684589/15625000000 : ℝ) ≤ (radius 8 (8399/65536 : ℝ)) ∧ (radius 8 (8399/65536 : ℝ)) ≤ (984107813697/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8399/65536 : ℝ)) (15376684589/15625000000 : ℝ) (984107813697/1000000000000 : ℝ) (44392997069/250000000000 : ℝ) (177571988283/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8399/65536 : ℝ)) (15376684589/15625000000 : ℝ) (984107813697/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15376684589/15625000000 : ℝ) (984107813697/1000000000000 : ℝ) (31001684589/31250000000 : ℝ) (992053906849/1000000000000 : ℝ) (99202208327/100000000000 : ℝ) (992022083271/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 1 (31001684589/31250000000 : ℝ) (992053906849/1000000000000 : ℝ) (99202208327/100000000000 : ℝ) (992022083271/1000000000000 : ℝ) (992037995059/1000000000000 : ℝ) (49601899753/50000000000 : ℝ) (992037994931/1000000000000 : ℝ) (992037994933/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 2 (992037995059/1000000000000 : ℝ) (49601899753/50000000000 : ℝ) (992037994931/1000000000000 : ℝ) (992037994933/1000000000000 : ℝ) (198407598999/200000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 3 (198407598999/200000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 4 (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 5 (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 6 (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8399/65536 : ℝ)) 7 (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8399/65536 : ℝ))) (44392997069/250000000000 : ℝ) (177571988283/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44392997069/250000000000 : ℝ) (177571988283/1000000000000 : ℝ) (294392997069/500000000000 : ℝ) (294392997071/500000000000 : ℝ) (421392914363/1000000000000 : ℝ) (421392914373/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 1 (294392997069/500000000000 : ℝ) (294392997071/500000000000 : ℝ) (421392914363/1000000000000 : ℝ) (421392914373/1000000000000 : ℝ) (2020357817/4000000000 : ℝ) (252544727129/500000000000 : ℝ) (249053330637/500000000000 : ℝ) (498106661283/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 2 (2020357817/4000000000 : ℝ) (252544727129/500000000000 : ℝ) (249053330637/500000000000 : ℝ) (498106661283/1000000000000 : ℝ) (250799028881/500000000000 : ℝ) (501598057771/1000000000000 : ℝ) (501585906601/1000000000000 : ℝ) (50158590661/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 3 (250799028881/500000000000 : ℝ) (501598057771/1000000000000 : ℝ) (501585906601/1000000000000 : ℝ) (50158590661/100000000000 : ℝ) (501591982181/1000000000000 : ℝ) (501591982191/1000000000000 : ℝ) (7837374721/15625000000 : ℝ) (250795991077/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 4 (501591982181/1000000000000 : ℝ) (501591982191/1000000000000 : ℝ) (7837374721/15625000000 : ℝ) (250795991077/500000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 5 (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 6 (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8399/65536 : ℝ))) 7 (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8399/65536 : ℝ)) hmem 8 (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8399/65536 : ℝ))) hcmem 8 (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8399/65536 : ℝ)) (496018997497/500000000000 : ℝ) (992037994997/1000000000000 : ℝ) (250795991081/500000000000 : ℝ) (501591982173/1000000000000 : ℝ) (39711122311/50000000000 : ℝ) (4963890289/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1119_exp_lower
  have heNumeric : (32107857191/15625000000 : ℝ)/4 ≤ Real.exp (-17051284076869/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32107857191/15625000000 : ℝ)/4 ≤ Real.exp ((67191/524288 : ℝ)-(4963890289/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67191/524288 : ℝ) (8399/65536 : ℝ) (4963890289/6250000000 : ℝ) (32107857191/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1120; no trusted numerical premise.
theorem cover8_leaf1120_exp_radius : (498999748116079429/500000000000000000 : ℝ) ≤ Real.exp ((-67193/4194304 : ℝ)/8) ∧ Real.exp ((-67193/4194304 : ℝ)/8) ≤ (997999496232158859/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67193/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1120_exp_lower : (920113522613721619/1000000000000000000 : ℝ) ≤ Real.exp ((-2131410493597/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131410493597/3200000000000 : ℝ)/8) ≤ (46005676130686081/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131410493597/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1120_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451435253/500000000000 : ℝ) ≤ 4*Real.exp (8399/65536 : ℝ)*Real.exp (-mu (radius 8 (67193/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451435253/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67193/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1120_exp_radius
  have hrNumeric : (984107579067/1000000000000 : ℝ) ≤ Real.exp (-67193/4194304 : ℝ) ∧ Real.exp (-67193/4194304 : ℝ) ≤ (246026894767/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984107579067/1000000000000 : ℝ) ≤ (radius 8 (67193/524288 : ℝ)) ∧ (radius 8 (67193/524288 : ℝ)) ≤ (246026894767/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67193/524288 : ℝ)) (984107579067/1000000000000 : ℝ) (246026894767/250000000000 : ℝ) (17757328859/100000000000 : ℝ) (177573288597/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67193/524288 : ℝ)) (984107579067/1000000000000 : ℝ) (246026894767/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984107579067/1000000000000 : ℝ) (246026894767/250000000000 : ℝ) (992053789533/1000000000000 : ℝ) (496026894767/500000000000 : ℝ) (248005491253/250000000000 : ℝ) (992021965013/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 1 (992053789533/1000000000000 : ℝ) (496026894767/500000000000 : ℝ) (248005491253/250000000000 : ℝ) (992021965013/1000000000000 : ℝ) (124004734659/125000000000 : ℝ) (496018938637/500000000000 : ℝ) (124004734643/125000000000 : ℝ) (496018938573/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 2 (124004734659/125000000000 : ℝ) (496018938637/500000000000 : ℝ) (124004734643/125000000000 : ℝ) (496018938573/500000000000 : ℝ) (124004734651/125000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 3 (124004734651/125000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 4 (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 5 (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 6 (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67193/524288 : ℝ)) 7 (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67193/524288 : ℝ))) (17757328859/100000000000 : ℝ) (177573288597/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17757328859/100000000000 : ℝ) (177573288597/1000000000000 : ℝ) (117757328859/200000000000 : ℝ) (588786644299/1000000000000 : ℝ) (105348614309/250000000000 : ℝ) (210697228623/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 1 (117757328859/200000000000 : ℝ) (588786644299/1000000000000 : ℝ) (105348614309/250000000000 : ℝ) (210697228623/500000000000 : ℝ) (101018110153/200000000000 : ℝ) (505090550773/1000000000000 : ℝ) (498107848161/1000000000000 : ℝ) (49810784817/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 2 (101018110153/200000000000 : ℝ) (505090550773/1000000000000 : ℝ) (498107848161/1000000000000 : ℝ) (49810784817/100000000000 : ℝ) (501599199463/1000000000000 : ℝ) (31349949967/62500000000 : ℝ) (125396762161/250000000000 : ℝ) (250793524327/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 3 (501599199463/1000000000000 : ℝ) (31349949967/62500000000 : ℝ) (125396762161/250000000000 : ℝ) (250793524327/500000000000 : ℝ) (501593124053/1000000000000 : ℝ) (501593124063/1000000000000 : ℝ) (31349570251/62500000000 : ℝ) (501593124027/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 4 (501593124053/1000000000000 : ℝ) (501593124063/1000000000000 : ℝ) (31349570251/62500000000 : ℝ) (501593124027/1000000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 5 (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 6 (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67193/524288 : ℝ))) 7 (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67193/524288 : ℝ)) hmem 8 (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67193/524288 : ℝ))) hcmem 8 (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67193/524288 : ℝ)) (992037877207/1000000000000 : ℝ) (99203787721/100000000000 : ℝ) (250796562017/500000000000 : ℝ) (100318624809/200000000000 : ℝ) (198556087141/250000000000 : ℝ) (158844869717/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1120_exp_lower
  have heNumeric : (1027451435253/500000000000 : ℝ)/4 ≤ Real.exp (-2131410493597/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451435253/500000000000 : ℝ)/4 ≤ Real.exp ((8399/65536 : ℝ)-(158844869717/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8399/65536 : ℝ) (67193/524288 : ℝ) (158844869717/200000000000 : ℝ) (1027451435253/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1121; no trusted numerical premise.
theorem cover8_leaf1121_exp_radius : (997999466489456571/1000000000000000000 : ℝ) ≤ Real.exp ((-33597/2097152 : ℝ)/8) ∧ Real.exp ((-33597/2097152 : ℝ)/8) ≤ (249499866622364143/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33597/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1121_exp_lower : (460056761595410297/500000000000000000 : ℝ) ≤ Real.exp ((-85256419101623/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256419101623/128000000000000 : ℝ)/8) ≤ (184022704638164119/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256419101623/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1121_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902880817/1000000000000 : ℝ) ≤ 4*Real.exp (67193/524288 : ℝ)*Real.exp (-mu (radius 8 (33597/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902880817/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33597/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1121_exp_radius
  have hrNumeric : (984107344437/1000000000000 : ℝ) ≤ Real.exp (-33597/2097152 : ℝ) ∧ Real.exp (-33597/2097152 : ℝ) ≤ (492053672219/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984107344437/1000000000000 : ℝ) ≤ (radius 8 (33597/262144 : ℝ)) ∧ (radius 8 (33597/262144 : ℝ)) ≤ (492053672219/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33597/262144 : ℝ)) (984107344437/1000000000000 : ℝ) (492053672219/500000000000 : ℝ) (1775745889/10000000000 : ℝ) (177574588907/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33597/262144 : ℝ)) (984107344437/1000000000000 : ℝ) (492053672219/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984107344437/1000000000000 : ℝ) (492053672219/500000000000 : ℝ) (496026836109/500000000000 : ℝ) (992053672219/1000000000000 : ℝ) (992021846753/1000000000000 : ℝ) (198404369351/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 1 (496026836109/500000000000 : ℝ) (992053672219/1000000000000 : ℝ) (992021846753/1000000000000 : ℝ) (198404369351/200000000000 : ℝ) (198407551897/200000000000 : ℝ) (992037759487/1000000000000 : ℝ) (992037759357/1000000000000 : ℝ) (1550058999/1562500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 2 (198407551897/200000000000 : ℝ) (992037759487/1000000000000 : ℝ) (992037759357/1000000000000 : ℝ) (1550058999/1562500000 : ℝ) (992037759421/1000000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 3 (992037759421/1000000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 4 (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 5 (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 6 (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33597/262144 : ℝ)) 7 (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33597/262144 : ℝ))) (1775745889/10000000000 : ℝ) (177574588907/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1775745889/10000000000 : ℝ) (177574588907/1000000000000 : ℝ) (11775745889/20000000000 : ℝ) (294393647227/500000000000 : ℝ) (421396000099/1000000000000 : ℝ) (105349000027/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 1 (11775745889/20000000000 : ℝ) (294393647227/500000000000 : ℝ) (421396000099/1000000000000 : ℝ) (105349000027/250000000000 : ℝ) (252545823637/500000000000 : ℝ) (505091647281/1000000000000 : ℝ) (498109035041/1000000000000 : ℝ) (498109035049/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 2 (252545823637/500000000000 : ℝ) (505091647281/1000000000000 : ℝ) (498109035041/1000000000000 : ℝ) (498109035049/1000000000000 : ℝ) (501600341157/1000000000000 : ℝ) (100320068233/200000000000 : ℝ) (501588190681/1000000000000 : ℝ) (501588190689/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 3 (501600341157/1000000000000 : ℝ) (100320068233/200000000000 : ℝ) (501588190681/1000000000000 : ℝ) (501588190689/1000000000000 : ℝ) (501594265919/1000000000000 : ℝ) (501594265927/1000000000000 : ℝ) (250797132941/500000000000 : ℝ) (501594265891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 4 (501594265919/1000000000000 : ℝ) (501594265927/1000000000000 : ℝ) (250797132941/500000000000 : ℝ) (501594265891/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 5 (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 6 (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33597/262144 : ℝ))) 7 (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33597/262144 : ℝ)) hmem 8 (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33597/262144 : ℝ))) hcmem 8 (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33597/262144 : ℝ)) (49601887971/50000000000 : ℝ) (15500589991/15625000000 : ℝ) (5015942659/10000000000 : ℝ) (501594265909/1000000000000 : ℝ) (397113125449/500000000000 : ℝ) (198556562729/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1121_exp_lower
  have heNumeric : (2054902880817/1000000000000 : ℝ)/4 ≤ Real.exp (-85256419101623/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902880817/1000000000000 : ℝ)/4 ≤ Real.exp ((67193/524288 : ℝ)-(198556562729/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67193/524288 : ℝ) (33597/262144 : ℝ) (198556562729/250000000000 : ℝ) (2054902880817/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1122; no trusted numerical premise.
theorem cover8_leaf1122_exp_radius : (249499859186688793/250000000000000000 : ℝ) ≤ Real.exp ((-67195/4194304 : ℝ)/8) ∧ Real.exp ((-67195/4194304 : ℝ)/8) ≤ (997999436746755173/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67195/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1122_exp_lower : (28753547617830153/31250000000000000 : ℝ) ≤ Real.exp ((-42628209228211/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628209228211/64000000000000 : ℝ)/8) ≤ (920113523770564897/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628209228211/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1122_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196115647/40000000000 : ℝ) ≤ 4*Real.exp (33597/262144 : ℝ)*Real.exp (-mu (radius 8 (67195/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (82196115647/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67195/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1122_exp_radius
  have hrNumeric : (61506694363/62500000000 : ℝ) ≤ Real.exp (-67195/4194304 : ℝ) ∧ Real.exp (-67195/4194304 : ℝ) ≤ (984107109809/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61506694363/62500000000 : ℝ) ≤ (radius 8 (67195/524288 : ℝ)) ∧ (radius 8 (67195/524288 : ℝ)) ≤ (984107109809/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67195/524288 : ℝ)) (61506694363/62500000000 : ℝ) (984107109809/1000000000000 : ℝ) (88787944597/500000000000 : ℝ) (177575889201/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67195/524288 : ℝ)) (61506694363/62500000000 : ℝ) (984107109809/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61506694363/62500000000 : ℝ) (984107109809/1000000000000 : ℝ) (124006694363/125000000000 : ℝ) (198410710981/200000000000 : ℝ) (198404345699/200000000000 : ℝ) (992021728497/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 1 (124006694363/125000000000 : ℝ) (198410710981/200000000000 : ℝ) (198404345699/200000000000 : ℝ) (992021728497/1000000000000 : ℝ) (992037641699/1000000000000 : ℝ) (992037641701/1000000000000 : ℝ) (992037641571/1000000000000 : ℝ) (496018820787/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 2 (992037641699/1000000000000 : ℝ) (992037641701/1000000000000 : ℝ) (992037641571/1000000000000 : ℝ) (496018820787/500000000000 : ℝ) (198407528327/200000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 3 (198407528327/200000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 4 (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 5 (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 6 (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67195/524288 : ℝ)) 7 (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67195/524288 : ℝ))) (88787944597/500000000000 : ℝ) (177575889201/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88787944597/500000000000 : ℝ) (177575889201/1000000000000 : ℝ) (588787944597/1000000000000 : ℝ) (588787944601/1000000000000 : ℝ) (421397542937/1000000000000 : ℝ) (421397542947/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 1 (588787944597/1000000000000 : ℝ) (588787944601/1000000000000 : ℝ) (421397542937/1000000000000 : ℝ) (421397542947/1000000000000 : ℝ) (505092743767/1000000000000 : ℝ) (252546371887/500000000000 : ℝ) (249055110951/500000000000 : ℝ) (498110221911/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 2 (505092743767/1000000000000 : ℝ) (252546371887/500000000000 : ℝ) (249055110951/500000000000 : ℝ) (498110221911/1000000000000 : ℝ) (250800741417/500000000000 : ℝ) (501601482843/1000000000000 : ℝ) (5015893327/10000000000 : ℝ) (501589332709/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 3 (250800741417/500000000000 : ℝ) (501601482843/1000000000000 : ℝ) (5015893327/10000000000 : ℝ) (501589332709/1000000000000 : ℝ) (501595407767/1000000000000 : ℝ) (15674856493/31250000000 : ℝ) (50159540773/100000000000 : ℝ) (25079770387/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 4 (501595407767/1000000000000 : ℝ) (15674856493/31250000000 : ℝ) (50159540773/100000000000 : ℝ) (25079770387/50000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 5 (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 6 (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67195/524288 : ℝ))) 7 (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67195/524288 : ℝ)) hmem 8 (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67195/524288 : ℝ))) hcmem 8 (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67195/524288 : ℝ)) (496018820817/500000000000 : ℝ) (496018820819/500000000000 : ℝ) (125398851937/250000000000 : ℝ) (250797703879/500000000000 : ℝ) (198557038301/250000000000 : ℝ) (99278519153/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1122_exp_lower
  have heNumeric : (82196115647/40000000000 : ℝ)/4 ≤ Real.exp (-42628209228211/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196115647/40000000000 : ℝ)/4 ≤ Real.exp ((33597/262144 : ℝ)-(99278519153/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33597/262144 : ℝ) (67195/524288 : ℝ) (99278519153/125000000000 : ℝ) (82196115647/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1123; no trusted numerical premise.
theorem cover8_leaf1123_exp_radius : (498999703502027329/500000000000000000 : ℝ) ≤ Real.exp ((-16799/1048576 : ℝ)/8) ∧ Real.exp ((-16799/1048576 : ℝ)/8) ≤ (997999407004054659/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16799/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1123_exp_lower : (920113524351689369/1000000000000000000 : ℝ) ≤ Real.exp ((-17051283561937/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051283561937/25600000000000 : ℝ)/8) ≤ (92011352435168937/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051283561937/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1123_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902901557/1000000000000 : ℝ) ≤ 4*Real.exp (67195/524288 : ℝ)*Real.exp (-mu (radius 8 (16799/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902901557/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16799/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1123_exp_radius
  have hrNumeric : (492053437589/500000000000 : ℝ) ≤ Real.exp (-16799/1048576 : ℝ) ∧ Real.exp (-16799/1048576 : ℝ) ≤ (984106875179/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492053437589/500000000000 : ℝ) ≤ (radius 8 (16799/131072 : ℝ)) ∧ (radius 8 (16799/131072 : ℝ)) ≤ (984106875179/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16799/131072 : ℝ)) (492053437589/500000000000 : ℝ) (984106875179/1000000000000 : ℝ) (35515437897/200000000000 : ℝ) (177577189491/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16799/131072 : ℝ)) (492053437589/500000000000 : ℝ) (984106875179/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492053437589/500000000000 : ℝ) (984106875179/1000000000000 : ℝ) (992053437589/1000000000000 : ℝ) (99205343759/100000000000 : ℝ) (992021610237/1000000000000 : ℝ) (496010805119/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 1 (992053437589/1000000000000 : ℝ) (99205343759/100000000000 : ℝ) (992021610237/1000000000000 : ℝ) (496010805119/500000000000 : ℝ) (992037523913/1000000000000 : ℝ) (496018761957/500000000000 : ℝ) (198407504757/200000000000 : ℝ) (992037523787/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 2 (992037523913/1000000000000 : ℝ) (496018761957/500000000000 : ℝ) (198407504757/200000000000 : ℝ) (992037523787/1000000000000 : ℝ) (992037523849/1000000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 3 (992037523849/1000000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 4 (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 5 (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 6 (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16799/131072 : ℝ)) 7 (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16799/131072 : ℝ))) (35515437897/200000000000 : ℝ) (177577189491/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35515437897/200000000000 : ℝ) (177577189491/1000000000000 : ℝ) (294394297371/500000000000 : ℝ) (294394297373/500000000000 : ℝ) (210699542883/500000000000 : ℝ) (210699542887/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 1 (294394297371/500000000000 : ℝ) (294394297373/500000000000 : ℝ) (210699542883/500000000000 : ℝ) (210699542887/500000000000 : ℝ) (252546920127/500000000000 : ℝ) (25254692013/50000000000 : ℝ) (124527852189/250000000000 : ℝ) (124527852191/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 2 (252546920127/500000000000 : ℝ) (25254692013/50000000000 : ℝ) (124527852189/250000000000 : ℝ) (124527852191/250000000000 : ℝ) (100320524901/200000000000 : ℝ) (489846313/976562500 : ℝ) (501590474713/1000000000000 : ℝ) (501590474721/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 3 (100320524901/200000000000 : ℝ) (489846313/976562500 : ℝ) (501590474713/1000000000000 : ℝ) (501590474721/1000000000000 : ℝ) (501596549609/1000000000000 : ℝ) (501596549617/1000000000000 : ℝ) (125399137393/250000000000 : ℝ) (25079827479/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 4 (501596549609/1000000000000 : ℝ) (501596549617/1000000000000 : ℝ) (125399137393/250000000000 : ℝ) (25079827479/50000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 5 (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 6 (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16799/131072 : ℝ))) 7 (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16799/131072 : ℝ)) hmem 8 (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16799/131072 : ℝ))) hcmem 8 (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16799/131072 : ℝ)) (124004690481/125000000000 : ℝ) (992037523851/1000000000000 : ℝ) (50159654959/100000000000 : ℝ) (501596549599/1000000000000 : ℝ) (397115027751/500000000000 : ℝ) (4963937847/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1123_exp_lower
  have heNumeric : (2054902901557/1000000000000 : ℝ)/4 ≤ Real.exp (-17051283561937/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902901557/1000000000000 : ℝ)/4 ≤ Real.exp ((67195/524288 : ℝ)-(4963937847/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67195/524288 : ℝ) (16799/131072 : ℝ) (4963937847/6250000000 : ℝ) (2054902901557/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1124; no trusted numerical premise.
theorem cover8_leaf1124_exp_radius : (997999377261355031/1000000000000000000 : ℝ) ≤ Real.exp ((-67197/4194304 : ℝ)/8) ∧ Real.exp ((-67197/4194304 : ℝ)/8) ≤ (124749922157669379/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67197/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1124_exp_lower : (920113524935804211/1000000000000000000 : ℝ) ≤ Real.exp ((-4262820857981/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262820857981/6400000000000 : ℝ)/8) ≤ (230028381233951053/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262820857981/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1124_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451455997/500000000000 : ℝ) ≤ 4*Real.exp (16799/131072 : ℝ)*Real.exp (-mu (radius 8 (67197/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451455997/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67197/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1124_exp_radius
  have hrNumeric : (984106640549/1000000000000 : ℝ) ≤ Real.exp (-67197/4194304 : ℝ) ∧ Real.exp (-67197/4194304 : ℝ) ≤ (19682132811/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984106640549/1000000000000 : ℝ) ≤ (radius 8 (67197/524288 : ℝ)) ∧ (radius 8 (67197/524288 : ℝ)) ≤ (19682132811/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67197/524288 : ℝ)) (984106640549/1000000000000 : ℝ) (19682132811/20000000000 : ℝ) (177578489759/1000000000000 : ℝ) (88789244883/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67197/524288 : ℝ)) (984106640549/1000000000000 : ℝ) (19682132811/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984106640549/1000000000000 : ℝ) (19682132811/20000000000 : ℝ) (496026660137/500000000000 : ℝ) (39682132811/40000000000 : ℝ) (992021491979/1000000000000 : ℝ) (49601074599/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 1 (496026660137/500000000000 : ℝ) (39682132811/40000000000 : ℝ) (992021491979/1000000000000 : ℝ) (49601074599/50000000000 : ℝ) (496018703063/500000000000 : ℝ) (62002337883/62500000000 : ℝ) (496018702999/500000000000 : ℝ) (496018703/500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 2 (496018703063/500000000000 : ℝ) (62002337883/62500000000 : ℝ) (496018702999/500000000000 : ℝ) (496018703/500000000 : ℝ) (496018703031/500000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 3 (496018703031/500000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 4 (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 5 (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 6 (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67197/524288 : ℝ)) 7 (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67197/524288 : ℝ))) (177578489759/1000000000000 : ℝ) (88789244883/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177578489759/1000000000000 : ℝ) (88789244883/500000000000 : ℝ) (588789244879/1000000000000 : ℝ) (588789244883/1000000000000 : ℝ) (421400628569/1000000000000 : ℝ) (421400628579/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 1 (588789244879/1000000000000 : ℝ) (588789244883/1000000000000 : ℝ) (421400628569/1000000000000 : ℝ) (421400628579/1000000000000 : ℝ) (126273734181/250000000000 : ℝ) (505094936731/1000000000000 : ℝ) (498112595591/1000000000000 : ℝ) (498112595599/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 2 (126273734181/250000000000 : ℝ) (505094936731/1000000000000 : ℝ) (498112595591/1000000000000 : ℝ) (498112595599/1000000000000 : ℝ) (501603766157/1000000000000 : ℝ) (100320753233/200000000000 : ℝ) (501591616707/1000000000000 : ℝ) (125397904179/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 3 (501603766157/1000000000000 : ℝ) (100320753233/200000000000 : ℝ) (501591616707/1000000000000 : ℝ) (125397904179/250000000000 : ℝ) (62699711429/125000000000 : ℝ) (501597691441/1000000000000 : ℝ) (100319538279/200000000000 : ℝ) (125399422851/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 4 (62699711429/125000000000 : ℝ) (501597691441/1000000000000 : ℝ) (100319538279/200000000000 : ℝ) (125399422851/250000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 5 (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 6 (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67197/524288 : ℝ))) 7 (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67197/524288 : ℝ)) hmem 8 (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67197/524288 : ℝ))) hcmem 8 (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67197/524288 : ℝ)) (992037406061/1000000000000 : ℝ) (62002337879/62500000000 : ℝ) (501597691413/1000000000000 : ℝ) (501597691423/1000000000000 : ℝ) (794231957771/1000000000000 : ℝ) (79423195779/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1124_exp_lower
  have heNumeric : (1027451455997/500000000000 : ℝ)/4 ≤ Real.exp (-4262820857981/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451455997/500000000000 : ℝ)/4 ≤ Real.exp ((16799/131072 : ℝ)-(79423195779/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16799/131072 : ℝ) (67197/524288 : ℝ) (79423195779/100000000000 : ℝ) (1027451455997/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1100_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1100_certificate
#check SmaleRate.Proofs.cover8_leaf1101_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1101_certificate
#check SmaleRate.Proofs.cover8_leaf1102_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1102_certificate
#check SmaleRate.Proofs.cover8_leaf1103_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1103_certificate
#check SmaleRate.Proofs.cover8_leaf1104_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1104_certificate
#check SmaleRate.Proofs.cover8_leaf1105_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1105_certificate
#check SmaleRate.Proofs.cover8_leaf1106_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1106_certificate
#check SmaleRate.Proofs.cover8_leaf1107_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1107_certificate
#check SmaleRate.Proofs.cover8_leaf1108_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1108_certificate
#check SmaleRate.Proofs.cover8_leaf1109_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1109_certificate
#check SmaleRate.Proofs.cover8_leaf1110_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1110_certificate
#check SmaleRate.Proofs.cover8_leaf1111_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1111_certificate
#check SmaleRate.Proofs.cover8_leaf1112_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1112_certificate
#check SmaleRate.Proofs.cover8_leaf1113_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1113_certificate
#check SmaleRate.Proofs.cover8_leaf1114_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1114_certificate
#check SmaleRate.Proofs.cover8_leaf1115_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1115_certificate
#check SmaleRate.Proofs.cover8_leaf1116_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1116_certificate
#check SmaleRate.Proofs.cover8_leaf1117_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1117_certificate
#check SmaleRate.Proofs.cover8_leaf1118_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1118_certificate
#check SmaleRate.Proofs.cover8_leaf1119_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1119_certificate
#check SmaleRate.Proofs.cover8_leaf1120_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1120_certificate
#check SmaleRate.Proofs.cover8_leaf1121_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1121_certificate
#check SmaleRate.Proofs.cover8_leaf1122_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1122_certificate
#check SmaleRate.Proofs.cover8_leaf1123_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1123_certificate
#check SmaleRate.Proofs.cover8_leaf1124_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1124_certificate
