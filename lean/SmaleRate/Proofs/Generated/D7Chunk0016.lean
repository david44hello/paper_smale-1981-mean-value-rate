/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0400; no trusted numerical premise.
theorem cover7_leaf0400_exp_radius : (997547709142906383/1000000000000000000 : ℝ) ≤ Real.exp ((-9011/458752 : ℝ)/8) ∧ Real.exp ((-9011/458752 : ℝ)/8) ≤ (62346731821431649/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9011/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0400_exp_lower : (229522370430426549/250000000000000000 : ℝ) ≤ Real.exp ((-1093893356411/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093893356411/1600000000000 : ℝ)/8) ≤ (918089481721706197/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093893356411/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0400_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019017512947/1000000000000 : ℝ) ≤ 4*Real.exp (4505/32768 : ℝ)*Real.exp (-mu (radius 7 (9011/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019017512947/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9011/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0400_exp_radius
  have hrNumeric : (980549234267/1000000000000 : ℝ) ≤ Real.exp (-9011/458752 : ℝ) ∧ Real.exp (-9011/458752 : ℝ) ≤ (245137308567/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980549234267/1000000000000 : ℝ) ≤ (radius 7 (9011/65536 : ℝ)) ∧ (radius 7 (9011/65536 : ℝ)) ≤ (245137308567/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9011/65536 : ℝ)) (980549234267/1000000000000 : ℝ) (245137308567/250000000000 : ℝ) (24534159597/125000000000 : ℝ) (98136638391/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9011/65536 : ℝ)) (980549234267/1000000000000 : ℝ) (245137308567/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980549234267/1000000000000 : ℝ) (245137308567/250000000000 : ℝ) (990274617133/1000000000000 : ℝ) (495137308567/500000000000 : ℝ) (49511343/50000000 : ℝ) (495113430001/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 1 (990274617133/1000000000000 : ℝ) (495137308567/500000000000 : ℝ) (49511343/50000000 : ℝ) (495113430001/500000000000 : ℝ) (495125369283/500000000000 : ℝ) (123781342321/125000000000 : ℝ) (495125369139/500000000000 : ℝ) (990250738281/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 2 (495125369283/500000000000 : ℝ) (123781342321/125000000000 : ℝ) (495125369139/500000000000 : ℝ) (990250738281/1000000000000 : ℝ) (495125369211/500000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 3 (495125369211/500000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 4 (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 5 (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 6 (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9011/65536 : ℝ)) 7 (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9011/65536 : ℝ))) (24534159597/125000000000 : ℝ) (98136638391/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24534159597/125000000000 : ℝ) (98136638391/500000000000 : ℝ) (149534159597/250000000000 : ℝ) (598136638391/1000000000000 : ℝ) (443027399577/1000000000000 : ℝ) (13844606237/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 1 (149534159597/250000000000 : ℝ) (598136638391/1000000000000 : ℝ) (443027399577/1000000000000 : ℝ) (13844606237/31250000000 : ℝ) (260291009491/500000000000 : ℝ) (130145504747/250000000000 : ℝ) (514772687209/1000000000000 : ℝ) (102954537443/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 2 (260291009491/500000000000 : ℝ) (130145504747/250000000000 : ℝ) (514772687209/1000000000000 : ℝ) (102954537443/200000000000 : ℝ) (103535470619/200000000000 : ℝ) (258838676551/500000000000 : ℝ) (129417301013/250000000000 : ℝ) (517669204059/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 3 (103535470619/200000000000 : ℝ) (258838676551/500000000000 : ℝ) (129417301013/250000000000 : ℝ) (517669204059/1000000000000 : ℝ) (517673278573/1000000000000 : ℝ) (517673278581/1000000000000 : ℝ) (517673278557/1000000000000 : ℝ) (103534655713/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 4 (517673278573/1000000000000 : ℝ) (517673278581/1000000000000 : ℝ) (517673278557/1000000000000 : ℝ) (103534655713/200000000000 : ℝ) (103534655713/200000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 5 (103534655713/200000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 6 (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9011/65536 : ℝ))) 7 (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9011/65536 : ℝ)) hmem 8 (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9011/65536 : ℝ))) hcmem 8 (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9011/65536 : ℝ)) (990250738421/1000000000000 : ℝ) (39610029537/40000000000 : ℝ) (129418319641/250000000000 : ℝ) (517673278573/1000000000000 : ℝ) (102645629649/125000000000 : ℝ) (82116503721/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0400_exp_lower
  have heNumeric : (2019017512947/1000000000000 : ℝ)/4 ≤ Real.exp (-1093893356411/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019017512947/1000000000000 : ℝ)/4 ≤ Real.exp ((4505/32768 : ℝ)-(82116503721/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4505/32768 : ℝ) (9011/65536 : ℝ) (82116503721/100000000000 : ℝ) (2019017512947/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0401; no trusted numerical premise.
theorem cover7_leaf0401_exp_radius : (124693429666595441/125000000000000000 : ℝ) ≤ Real.exp ((-2253/114688 : ℝ)/8) ∧ Real.exp ((-2253/114688 : ℝ)/8) ≤ (997547437332763529/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2253/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0401_exp_lower : (229522373168572857/250000000000000000 : ℝ) ≤ Real.exp ((-10938932037101/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938932037101/16000000000000 : ℝ)/8) ≤ (918089492674291429/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938932037101/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0401_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009508852819/500000000000 : ℝ) ≤ 4*Real.exp (9011/65536 : ℝ)*Real.exp (-mu (radius 7 (2253/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009508852819/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2253/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0401_exp_radius
  have hrNumeric : (980547096841/1000000000000 : ℝ) ≤ Real.exp (-2253/114688 : ℝ) ∧ Real.exp (-2253/114688 : ℝ) ≤ (490273548421/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980547096841/1000000000000 : ℝ) ≤ (radius 7 (2253/16384 : ℝ)) ∧ (radius 7 (2253/16384 : ℝ)) ≤ (490273548421/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2253/16384 : ℝ)) (980547096841/1000000000000 : ℝ) (490273548421/500000000000 : ℝ) (39256790941/200000000000 : ℝ) (196283954711/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2253/16384 : ℝ)) (980547096841/1000000000000 : ℝ) (490273548421/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980547096841/1000000000000 : ℝ) (490273548421/500000000000 : ℝ) (49513677421/50000000000 : ℝ) (990273548421/1000000000000 : ℝ) (990225780739/1000000000000 : ℝ) (49511289037/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 1 (49513677421/50000000000 : ℝ) (990273548421/1000000000000 : ℝ) (990225780739/1000000000000 : ℝ) (49511289037/50000000000 : ℝ) (990249664579/1000000000000 : ℝ) (990249664581/1000000000000 : ℝ) (990249664291/1000000000000 : ℝ) (990249664293/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 2 (990249664579/1000000000000 : ℝ) (990249664581/1000000000000 : ℝ) (990249664291/1000000000000 : ℝ) (990249664293/1000000000000 : ℝ) (198049932887/200000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 3 (198049932887/200000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 4 (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 5 (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 6 (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2253/16384 : ℝ)) 7 (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2253/16384 : ℝ))) (39256790941/200000000000 : ℝ) (196283954711/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39256790941/200000000000 : ℝ) (196283954711/1000000000000 : ℝ) (74767747169/125000000000 : ℝ) (149535494339/250000000000 : ℝ) (221519725253/500000000000 : ℝ) (221519725257/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 1 (74767747169/125000000000 : ℝ) (149535494339/250000000000 : ℝ) (221519725253/500000000000 : ℝ) (221519725257/500000000000 : ℝ) (520590713929/1000000000000 : ℝ) (104118142787/200000000000 : ℝ) (64347748233/125000000000 : ℝ) (514781985871/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 2 (520590713929/1000000000000 : ℝ) (104118142787/200000000000 : ℝ) (64347748233/125000000000 : ℝ) (514781985871/1000000000000 : ℝ) (64710793737/125000000000 : ℝ) (517686349903/1000000000000 : ℝ) (8088721917/15625000000 : ℝ) (103535640539/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 3 (64710793737/125000000000 : ℝ) (517686349903/1000000000000 : ℝ) (8088721917/15625000000 : ℝ) (103535640539/200000000000 : ℝ) (129420569073/250000000000 : ℝ) (517682276299/1000000000000 : ℝ) (20707291051/40000000000 : ℝ) (517682276283/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 4 (129420569073/250000000000 : ℝ) (517682276299/1000000000000 : ℝ) (20707291051/40000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 5 (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 6 (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2253/16384 : ℝ))) 7 (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2253/16384 : ℝ)) hmem 8 (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2253/16384 : ℝ))) hcmem 8 (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2253/16384 : ℝ)) (495124832217/500000000000 : ℝ) (990249664437/1000000000000 : ℝ) (517682276283/1000000000000 : ℝ) (517682276291/1000000000000 : ℝ) (164236040109/200000000000 : ℝ) (821180200561/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0401_exp_lower
  have heNumeric : (1009508852819/500000000000 : ℝ)/4 ≤ Real.exp (-10938932037101/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009508852819/500000000000 : ℝ)/4 ≤ Real.exp ((9011/65536 : ℝ)-(821180200561/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9011/65536 : ℝ) (2253/16384 : ℝ) (821180200561/1000000000000 : ℝ) (1009508852819/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0402; no trusted numerical premise.
theorem cover7_leaf0402_exp_radius : (62346697845168421/62500000000000000 : ℝ) ≤ Real.exp ((-9013/458752 : ℝ)/8) ∧ Real.exp ((-9013/458752 : ℝ)/8) ≤ (997547165522694737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9013/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0402_exp_lower : (229522375938909711/250000000000000000 : ℝ) ≤ Real.exp ((-546946524607/800000000000 : ℝ)/8) ∧ Real.exp ((-546946524607/800000000000 : ℝ)/8) ≤ (183617900751127769/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546946524607/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0402_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009508950297/500000000000 : ℝ) ≤ 4*Real.exp (2253/16384 : ℝ)*Real.exp (-mu (radius 7 (9013/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009508950297/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9013/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0402_exp_radius
  have hrNumeric : (49027247971/50000000000 : ℝ) ≤ Real.exp (-9013/458752 : ℝ) ∧ Real.exp (-9013/458752 : ℝ) ≤ (980544959421/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49027247971/50000000000 : ℝ) ≤ (radius 7 (9013/65536 : ℝ)) ∧ (radius 7 (9013/65536 : ℝ)) ≤ (980544959421/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9013/65536 : ℝ)) (49027247971/50000000000 : ℝ) (980544959421/1000000000000 : ℝ) (39258926401/200000000000 : ℝ) (196294632011/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9013/65536 : ℝ)) (49027247971/50000000000 : ℝ) (980544959421/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49027247971/50000000000 : ℝ) (980544959421/1000000000000 : ℝ) (99027247971/100000000000 : ℝ) (990272479711/1000000000000 : ℝ) (990224701479/1000000000000 : ℝ) (24755617537/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 1 (99027247971/100000000000 : ℝ) (990272479711/1000000000000 : ℝ) (990224701479/1000000000000 : ℝ) (24755617537/25000000000 : ℝ) (495124295297/500000000000 : ℝ) (247562147649/250000000000 : ℝ) (495124295153/500000000000 : ℝ) (247562147577/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 2 (495124295297/500000000000 : ℝ) (247562147649/250000000000 : ℝ) (495124295153/500000000000 : ℝ) (247562147577/250000000000 : ℝ) (19804971809/20000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 3 (19804971809/20000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 4 (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 5 (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 6 (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9013/65536 : ℝ)) 7 (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9013/65536 : ℝ))) (39258926401/200000000000 : ℝ) (196294632011/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39258926401/200000000000 : ℝ) (196294632011/1000000000000 : ℝ) (299073658001/500000000000 : ℝ) (299073658003/500000000000 : ℝ) (221525750199/500000000000 : ℝ) (88610300081/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 1 (299073658001/500000000000 : ℝ) (299073658003/500000000000 : ℝ) (221525750199/500000000000 : ℝ) (88610300081/200000000000 : ℝ) (2602997041/5000000000 : ℝ) (260299704103/500000000000 : ℝ) (514791283739/1000000000000 : ℝ) (102958256749/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 2 (2602997041/5000000000 : ℝ) (260299704103/500000000000 : ℝ) (514791283739/1000000000000 : ℝ) (102958256749/200000000000 : ℝ) (517695345969/1000000000000 : ℝ) (64711918247/125000000000 : ℝ) (129421800149/250000000000 : ℝ) (517687200603/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 3 (517695345969/1000000000000 : ℝ) (64711918247/125000000000 : ℝ) (129421800149/250000000000 : ℝ) (517687200603/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (51769127329/100000000000 : ℝ) (258845636633/500000000000 : ℝ) (258845636637/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 4 (258845636641/500000000000 : ℝ) (51769127329/100000000000 : ℝ) (258845636633/500000000000 : ℝ) (258845636637/500000000000 : ℝ) (258845636637/500000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 5 (258845636637/500000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 6 (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9013/65536 : ℝ))) 7 (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9013/65536 : ℝ)) hmem 8 (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9013/65536 : ℝ))) hcmem 8 (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9013/65536 : ℝ)) (990248590449/1000000000000 : ℝ) (247562147613/250000000000 : ℝ) (517691273273/1000000000000 : ℝ) (258845636641/500000000000 : ℝ) (205298840693/250000000000 : ℝ) (82119536279/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0402_exp_lower
  have heNumeric : (1009508950297/500000000000 : ℝ)/4 ≤ Real.exp (-546946524607/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009508950297/500000000000 : ℝ)/4 ≤ Real.exp ((2253/16384 : ℝ)-(82119536279/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2253/16384 : ℝ) (9013/65536 : ℝ) (82119536279/100000000000 : ℝ) (1009508950297/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0403; no trusted numerical premise.
theorem cover7_leaf0403_exp_radius : (997546893712700007/1000000000000000000 : ℝ) ≤ Real.exp ((-4507/229376 : ℝ)/8) ∧ Real.exp ((-4507/229376 : ℝ)/8) ≤ (124693361714087501/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4507/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0403_exp_lower : (459044757483161127/500000000000000000 : ℝ) ≤ Real.exp ((-10938928929147/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938928929147/16000000000000 : ℝ)/8) ≤ (183617902993264451/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938928929147/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0403_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509048913/500000000000 : ℝ) ≤ 4*Real.exp (9013/65536 : ℝ)*Real.exp (-mu (radius 7 (4507/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509048913/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4507/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0403_exp_radius
  have hrNumeric : (245135705501/250000000000 : ℝ) ≤ Real.exp (-4507/229376 : ℝ) ∧ Real.exp (-4507/229376 : ℝ) ≤ (196108564401/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245135705501/250000000000 : ℝ) ≤ (radius 7 (4507/32768 : ℝ)) ∧ (radius 7 (4507/32768 : ℝ)) ≤ (196108564401/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4507/32768 : ℝ)) (245135705501/250000000000 : ℝ) (196108564401/200000000000 : ℝ) (49076327169/250000000000 : ℝ) (98152654341/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4507/32768 : ℝ)) (245135705501/250000000000 : ℝ) (196108564401/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245135705501/250000000000 : ℝ) (196108564401/200000000000 : ℝ) (495135705501/500000000000 : ℝ) (990271411003/1000000000000 : ℝ) (49511181111/50000000000 : ℝ) (495111811111/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 1 (495135705501/500000000000 : ℝ) (990271411003/1000000000000 : ℝ) (49511181111/50000000000 : ℝ) (495111811111/500000000000 : ℝ) (990247516611/1000000000000 : ℝ) (990247516613/1000000000000 : ℝ) (495123758161/500000000000 : ℝ) (39609900653/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 2 (990247516611/1000000000000 : ℝ) (990247516613/1000000000000 : ℝ) (495123758161/500000000000 : ℝ) (39609900653/40000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 3 (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 4 (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 5 (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 6 (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4507/32768 : ℝ)) 7 (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4507/32768 : ℝ))) (49076327169/250000000000 : ℝ) (98152654341/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49076327169/250000000000 : ℝ) (98152654341/500000000000 : ℝ) (299076327169/500000000000 : ℝ) (598152654341/1000000000000 : ℝ) (110765887313/250000000000 : ℝ) (22153177463/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 1 (299076327169/500000000000 : ℝ) (598152654341/1000000000000 : ℝ) (110765887313/250000000000 : ℝ) (22153177463/50000000000 : ℝ) (104121620359/200000000000 : ℝ) (520608101801/1000000000000 : ℝ) (16087518151/31250000000 : ℝ) (514800580839/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 2 (104121620359/200000000000 : ℝ) (520608101801/1000000000000 : ℝ) (16087518151/31250000000 : ℝ) (514800580839/1000000000000 : ℝ) (517704341313/1000000000000 : ℝ) (12942608533/25000000000 : ℝ) (258848098887/500000000000 : ℝ) (517696197781/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 3 (517704341313/1000000000000 : ℝ) (12942608533/25000000000 : ℝ) (258848098887/500000000000 : ℝ) (517696197781/1000000000000 : ℝ) (517700269543/1000000000000 : ℝ) (517700269551/1000000000000 : ℝ) (517700269527/1000000000000 : ℝ) (103540053907/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 4 (517700269543/1000000000000 : ℝ) (517700269551/1000000000000 : ℝ) (517700269527/1000000000000 : ℝ) (103540053907/200000000000 : ℝ) (103540053907/200000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 5 (103540053907/200000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 6 (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4507/32768 : ℝ))) 7 (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4507/32768 : ℝ)) hmem 8 (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4507/32768 : ℝ))) hcmem 8 (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4507/32768 : ℝ)) (495123758233/500000000000 : ℝ) (990247516469/1000000000000 : ℝ) (258850134767/500000000000 : ℝ) (517700269543/1000000000000 : ℝ) (410605261937/500000000000 : ℝ) (205302630973/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0403_exp_lower
  have heNumeric : (1009509048913/500000000000 : ℝ)/4 ≤ Real.exp (-10938928929147/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509048913/500000000000 : ℝ)/4 ≤ Real.exp ((9013/65536 : ℝ)-(205302630973/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9013/65536 : ℝ) (4507/32768 : ℝ) (205302630973/250000000000 : ℝ) (1009509048913/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0404; no trusted numerical premise.
theorem cover7_leaf0404_exp_radius : (997546621902779339/1000000000000000000 : ℝ) ≤ Real.exp ((-9015/458752 : ℝ)/8) ∧ Real.exp ((-9015/458752 : ℝ)/8) ≤ (49877331095138967/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9015/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0404_exp_lower : (918089526306112141/1000000000000000000 : ℝ) ≤ Real.exp ((-5469463674077/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469463674077/8000000000000 : ℝ)/8) ≤ (459044763153056071/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469463674077/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0404_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901829733/100000000000 : ℝ) ≤ 4*Real.exp (4507/32768 : ℝ)*Real.exp (-mu (radius 7 (9015/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201901829733/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9015/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0404_exp_radius
  have hrNumeric : (980540684593/1000000000000 : ℝ) ≤ Real.exp (-9015/458752 : ℝ) ∧ Real.exp (-9015/458752 : ℝ) ≤ (490270342297/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980540684593/1000000000000 : ℝ) ≤ (radius 7 (9015/65536 : ℝ)) ∧ (radius 7 (9015/65536 : ℝ)) ≤ (490270342297/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9015/65536 : ℝ)) (980540684593/1000000000000 : ℝ) (490270342297/500000000000 : ℝ) (98157992359/500000000000 : ℝ) (49078996181/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9015/65536 : ℝ)) (980540684593/1000000000000 : ℝ) (490270342297/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980540684593/1000000000000 : ℝ) (490270342297/500000000000 : ℝ) (123783792787/125000000000 : ℝ) (990270342297/1000000000000 : ℝ) (990222542963/1000000000000 : ℝ) (247555635741/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 1 (123783792787/125000000000 : ℝ) (990270342297/1000000000000 : ℝ) (990222542963/1000000000000 : ℝ) (247555635741/250000000000 : ℝ) (990246442629/1000000000000 : ℝ) (990246442631/1000000000000 : ℝ) (990246442341/1000000000000 : ℝ) (990246442343/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 2 (990246442629/1000000000000 : ℝ) (990246442631/1000000000000 : ℝ) (990246442341/1000000000000 : ℝ) (990246442343/1000000000000 : ℝ) (198049288497/200000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 3 (198049288497/200000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 4 (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 5 (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 6 (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9015/65536 : ℝ)) 7 (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9015/65536 : ℝ))) (98157992359/500000000000 : ℝ) (49078996181/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98157992359/500000000000 : ℝ) (49078996181/250000000000 : ℝ) (598157992359/1000000000000 : ℝ) (299078996181/500000000000 : ℝ) (110768899267/250000000000 : ℝ) (110768899269/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 1 (598157992359/1000000000000 : ℝ) (299078996181/500000000000 : ℝ) (110768899267/250000000000 : ℝ) (110768899269/250000000000 : ℝ) (520616794713/1000000000000 : ℝ) (520616794719/1000000000000 : ℝ) (64351234643/125000000000 : ℝ) (514809877151/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 2 (520616794713/1000000000000 : ℝ) (520616794719/1000000000000 : ℝ) (64351234643/125000000000 : ℝ) (514809877151/1000000000000 : ℝ) (64714166991/125000000000 : ℝ) (103542667187/200000000000 : ℝ) (258852597111/500000000000 : ℝ) (51770519423/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 3 (64714166991/125000000000 : ℝ) (103542667187/200000000000 : ℝ) (258852597111/500000000000 : ℝ) (51770519423/100000000000 : ℝ) (20708370603/40000000000 : ℝ) (517709265083/1000000000000 : ℝ) (258854632529/500000000000 : ℝ) (517709265067/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 4 (20708370603/40000000000 : ℝ) (517709265083/1000000000000 : ℝ) (258854632529/500000000000 : ℝ) (517709265067/1000000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 5 (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 6 (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9015/65536 : ℝ))) 7 (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9015/65536 : ℝ)) hmem 8 (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9015/65536 : ℝ))) hcmem 8 (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9015/65536 : ℝ)) (247561610621/250000000000 : ℝ) (990246442487/1000000000000 : ℝ) (258854632533/500000000000 : ℝ) (20708370603/40000000000 : ℝ) (821225683851/1000000000000 : ℝ) (821225683869/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0404_exp_lower
  have heNumeric : (201901829733/100000000000 : ℝ)/4 ≤ Real.exp (-5469463674077/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901829733/100000000000 : ℝ)/4 ≤ Real.exp ((4507/32768 : ℝ)-(821225683869/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4507/32768 : ℝ) (9015/65536 : ℝ) (821225683869/1000000000000 : ℝ) (201901829733/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0405; no trusted numerical premise.
theorem cover7_leaf0405_exp_radius : (498773175046466367/500000000000000000 : ℝ) ≤ Real.exp ((-161/8192 : ℝ)/8) ∧ Real.exp ((-161/8192 : ℝ)/8) ≤ (199509270018586547/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-161/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0405_exp_lower : (459044768886987829/500000000000000000 : ℝ) ≤ Real.exp ((-2187785149861/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187785149861/3200000000000 : ℝ)/8) ≤ (918089537773975659/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187785149861/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0405_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509249543/500000000000 : ℝ) ≤ 4*Real.exp (9015/65536 : ℝ)*Real.exp (-mu (radius 7 (1127/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509249543/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1127/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0405_exp_radius
  have hrNumeric : (490269273593/500000000000 : ℝ) ≤ Real.exp (-161/8192 : ℝ) ∧ Real.exp (-161/8192 : ℝ) ≤ (980538547187/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490269273593/500000000000 : ℝ) ≤ (radius 7 (1127/8192 : ℝ)) ∧ (radius 7 (1127/8192 : ℝ)) ≤ (980538547187/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1127/8192 : ℝ)) (490269273593/500000000000 : ℝ) (980538547187/1000000000000 : ℝ) (24540832517/125000000000 : ℝ) (98163330071/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1127/8192 : ℝ)) (490269273593/500000000000 : ℝ) (980538547187/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490269273593/500000000000 : ℝ) (980538547187/1000000000000 : ℝ) (990269273593/1000000000000 : ℝ) (495134636797/500000000000 : ℝ) (495110731853/500000000000 : ℝ) (247555365927/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 1 (990269273593/1000000000000 : ℝ) (495134636797/500000000000 : ℝ) (495110731853/500000000000 : ℝ) (247555365927/250000000000 : ℝ) (990245368649/1000000000000 : ℝ) (990245368651/1000000000000 : ℝ) (24756134209/25000000000 : ℝ) (990245368363/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 2 (990245368649/1000000000000 : ℝ) (990245368651/1000000000000 : ℝ) (24756134209/25000000000 : ℝ) (990245368363/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 3 (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 4 (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 5 (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 6 (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1127/8192 : ℝ)) 7 (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1127/8192 : ℝ))) (24540832517/125000000000 : ℝ) (98163330071/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24540832517/125000000000 : ℝ) (98163330071/500000000000 : ℝ) (149540832517/250000000000 : ℝ) (598163330071/1000000000000 : ℝ) (443087643853/1000000000000 : ℝ) (443087643861/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 1 (149540832517/250000000000 : ℝ) (598163330071/1000000000000 : ℝ) (443087643853/1000000000000 : ℝ) (443087643861/1000000000000 : ℝ) (6507818587/12500000000 : ℝ) (260312743483/500000000000 : ℝ) (12870479317/25000000000 : ℝ) (514819172687/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 2 (6507818587/12500000000 : ℝ) (260312743483/500000000000 : ℝ) (12870479317/25000000000 : ℝ) (514819172687/1000000000000 : ℝ) (25886116491/50000000000 : ℝ) (517722329827/1000000000000 : ℝ) (517714189947/1000000000000 : ℝ) (258857094977/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 3 (25886116491/50000000000 : ℝ) (517722329827/1000000000000 : ℝ) (517714189947/1000000000000 : ℝ) (258857094977/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (517718259891/1000000000000 : ℝ) (517718259867/1000000000000 : ℝ) (4141746079/8000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 4 (517718259883/1000000000000 : ℝ) (517718259891/1000000000000 : ℝ) (517718259867/1000000000000 : ℝ) (4141746079/8000000000 : ℝ) (4141746079/8000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 5 (4141746079/8000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 6 (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1127/8192 : ℝ))) 7 (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1127/8192 : ℝ)) hmem 8 (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1127/8192 : ℝ))) hcmem 8 (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1127/8192 : ℝ)) (123780671063/125000000000 : ℝ) (990245368507/1000000000000 : ℝ) (258859129937/500000000000 : ℝ) (517718259883/1000000000000 : ℝ) (102655105339/125000000000 : ℝ) (82124084273/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0405_exp_lower
  have heNumeric : (1009509249543/500000000000 : ℝ)/4 ≤ Real.exp (-2187785149861/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509249543/500000000000 : ℝ)/4 ≤ Real.exp ((9015/65536 : ℝ)-(82124084273/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9015/65536 : ℝ) (1127/8192 : ℝ) (82124084273/100000000000 : ℝ) (1009509249543/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0406; no trusted numerical premise.
theorem cover7_leaf0406_exp_radius : (7793328736587189/7812500000000000 : ℝ) ≤ Real.exp ((-9017/458752 : ℝ)/8) ∧ Real.exp ((-9017/458752 : ℝ)/8) ≤ (997546078283160193/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9017/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0406_exp_lower : (459044774685472831/500000000000000000 : ℝ) ≤ Real.exp ((-1367365516557/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367365516557/2000000000000 : ℝ)/8) ≤ (918089549370945663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367365516557/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0406_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509351557/500000000000 : ℝ) ≤ 4*Real.exp (1127/8192 : ℝ)*Real.exp (-mu (radius 7 (9017/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509351557/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9017/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0406_exp_radius
  have hrNumeric : (122567051223/125000000000 : ℝ) ≤ Real.exp (-9017/458752 : ℝ) ∧ Real.exp (-9017/458752 : ℝ) ≤ (196107281957/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122567051223/125000000000 : ℝ) ≤ (radius 7 (9017/65536 : ℝ)) ∧ (radius 7 (9017/65536 : ℝ)) ≤ (196107281957/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9017/65536 : ℝ)) (122567051223/125000000000 : ℝ) (196107281957/200000000000 : ℝ) (98168667463/500000000000 : ℝ) (49084333733/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9017/65536 : ℝ)) (122567051223/125000000000 : ℝ) (196107281957/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122567051223/125000000000 : ℝ) (196107281957/200000000000 : ℝ) (247567051223/250000000000 : ℝ) (990268204893/1000000000000 : ℝ) (990220384451/1000000000000 : ℝ) (990220384453/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 1 (247567051223/250000000000 : ℝ) (990268204893/1000000000000 : ℝ) (990220384451/1000000000000 : ℝ) (990220384453/1000000000000 : ℝ) (990244294671/1000000000000 : ℝ) (990244294673/1000000000000 : ℝ) (495122147191/500000000000 : ℝ) (198048858877/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 2 (990244294671/1000000000000 : ℝ) (990244294673/1000000000000 : ℝ) (495122147191/500000000000 : ℝ) (198048858877/200000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 3 (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 4 (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 5 (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 6 (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9017/65536 : ℝ)) 7 (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9017/65536 : ℝ))) (98168667463/500000000000 : ℝ) (49084333733/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98168667463/500000000000 : ℝ) (49084333733/250000000000 : ℝ) (598168667463/1000000000000 : ℝ) (299084333733/500000000000 : ℝ) (221549844801/500000000000 : ℝ) (44309968961/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 1 (598168667463/1000000000000 : ℝ) (299084333733/500000000000 : ℝ) (221549844801/500000000000 : ℝ) (44309968961/100000000000 : ℝ) (130158544633/250000000000 : ℝ) (260317089269/500000000000 : ℝ) (102965693487/200000000000 : ℝ) (257414233721/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 2 (130158544633/250000000000 : ℝ) (260317089269/500000000000 : ℝ) (102965693487/200000000000 : ℝ) (257414233721/500000000000 : ℝ) (517731322983/1000000000000 : ℝ) (51773132299/100000000000 : ℝ) (517723184943/1000000000000 : ℝ) (10354463699/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 3 (517731322983/1000000000000 : ℝ) (51773132299/100000000000 : ℝ) (517723184943/1000000000000 : ℝ) (10354463699/20000000000 : ℝ) (517727253963/1000000000000 : ℝ) (51772725397/100000000000 : ℝ) (517727253947/1000000000000 : ℝ) (103545450791/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 4 (517727253963/1000000000000 : ℝ) (51772725397/100000000000 : ℝ) (517727253947/1000000000000 : ℝ) (103545450791/200000000000 : ℝ) (103545450791/200000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 5 (103545450791/200000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 6 (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9017/65536 : ℝ))) 7 (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9017/65536 : ℝ)) hmem 8 (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9017/65536 : ℝ))) hcmem 8 (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9017/65536 : ℝ)) (495122147263/500000000000 : ℝ) (990244294529/1000000000000 : ℝ) (258863626977/500000000000 : ℝ) (517727253963/1000000000000 : ℝ) (821256000449/1000000000000 : ℝ) (410628000233/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0406_exp_lower
  have heNumeric : (1009509351557/500000000000 : ℝ)/4 ≤ Real.exp (-1367365516557/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509351557/500000000000 : ℝ)/4 ≤ Real.exp ((1127/8192 : ℝ)-(410628000233/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1127/8192 : ℝ) (9017/65536 : ℝ) (410628000233/500000000000 : ℝ) (1009509351557/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0407; no trusted numerical premise.
theorem cover7_leaf0407_exp_radius : (997545806473461711/1000000000000000000 : ℝ) ≤ Real.exp ((-4509/229376 : ℝ)/8) ∧ Real.exp ((-4509/229376 : ℝ)/8) ≤ (62346612904591357/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4509/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0407_exp_lower : (918089561096563111/1000000000000000000 : ℝ) ≤ Real.exp ((-10938922497671/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938922497671/16000000000000 : ℝ)/8) ≤ (114761195137070389/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938922497671/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0407_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509454703/500000000000 : ℝ) ≤ 4*Real.exp (9017/65536 : ℝ)*Real.exp (-mu (radius 7 (4509/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509454703/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4509/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0407_exp_radius
  have hrNumeric : (980534272387/1000000000000 : ℝ) ≤ Real.exp (-4509/229376 : ℝ) ∧ Real.exp (-4509/229376 : ℝ) ≤ (245133568097/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980534272387/1000000000000 : ℝ) ≤ (radius 7 (4509/32768 : ℝ)) ∧ (radius 7 (4509/32768 : ℝ)) ≤ (245133568097/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4509/32768 : ℝ)) (980534272387/1000000000000 : ℝ) (245133568097/250000000000 : ℝ) (196348009087/1000000000000 : ℝ) (196348009093/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4509/32768 : ℝ)) (980534272387/1000000000000 : ℝ) (245133568097/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980534272387/1000000000000 : ℝ) (245133568097/250000000000 : ℝ) (990267136193/1000000000000 : ℝ) (495133568097/500000000000 : ℝ) (495109652599/500000000000 : ℝ) (990219305199/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 1 (990267136193/1000000000000 : ℝ) (495133568097/500000000000 : ℝ) (495109652599/500000000000 : ℝ) (990219305199/1000000000000 : ℝ) (198048644139/200000000000 : ℝ) (990243220697/1000000000000 : ℝ) (495121610203/500000000000 : ℝ) (123780402551/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 2 (198048644139/200000000000 : ℝ) (990243220697/1000000000000 : ℝ) (495121610203/500000000000 : ℝ) (123780402551/125000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 3 (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 4 (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 5 (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 6 (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4509/32768 : ℝ)) 7 (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4509/32768 : ℝ))) (196348009087/1000000000000 : ℝ) (196348009093/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196348009087/1000000000000 : ℝ) (196348009093/1000000000000 : ℝ) (598174004543/1000000000000 : ℝ) (598174004547/1000000000000 : ℝ) (221555867157/500000000000 : ℝ) (221555867161/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 1 (598174004543/1000000000000 : ℝ) (598174004547/1000000000000 : ℝ) (221555867157/500000000000 : ℝ) (221555867161/500000000000 : ℝ) (130160717357/250000000000 : ℝ) (104128573887/200000000000 : ℝ) (51483776141/100000000000 : ℝ) (257418880709/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 2 (130160717357/250000000000 : ℝ) (104128573887/200000000000 : ℝ) (51483776141/100000000000 : ℝ) (257418880709/500000000000 : ℝ) (517740315419/1000000000000 : ℝ) (517740315427/1000000000000 : ℝ) (51773217921/100000000000 : ℝ) (517732179219/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 3 (517740315419/1000000000000 : ℝ) (517740315427/1000000000000 : ℝ) (51773217921/100000000000 : ℝ) (517732179219/1000000000000 : ℝ) (258868123657/500000000000 : ℝ) (517736247323/1000000000000 : ℝ) (258868123649/500000000000 : ℝ) (129434061827/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 4 (258868123657/500000000000 : ℝ) (517736247323/1000000000000 : ℝ) (258868123649/500000000000 : ℝ) (129434061827/250000000000 : ℝ) (258868123653/500000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 5 (258868123653/500000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 6 (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4509/32768 : ℝ))) 7 (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4509/32768 : ℝ)) hmem 8 (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4509/32768 : ℝ))) hcmem 8 (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4509/32768 : ℝ)) (19804864411/20000000000 : ℝ) (990243220553/1000000000000 : ℝ) (103547249461/200000000000 : ℝ) (129434061829/250000000000 : ℝ) (41063557853/50000000000 : ℝ) (821271157081/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0407_exp_lower
  have heNumeric : (1009509454703/500000000000 : ℝ)/4 ≤ Real.exp (-10938922497671/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509454703/500000000000 : ℝ)/4 ≤ Real.exp ((9017/65536 : ℝ)-(821271157081/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9017/65536 : ℝ) (4509/32768 : ℝ) (821271157081/1000000000000 : ℝ) (1009509454703/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0408; no trusted numerical premise.
theorem cover7_leaf0408_exp_radius : (997545534663837293/1000000000000000000 : ℝ) ≤ Real.exp ((-9019/458752 : ℝ)/8) ∧ Real.exp ((-9019/458752 : ℝ)/8) ≤ (498772767331918647/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9019/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0408_exp_lower : (918089572950942773/1000000000000000000 : ℝ) ≤ Real.exp ((-5469460422467/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469460422467/8000000000000 : ℝ)/8) ≤ (459044786475471387/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469460422467/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0408_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509558981/500000000000 : ℝ) ≤ 4*Real.exp (4509/32768 : ℝ)*Real.exp (-mu (radius 7 (9019/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509558981/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9019/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0408_exp_radius
  have hrNumeric : (490266067497/500000000000 : ℝ) ≤ Real.exp (-9019/458752 : ℝ) ∧ Real.exp (-9019/458752 : ℝ) ≤ (196106426999/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490266067497/500000000000 : ℝ) ≤ (radius 7 (9019/65536 : ℝ)) ∧ (radius 7 (9019/65536 : ℝ)) ≤ (196106426999/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9019/65536 : ℝ)) (490266067497/500000000000 : ℝ) (196106426999/200000000000 : ℝ) (95878263/488281250 : ℝ) (19635868263/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9019/65536 : ℝ)) (490266067497/500000000000 : ℝ) (196106426999/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490266067497/500000000000 : ℝ) (196106426999/200000000000 : ℝ) (990266067497/1000000000000 : ℝ) (495133033749/500000000000 : ℝ) (198043645189/200000000000 : ℝ) (495109112973/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 1 (990266067497/1000000000000 : ℝ) (495133033749/500000000000 : ℝ) (198043645189/200000000000 : ℝ) (495109112973/500000000000 : ℝ) (990242146721/1000000000000 : ℝ) (495121073361/500000000000 : ℝ) (7736266769/7812500000 : ℝ) (495121073217/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 2 (990242146721/1000000000000 : ℝ) (495121073361/500000000000 : ℝ) (7736266769/7812500000 : ℝ) (495121073217/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 3 (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 4 (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 5 (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 6 (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9019/65536 : ℝ)) 7 (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9019/65536 : ℝ))) (95878263/488281250 : ℝ) (19635868263/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95878263/488281250 : ℝ) (19635868263/100000000000 : ℝ) (584159513/976562500 : ℝ) (119635868263/200000000000 : ℝ) (221561888997/500000000000 : ℝ) (221561889001/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 1 (584159513/976562500 : ℝ) (119635868263/200000000000 : ℝ) (221561888997/500000000000 : ℝ) (221561889001/500000000000 : ℝ) (520651559653/1000000000000 : ℝ) (520651559659/1000000000000 : ℝ) (514847054609/1000000000000 : ℝ) (64355881827/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 2 (520651559653/1000000000000 : ℝ) (520651559659/1000000000000 : ℝ) (514847054609/1000000000000 : ℝ) (64355881827/125000000000 : ℝ) (517749307131/1000000000000 : ℝ) (258874653569/500000000000 : ℝ) (258870586377/500000000000 : ℝ) (517741172761/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 3 (517749307131/1000000000000 : ℝ) (258874653569/500000000000 : ℝ) (258870586377/500000000000 : ℝ) (517741172761/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (10354904799/20000000000 : ℝ) (258872619963/500000000000 : ℝ) (258872619967/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 4 (258872619971/500000000000 : ℝ) (10354904799/20000000000 : ℝ) (258872619963/500000000000 : ℝ) (258872619967/500000000000 : ℝ) (258872619967/500000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 5 (258872619967/500000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 6 (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9019/65536 : ℝ))) 7 (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9019/65536 : ℝ)) hmem 8 (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9019/65536 : ℝ))) hcmem 8 (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9019/65536 : ℝ)) (61890134161/62500000000 : ℝ) (495121073289/500000000000 : ℝ) (517745239933/1000000000000 : ℝ) (258872619971/500000000000 : ℝ) (821286312557/1000000000000 : ℝ) (410643156287/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0408_exp_lower
  have heNumeric : (1009509558981/500000000000 : ℝ)/4 ≤ Real.exp (-5469460422467/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509558981/500000000000 : ℝ)/4 ≤ Real.exp ((4509/32768 : ℝ)-(410643156287/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4509/32768 : ℝ) (9019/65536 : ℝ) (410643156287/500000000000 : ℝ) (1009509558981/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0409; no trusted numerical premise.
theorem cover7_leaf0409_exp_radius : (997545262854286937/1000000000000000000 : ℝ) ≤ Real.exp ((-2255/114688 : ℝ)/8) ∧ Real.exp ((-2255/114688 : ℝ)/8) ≤ (498772631427143469/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2255/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0409_exp_lower : (918089584933740369/1000000000000000000 : ℝ) ≤ Real.exp ((-10938919174293/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938919174293/16000000000000 : ℝ)/8) ≤ (91808958493374037/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938919174293/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0409_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509664389/500000000000 : ℝ) ≤ 4*Real.exp (9019/65536 : ℝ)*Real.exp (-mu (radius 7 (2255/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509664389/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2255/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0409_exp_radius
  have hrNumeric : (490264998803/500000000000 : ℝ) ≤ Real.exp (-2255/114688 : ℝ) ∧ Real.exp (-2255/114688 : ℝ) ≤ (980529997607/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490264998803/500000000000 : ℝ) ≤ (radius 7 (2255/16384 : ℝ)) ∧ (radius 7 (2255/16384 : ℝ)) ≤ (980529997607/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2255/16384 : ℝ)) (490264998803/500000000000 : ℝ) (980529997607/1000000000000 : ℝ) (196369355533/1000000000000 : ℝ) (196369355539/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2255/16384 : ℝ)) (490264998803/500000000000 : ℝ) (980529997607/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490264998803/500000000000 : ℝ) (980529997607/1000000000000 : ℝ) (990264998803/1000000000000 : ℝ) (247566249701/250000000000 : ℝ) (990217146693/1000000000000 : ℝ) (198043429339/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 1 (990264998803/1000000000000 : ℝ) (247566249701/250000000000 : ℝ) (990217146693/1000000000000 : ℝ) (198043429339/200000000000 : ℝ) (247560268187/250000000000 : ℝ) (3960964291/4000000000 : ℝ) (495120536229/500000000000 : ℝ) (990241072461/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 2 (247560268187/250000000000 : ℝ) (3960964291/4000000000 : ℝ) (495120536229/500000000000 : ℝ) (990241072461/1000000000000 : ℝ) (990241072603/1000000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 3 (990241072603/1000000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 4 (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 5 (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 6 (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2255/16384 : ℝ)) 7 (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2255/16384 : ℝ))) (196369355533/1000000000000 : ℝ) (196369355539/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196369355533/1000000000000 : ℝ) (196369355539/1000000000000 : ℝ) (299092338883/500000000000 : ℝ) (59818467777/100000000000 : ℝ) (221567910319/500000000000 : ℝ) (221567910323/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 1 (299092338883/500000000000 : ℝ) (59818467777/100000000000 : ℝ) (221567910319/500000000000 : ℝ) (221567910323/500000000000 : ℝ) (260330124601/500000000000 : ℝ) (65082531151/125000000000 : ℝ) (514856347027/1000000000000 : ℝ) (102971269407/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 2 (260330124601/500000000000 : ℝ) (65082531151/125000000000 : ℝ) (514856347027/1000000000000 : ℝ) (102971269407/200000000000 : ℝ) (258879149057/500000000000 : ℝ) (258879149061/500000000000 : ℝ) (8089846337/15625000000 : ℝ) (64718770697/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 3 (258879149057/500000000000 : ℝ) (258879149061/500000000000 : ℝ) (8089846337/15625000000 : ℝ) (64718770697/125000000000 : ℝ) (517754231841/1000000000000 : ℝ) (517754231849/1000000000000 : ℝ) (20710169273/40000000000 : ℝ) (258877115917/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 4 (517754231841/1000000000000 : ℝ) (517754231849/1000000000000 : ℝ) (20710169273/40000000000 : ℝ) (258877115917/500000000000 : ℝ) (517754231833/1000000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 5 (517754231833/1000000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 6 (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2255/16384 : ℝ))) 7 (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2255/16384 : ℝ)) hmem 8 (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2255/16384 : ℝ))) hcmem 8 (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2255/16384 : ℝ)) (495120536301/500000000000 : ℝ) (495120536303/500000000000 : ℝ) (64719278979/125000000000 : ℝ) (258877115921/500000000000 : ℝ) (51331341683/62500000000 : ℝ) (205325366737/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0409_exp_lower
  have heNumeric : (1009509664389/500000000000 : ℝ)/4 ≤ Real.exp (-10938919174293/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509664389/500000000000 : ℝ)/4 ≤ Real.exp ((9019/65536 : ℝ)-(205325366737/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9019/65536 : ℝ) (2255/16384 : ℝ) (205325366737/250000000000 : ℝ) (1009509664389/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0410; no trusted numerical premise.
theorem cover7_leaf0410_exp_radius : (997544991044810643/1000000000000000000 : ℝ) ≤ Real.exp ((-9021/458752 : ℝ)/8) ∧ Real.exp ((-9021/458752 : ℝ)/8) ≤ (249386247761202661/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9021/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0410_exp_lower : (459044798522420571/500000000000000000 : ℝ) ≤ Real.exp ((-2734729371441/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734729371441/4000000000000 : ℝ)/8) ≤ (918089597044841143/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734729371441/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0410_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504754885463/250000000000 : ℝ) ≤ 4*Real.exp (2255/16384 : ℝ)*Real.exp (-mu (radius 7 (9021/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504754885463/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9021/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0410_exp_radius
  have hrNumeric : (490263930111/500000000000 : ℝ) ≤ Real.exp (-9021/458752 : ℝ) ∧ Real.exp (-9021/458752 : ℝ) ≤ (980527860223/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490263930111/500000000000 : ℝ) ≤ (radius 7 (9021/65536 : ℝ)) ∧ (radius 7 (9021/65536 : ℝ)) ≤ (980527860223/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9021/65536 : ℝ)) (490263930111/500000000000 : ℝ) (980527860223/1000000000000 : ℝ) (196380027819/1000000000000 : ℝ) (7855201113/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9021/65536 : ℝ)) (490263930111/500000000000 : ℝ) (980527860223/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490263930111/500000000000 : ℝ) (980527860223/1000000000000 : ℝ) (990263930111/1000000000000 : ℝ) (3868218477/3906250000 : ℝ) (495108033721/500000000000 : ℝ) (247554016861/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 1 (990263930111/1000000000000 : ℝ) (3868218477/3906250000 : ℝ) (495108033721/500000000000 : ℝ) (247554016861/250000000000 : ℝ) (123779999847/125000000000 : ℝ) (495119999389/500000000000 : ℝ) (990239998487/1000000000000 : ℝ) (990239998489/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 2 (123779999847/125000000000 : ℝ) (495119999389/500000000000 : ℝ) (990239998487/1000000000000 : ℝ) (990239998489/1000000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 3 (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 4 (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 5 (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 6 (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9021/65536 : ℝ)) 7 (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9021/65536 : ℝ))) (196380027819/1000000000000 : ℝ) (7855201113/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196380027819/1000000000000 : ℝ) (7855201113/40000000000 : ℝ) (598190013909/1000000000000 : ℝ) (598190013913/1000000000000 : ℝ) (110786965563/250000000000 : ℝ) (22157393113/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 1 (598190013909/1000000000000 : ℝ) (598190013913/1000000000000 : ℝ) (110786965563/250000000000 : ℝ) (22157393113/50000000000 : ℝ) (3254180863/6250000000 : ℝ) (520668938087/1000000000000 : ℝ) (514865638671/1000000000000 : ℝ) (257432819339/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 2 (3254180863/6250000000 : ℝ) (520668938087/1000000000000 : ℝ) (514865638671/1000000000000 : ℝ) (257432819339/500000000000 : ℝ) (4142138307/8000000000 : ℝ) (517767288383/1000000000000 : ℝ) (517759157659/1000000000000 : ℝ) (517759157667/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 3 (4142138307/8000000000 : ℝ) (517767288383/1000000000000 : ℝ) (517759157659/1000000000000 : ℝ) (517759157667/1000000000000 : ℝ) (517763223017/1000000000000 : ℝ) (20710528921/40000000000 : ℝ) (517763223001/1000000000000 : ℝ) (51776322301/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 4 (517763223017/1000000000000 : ℝ) (20710528921/40000000000 : ℝ) (517763223001/1000000000000 : ℝ) (51776322301/100000000000 : ℝ) (517763223009/1000000000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 5 (517763223009/1000000000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 6 (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9021/65536 : ℝ))) 7 (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9021/65536 : ℝ)) hmem 8 (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9021/65536 : ℝ))) hcmem 8 (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9021/65536 : ℝ)) (990239998631/1000000000000 : ℝ) (495119999317/500000000000 : ℝ) (16180100719/31250000000 : ℝ) (258881611509/500000000000 : ℝ) (164263324037/200000000000 : ℝ) (205329155051/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0410_exp_lower
  have heNumeric : (504754885463/250000000000 : ℝ)/4 ≤ Real.exp (-2734729371441/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504754885463/250000000000 : ℝ)/4 ≤ Real.exp ((2255/16384 : ℝ)-(205329155051/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2255/16384 : ℝ) (9021/65536 : ℝ) (205329155051/250000000000 : ℝ) (504754885463/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0411; no trusted numerical premise.
theorem cover7_leaf0411_exp_radius : (249386179808852103/250000000000000000 : ℝ) ≤ Real.exp ((-4511/229376 : ℝ)/8) ∧ Real.exp ((-4511/229376 : ℝ)/8) ≤ (997544719235408413/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4511/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0411_exp_lower : (918089609285622233/1000000000000000000 : ℝ) ≤ Real.exp ((-2187783155831/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187783155831/3200000000000 : ℝ)/8) ≤ (459044804642811117/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187783155831/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0411_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509878603/500000000000 : ℝ) ≤ 4*Real.exp (9021/65536 : ℝ)*Real.exp (-mu (radius 7 (4511/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509878603/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4511/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0411_exp_radius
  have hrNumeric : (245131430711/250000000000 : ℝ) ≤ Real.exp (-4511/229376 : ℝ) ∧ Real.exp (-4511/229376 : ℝ) ≤ (196105144569/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245131430711/250000000000 : ℝ) ≤ (radius 7 (4511/32768 : ℝ)) ∧ (radius 7 (4511/32768 : ℝ)) ≤ (196105144569/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4511/32768 : ℝ)) (245131430711/250000000000 : ℝ) (196105144569/200000000000 : ℝ) (12274418717/62500000000 : ℝ) (98195349739/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4511/32768 : ℝ)) (245131430711/250000000000 : ℝ) (196105144569/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245131430711/250000000000 : ℝ) (196105144569/200000000000 : ℝ) (495131430711/500000000000 : ℝ) (990262861423/1000000000000 : ℝ) (990214988193/1000000000000 : ℝ) (198042997639/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 1 (495131430711/500000000000 : ℝ) (990262861423/1000000000000 : ℝ) (990214988193/1000000000000 : ℝ) (198042997639/200000000000 : ℝ) (990238924807/1000000000000 : ℝ) (990238924809/1000000000000 : ℝ) (495119462259/500000000000 : ℝ) (24755973113/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 2 (990238924807/1000000000000 : ℝ) (990238924809/1000000000000 : ℝ) (495119462259/500000000000 : ℝ) (24755973113/25000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 3 (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 4 (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 5 (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 6 (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4511/32768 : ℝ)) 7 (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4511/32768 : ℝ))) (12274418717/62500000000 : ℝ) (98195349739/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (12274418717/62500000000 : ℝ) (98195349739/500000000000 : ℝ) (74774418717/125000000000 : ℝ) (598195349739/1000000000000 : ℝ) (17726396113/40000000000 : ℝ) (27697493927/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 1 (74774418717/125000000000 : ℝ) (598195349739/1000000000000 : ℝ) (17726396113/40000000000 : ℝ) (27697493927/62500000000 : ℝ) (13016940657/25000000000 : ℝ) (260338813143/500000000000 : ℝ) (51487492953/100000000000 : ℝ) (514874929537/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 2 (13016940657/25000000000 : ℝ) (260338813143/500000000000 : ℝ) (51487492953/100000000000 : ℝ) (514874929537/1000000000000 : ℝ) (103555255581/200000000000 : ℝ) (64722034739/125000000000 : ℝ) (517768149019/1000000000000 : ℝ) (258884074513/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 3 (103555255581/200000000000 : ℝ) (64722034739/125000000000 : ℝ) (517768149019/1000000000000 : ℝ) (258884074513/500000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213469/1000000000000 : ℝ) (258886106723/500000000000 : ℝ) (258886106727/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 4 (258886106731/500000000000 : ℝ) (517772213469/1000000000000 : ℝ) (258886106723/500000000000 : ℝ) (258886106727/500000000000 : ℝ) (258886106727/500000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 5 (258886106727/500000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 6 (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4511/32768 : ℝ))) 7 (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4511/32768 : ℝ)) hmem 8 (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4511/32768 : ℝ))) hcmem 8 (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4511/32768 : ℝ)) (495119462331/500000000000 : ℝ) (198047784933/200000000000 : ℝ) (517772213453/1000000000000 : ℝ) (258886106731/500000000000 : ℝ) (821331772313/1000000000000 : ℝ) (82133177233/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0411_exp_lower
  have heNumeric : (1009509878603/500000000000 : ℝ)/4 ≤ Real.exp (-2187783155831/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509878603/500000000000 : ℝ)/4 ≤ Real.exp ((9021/65536 : ℝ)-(82133177233/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9021/65536 : ℝ) (4511/32768 : ℝ) (82133177233/100000000000 : ℝ) (1009509878603/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0412; no trusted numerical premise.
theorem cover7_leaf0412_exp_radius : (997544447426080243/1000000000000000000 : ℝ) ≤ Real.exp ((-1289/65536 : ℝ)/8) ∧ Real.exp ((-1289/65536 : ℝ)/8) ≤ (249386111856520061/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1289/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0412_exp_lower : (918089621654362227/1000000000000000000 : ℝ) ≤ Real.exp ((-5469457027353/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469457027353/8000000000000 : ℝ)/8) ≤ (229522405413590557/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469457027353/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0412_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504754993703/250000000000 : ℝ) ≤ 4*Real.exp (4511/32768 : ℝ)*Real.exp (-mu (radius 7 (9023/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504754993703/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9023/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0412_exp_radius
  have hrNumeric : (98052358547/100000000000 : ℝ) ≤ Real.exp (-1289/65536 : ℝ) ∧ Real.exp (-1289/65536 : ℝ) ≤ (980523585471/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98052358547/100000000000 : ℝ) ≤ (radius 7 (9023/65536 : ℝ)) ∧ (radius 7 (9023/65536 : ℝ)) ≤ (980523585471/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9023/65536 : ℝ)) (98052358547/100000000000 : ℝ) (980523585471/1000000000000 : ℝ) (98200685251/500000000000 : ℝ) (49100342627/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9023/65536 : ℝ)) (98052358547/100000000000 : ℝ) (980523585471/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98052358547/100000000000 : ℝ) (980523585471/1000000000000 : ℝ) (198052358547/200000000000 : ℝ) (30945681023/31250000000 : ℝ) (198042781789/200000000000 : ℝ) (990213908947/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 1 (198052358547/200000000000 : ℝ) (30945681023/31250000000 : ℝ) (198042781789/200000000000 : ℝ) (990213908947/1000000000000 : ℝ) (24755946271/25000000000 : ℝ) (495118925421/500000000000 : ℝ) (19804757011/20000000000 : ℝ) (990237850553/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 2 (24755946271/25000000000 : ℝ) (495118925421/500000000000 : ℝ) (19804757011/20000000000 : ℝ) (990237850553/1000000000000 : ℝ) (198047570139/200000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 3 (198047570139/200000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 4 (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 5 (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 6 (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9023/65536 : ℝ)) 7 (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9023/65536 : ℝ))) (98200685251/500000000000 : ℝ) (49100342627/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98200685251/500000000000 : ℝ) (49100342627/250000000000 : ℝ) (598200685251/1000000000000 : ℝ) (299100342627/500000000000 : ℝ) (443171942367/1000000000000 : ℝ) (3545375539/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 1 (598200685251/1000000000000 : ℝ) (299100342627/500000000000 : ℝ) (443171942367/1000000000000 : ℝ) (3545375539/8000000000 : ℝ) (520686313809/1000000000000 : ℝ) (104137262763/200000000000 : ℝ) (257442109807/500000000000 : ℝ) (514884219621/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 2 (520686313809/1000000000000 : ℝ) (104137262763/200000000000 : ℝ) (257442109807/500000000000 : ℝ) (514884219621/1000000000000 : ℝ) (517785266711/1000000000000 : ℝ) (258892633359/500000000000 : ℝ) (258888569827/500000000000 : ℝ) (258888569831/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 3 (517785266711/1000000000000 : ℝ) (258892633359/500000000000 : ℝ) (258888569827/500000000000 : ℝ) (258888569831/500000000000 : ℝ) (258890601591/500000000000 : ℝ) (51778120319/100000000000 : ℝ) (258890601583/500000000000 : ℝ) (20711248127/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 4 (258890601591/500000000000 : ℝ) (51778120319/100000000000 : ℝ) (258890601583/500000000000 : ℝ) (20711248127/40000000000 : ℝ) (258890601587/500000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 5 (258890601587/500000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 6 (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9023/65536 : ℝ))) 7 (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9023/65536 : ℝ)) hmem 8 (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9023/65536 : ℝ))) hcmem 8 (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9023/65536 : ℝ)) (495118925347/500000000000 : ℝ) (495118925349/500000000000 : ℝ) (517781203173/1000000000000 : ℝ) (517781203183/1000000000000 : ℝ) (821346923321/1000000000000 : ℝ) (821346923341/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0412_exp_lower
  have heNumeric : (504754993703/250000000000 : ℝ)/4 ≤ Real.exp (-5469457027353/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504754993703/250000000000 : ℝ)/4 ≤ Real.exp ((4511/32768 : ℝ)-(821346923341/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4511/32768 : ℝ) (9023/65536 : ℝ) (821346923341/1000000000000 : ℝ) (504754993703/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0413; no trusted numerical premise.
theorem cover7_leaf0413_exp_radius : (199508835123365227/200000000000000000 : ℝ) ≤ Real.exp ((-141/7168 : ℝ)/8) ∧ Real.exp ((-141/7168 : ℝ)/8) ≤ (124693021952103267/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-141/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0413_exp_lower : (459044817075645327/500000000000000000 : ℝ) ≤ Real.exp ((-2187782462477/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187782462477/3200000000000 : ℝ)/8) ≤ (183617926830258131/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187782462477/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0413_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009510097337/500000000000 : ℝ) ≤ 4*Real.exp (9023/65536 : ℝ)*Real.exp (-mu (radius 7 (141/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009510097337/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (141/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0413_exp_radius
  have hrNumeric : (9805214481/10000000000 : ℝ) ≤ Real.exp (-141/7168 : ℝ) ∧ Real.exp (-141/7168 : ℝ) ≤ (980521448101/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9805214481/10000000000 : ℝ) ≤ (radius 7 (141/1024 : ℝ)) ∧ (radius 7 (141/1024 : ℝ)) ≤ (980521448101/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (141/1024 : ℝ)) (9805214481/10000000000 : ℝ) (980521448101/1000000000000 : ℝ) (49103010227/250000000000 : ℝ) (98206020457/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (141/1024 : ℝ)) (9805214481/10000000000 : ℝ) (980521448101/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (141/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9805214481/10000000000 : ℝ) (980521448101/1000000000000 : ℝ) (19805214481/20000000000 : ℝ) (990260724051/1000000000000 : ℝ) (495106414849/500000000000 : ℝ) (9902128297/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (141/1024 : ℝ)) 1 (19805214481/20000000000 : ℝ) (990260724051/1000000000000 : ℝ) (495106414849/500000000000 : ℝ) (9902128297/10000000000 : ℝ) (495118388437/500000000000 : ℝ) (247559194219/250000000000 : ℝ) (123779597073/125000000000 : ℝ) (495118388293/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (141/1024 : ℝ)) 2 (495118388437/500000000000 : ℝ) (247559194219/250000000000 : ℝ) (123779597073/125000000000 : ℝ) (495118388293/500000000000 : ℝ) (990236776729/1000000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (141/1024 : ℝ)) 3 (990236776729/1000000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (141/1024 : ℝ)) 4 (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (141/1024 : ℝ)) 5 (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (141/1024 : ℝ)) 6 (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (141/1024 : ℝ)) 7 (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (141/1024 : ℝ))) (49103010227/250000000000 : ℝ) (98206020457/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49103010227/250000000000 : ℝ) (98206020457/500000000000 : ℝ) (299103010227/500000000000 : ℝ) (598206020457/1000000000000 : ℝ) (443183980879/1000000000000 : ℝ) (443183980887/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 1 (299103010227/500000000000 : ℝ) (598206020457/1000000000000 : ℝ) (443183980879/1000000000000 : ℝ) (443183980887/1000000000000 : ℝ) (260347500333/500000000000 : ℝ) (16271718771/31250000000 : ℝ) (257446754461/500000000000 : ℝ) (514893508929/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 2 (260347500333/500000000000 : ℝ) (16271718771/31250000000 : ℝ) (257446754461/500000000000 : ℝ) (514893508929/1000000000000 : ℝ) (258897127397/500000000000 : ℝ) (517794254801/1000000000000 : ℝ) (258893064783/500000000000 : ℝ) (517786129573/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 3 (258897127397/500000000000 : ℝ) (517794254801/1000000000000 : ℝ) (258893064783/500000000000 : ℝ) (517786129573/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192187/1000000000000 : ℝ) (129447548041/250000000000 : ℝ) (129447548043/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 4 (25889509609/50000000000 : ℝ) (517790192187/1000000000000 : ℝ) (129447548041/250000000000 : ℝ) (129447548043/250000000000 : ℝ) (129447548043/250000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 5 (129447548043/250000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 6 (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (141/1024 : ℝ))) 7 (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (141/1024 : ℝ)) hmem 8 (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (141/1024 : ℝ))) hcmem 8 (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (141/1024 : ℝ)) (123779597091/125000000000 : ℝ) (990236776731/1000000000000 : ℝ) (517790192171/1000000000000 : ℝ) (25889509609/50000000000 : ℝ) (410681036609/500000000000 : ℝ) (164272414647/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0413_exp_lower
  have heNumeric : (1009510097337/500000000000 : ℝ)/4 ≤ Real.exp (-2187782462477/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009510097337/500000000000 : ℝ)/4 ≤ Real.exp ((9023/65536 : ℝ)-(164272414647/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9023/65536 : ℝ) (141/1024 : ℝ) (164272414647/200000000000 : ℝ) (1009510097337/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0414; no trusted numerical premise.
theorem cover7_leaf0414_exp_radius : (99754390380764609/100000000000000000 : ℝ) ≤ Real.exp ((-9025/458752 : ℝ)/8) ∧ Real.exp ((-9025/458752 : ℝ)/8) ≤ (997543903807646091/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9025/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0414_exp_lower : (459044823388433281/500000000000000000 : ℝ) ≤ Real.exp ((-170920477377/250000000000 : ℝ)/8) ∧ Real.exp ((-170920477377/250000000000 : ℝ)/8) ≤ (918089646776866563/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170920477377/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0414_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009510208399/500000000000 : ℝ) ≤ 4*Real.exp (141/1024 : ℝ)*Real.exp (-mu (radius 7 (9025/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009510208399/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9025/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0414_exp_radius
  have hrNumeric : (196103862147/200000000000 : ℝ) ≤ Real.exp (-9025/458752 : ℝ) ∧ Real.exp (-9025/458752 : ℝ) ≤ (61282456921/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196103862147/200000000000 : ℝ) ≤ (radius 7 (9025/65536 : ℝ)) ∧ (radius 7 (9025/65536 : ℝ)) ≤ (61282456921/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9025/65536 : ℝ)) (196103862147/200000000000 : ℝ) (61282456921/62500000000 : ℝ) (196422710687/1000000000000 : ℝ) (196422710693/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9025/65536 : ℝ)) (196103862147/200000000000 : ℝ) (61282456921/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196103862147/200000000000 : ℝ) (61282456921/62500000000 : ℝ) (990259655367/1000000000000 : ℝ) (123782456921/125000000000 : ℝ) (247552937613/250000000000 : ℝ) (495105875227/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 1 (990259655367/1000000000000 : ℝ) (123782456921/125000000000 : ℝ) (247552937613/250000000000 : ℝ) (495105875227/500000000000 : ℝ) (990235702909/1000000000000 : ℝ) (990235702911/1000000000000 : ℝ) (990235702619/1000000000000 : ℝ) (495117851311/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 2 (990235702909/1000000000000 : ℝ) (990235702911/1000000000000 : ℝ) (990235702619/1000000000000 : ℝ) (495117851311/500000000000 : ℝ) (247558925691/250000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 3 (247558925691/250000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 4 (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 5 (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 6 (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9025/65536 : ℝ)) 7 (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9025/65536 : ℝ))) (196422710687/1000000000000 : ℝ) (196422710693/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196422710687/1000000000000 : ℝ) (196422710693/1000000000000 : ℝ) (598211355343/1000000000000 : ℝ) (598211355347/1000000000000 : ℝ) (110799004589/250000000000 : ℝ) (110799004591/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 1 (598211355343/1000000000000 : ℝ) (598211355347/1000000000000 : ℝ) (110799004589/250000000000 : ℝ) (110799004591/250000000000 : ℝ) (520703686849/1000000000000 : ℝ) (65087960857/125000000000 : ℝ) (514902797451/1000000000000 : ℝ) (257451398729/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 2 (520703686849/1000000000000 : ℝ) (65087960857/125000000000 : ℝ) (514902797451/1000000000000 : ℝ) (257451398729/500000000000 : ℝ) (10356064843/20000000000 : ℝ) (517803242157/1000000000000 : ℝ) (82847219/160000000 : ℝ) (258897559379/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 3 (10356064843/20000000000 : ℝ) (517803242157/1000000000000 : ℝ) (82847219/160000000 : ℝ) (258897559379/500000000000 : ℝ) (10355983609/20000000000 : ℝ) (258899590229/500000000000 : ℝ) (258899590217/500000000000 : ℝ) (258899590221/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 4 (10355983609/20000000000 : ℝ) (258899590229/500000000000 : ℝ) (258899590217/500000000000 : ℝ) (258899590221/500000000000 : ℝ) (258899590221/500000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 5 (258899590221/500000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 6 (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9025/65536 : ℝ))) 7 (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9025/65536 : ℝ)) hmem 8 (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9025/65536 : ℝ))) hcmem 8 (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9025/65536 : ℝ)) (990235702763/1000000000000 : ℝ) (990235702767/1000000000000 : ℝ) (517799180441/1000000000000 : ℝ) (10355983609/20000000000 : ℝ) (82137722199/100000000000 : ℝ) (102672152751/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0414_exp_lower
  have heNumeric : (1009510208399/500000000000 : ℝ)/4 ≤ Real.exp (-170920477377/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009510208399/500000000000 : ℝ)/4 ≤ Real.exp ((141/1024 : ℝ)-(102672152751/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (141/1024 : ℝ) (9025/65536 : ℝ) (102672152751/125000000000 : ℝ) (1009510208399/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0415; no trusted numerical premise.
theorem cover7_leaf0415_exp_radius : (997543631998540107/1000000000000000000 : ℝ) ≤ Real.exp ((-4513/229376 : ℝ)/8) ∧ Real.exp ((-4513/229376 : ℝ)/8) ≤ (249385907999635027/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4513/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0415_exp_lower : (22952241488282987/25000000000000000 : ℝ) ≤ Real.exp ((-10938908773903/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938908773903/16000000000000 : ℝ)/8) ≤ (918089659531319481/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938908773903/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0415_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019020641191/1000000000000 : ℝ) ≤ 4*Real.exp (9025/65536 : ℝ)*Real.exp (-mu (radius 7 (4513/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019020641191/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4513/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0415_exp_radius
  have hrNumeric : (7844137387/8000000000 : ℝ) ≤ Real.exp (-4513/229376 : ℝ) ∧ Real.exp (-4513/229376 : ℝ) ≤ (7660290417/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7844137387/8000000000 : ℝ) ≤ (radius 7 (4513/32768 : ℝ)) ∧ (radius 7 (4513/32768 : ℝ)) ≤ (7660290417/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4513/32768 : ℝ)) (7844137387/8000000000 : ℝ) (7660290417/7812500000 : ℝ) (98216689919/500000000000 : ℝ) (49108344961/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4513/32768 : ℝ)) (7844137387/8000000000 : ℝ) (7660290417/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7844137387/8000000000 : ℝ) (7660290417/7812500000 : ℝ) (990258586687/1000000000000 : ℝ) (15472790417/15625000000 : ℝ) (123776333901/125000000000 : ℝ) (990210671209/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 1 (990258586687/1000000000000 : ℝ) (15472790417/15625000000 : ℝ) (123776333901/125000000000 : ℝ) (990210671209/1000000000000 : ℝ) (990234628947/1000000000000 : ℝ) (990234628949/1000000000000 : ℝ) (990234628657/1000000000000 : ℝ) (990234628659/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 2 (990234628947/1000000000000 : ℝ) (990234628949/1000000000000 : ℝ) (990234628657/1000000000000 : ℝ) (990234628659/1000000000000 : ℝ) (495117314401/500000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 3 (495117314401/500000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 4 (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 5 (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 6 (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4513/32768 : ℝ)) 7 (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4513/32768 : ℝ))) (98216689919/500000000000 : ℝ) (49108344961/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98216689919/500000000000 : ℝ) (49108344961/250000000000 : ℝ) (598216689919/1000000000000 : ℝ) (299108344961/500000000000 : ℝ) (221604027399/500000000000 : ℝ) (88641610961/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 1 (598216689919/1000000000000 : ℝ) (299108344961/500000000000 : ℝ) (221604027399/500000000000 : ℝ) (88641610961/200000000000 : ℝ) (260356186179/500000000000 : ℝ) (130178093091/250000000000 : ℝ) (514912085201/1000000000000 : ℝ) (514912085207/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 2 (260356186179/500000000000 : ℝ) (130178093091/250000000000 : ℝ) (514912085201/1000000000000 : ℝ) (514912085207/1000000000000 : ℝ) (517812228779/1000000000000 : ℝ) (258906114393/500000000000 : ℝ) (517804107207/1000000000000 : ℝ) (258902053607/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 3 (517812228779/1000000000000 : ℝ) (258906114393/500000000000 : ℝ) (517804107207/1000000000000 : ℝ) (258902053607/500000000000 : ℝ) (517808167993/1000000000000 : ℝ) (64726021/125000000 : ℝ) (517808167977/1000000000000 : ℝ) (103561633597/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 4 (517808167993/1000000000000 : ℝ) (64726021/125000000 : ℝ) (517808167977/1000000000000 : ℝ) (103561633597/200000000000 : ℝ) (103561633597/200000000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 5 (103561633597/200000000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 6 (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4513/32768 : ℝ))) 7 (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4513/32768 : ℝ)) hmem 8 (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4513/32768 : ℝ))) hcmem 8 (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4513/32768 : ℝ)) (990234628801/1000000000000 : ℝ) (247558657201/250000000000 : ℝ) (32363010499/62500000000 : ℝ) (517808167993/1000000000000 : ℝ) (20534809241/25000000000 : ℝ) (410696184829/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0415_exp_lower
  have heNumeric : (2019020641191/1000000000000 : ℝ)/4 ≤ Real.exp (-10938908773903/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019020641191/1000000000000 : ℝ)/4 ≤ Real.exp ((9025/65536 : ℝ)-(410696184829/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9025/65536 : ℝ) (4513/32768 : ℝ) (410696184829/500000000000 : ℝ) (2019020641191/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0416; no trusted numerical premise.
theorem cover7_leaf0416_exp_radius : (498771680094754093/500000000000000000 : ℝ) ≤ Real.exp ((-9027/458752 : ℝ)/8) ∧ Real.exp ((-9027/458752 : ℝ)/8) ≤ (997543360189508187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9027/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0416_exp_lower : (459044836207382087/500000000000000000 : ℝ) ≤ Real.exp ((-5469453488847/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469453488847/8000000000000 : ℝ)/8) ≤ (36723586896590567/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469453488847/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0416_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504755216963/250000000000 : ℝ) ≤ 4*Real.exp (4513/32768 : ℝ)*Real.exp (-mu (radius 7 (9027/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504755216963/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9027/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0416_exp_radius
  have hrNumeric : (49025751801/50000000000 : ℝ) ≤ Real.exp (-9027/458752 : ℝ) ∧ Real.exp (-9027/458752 : ℝ) ≤ (980515036021/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49025751801/50000000000 : ℝ) ≤ (radius 7 (9027/65536 : ℝ)) ∧ (radius 7 (9027/65536 : ℝ)) ≤ (980515036021/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9027/65536 : ℝ)) (49025751801/50000000000 : ℝ) (980515036021/1000000000000 : ℝ) (196444048361/1000000000000 : ℝ) (196444048367/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9027/65536 : ℝ)) (49025751801/50000000000 : ℝ) (980515036021/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49025751801/50000000000 : ℝ) (980515036021/1000000000000 : ℝ) (99025751801/100000000000 : ℝ) (990257518011/1000000000000 : ℝ) (198041918393/200000000000 : ℝ) (495104795983/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 1 (99025751801/100000000000 : ℝ) (990257518011/1000000000000 : ℝ) (198041918393/200000000000 : ℝ) (495104795983/500000000000 : ℝ) (990233554987/1000000000000 : ℝ) (990233554989/1000000000000 : ℝ) (990233554697/1000000000000 : ℝ) (990233554699/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 2 (990233554987/1000000000000 : ℝ) (990233554989/1000000000000 : ℝ) (990233554697/1000000000000 : ℝ) (990233554699/1000000000000 : ℝ) (495116777421/500000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 3 (495116777421/500000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 4 (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 5 (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 6 (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9027/65536 : ℝ)) 7 (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9027/65536 : ℝ))) (196444048361/1000000000000 : ℝ) (196444048367/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196444048361/1000000000000 : ℝ) (196444048367/1000000000000 : ℝ) (29911101209/50000000000 : ℝ) (74777753023/125000000000 : ℝ) (110805022551/250000000000 : ℝ) (110805022553/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 1 (29911101209/50000000000 : ℝ) (74777753023/125000000000 : ℝ) (110805022551/250000000000 : ℝ) (110805022553/250000000000 : ℝ) (65090132149/125000000000 : ℝ) (260360528599/500000000000 : ℝ) (514921372171/1000000000000 : ℝ) (257460686089/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 2 (65090132149/125000000000 : ℝ) (260360528599/500000000000 : ℝ) (514921372171/1000000000000 : ℝ) (257460686089/500000000000 : ℝ) (517821214681/1000000000000 : ℝ) (16181912959/31250000000 : ℝ) (64726636867/125000000000 : ℝ) (517813094943/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 3 (517821214681/1000000000000 : ℝ) (16181912959/31250000000 : ℝ) (64726636867/125000000000 : ℝ) (517813094943/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (2022723261/3906250000 : ℝ) (64727144349/125000000000 : ℝ) (1294542887/2500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 4 (64727144351/125000000000 : ℝ) (2022723261/3906250000 : ℝ) (64727144349/125000000000 : ℝ) (1294542887/2500000000 : ℝ) (1294542887/2500000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 5 (1294542887/2500000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 6 (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9027/65536 : ℝ))) 7 (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9027/65536 : ℝ)) hmem 8 (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9027/65536 : ℝ))) hcmem 8 (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9027/65536 : ℝ)) (990233554841/1000000000000 : ℝ) (247558388711/250000000000 : ℝ) (517817154799/1000000000000 : ℝ) (64727144351/125000000000 : ℝ) (821407516167/1000000000000 : ℝ) (102675939523/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0416_exp_lower
  have heNumeric : (504755216963/250000000000 : ℝ)/4 ≤ Real.exp (-5469453488847/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504755216963/250000000000 : ℝ)/4 ≤ Real.exp ((4513/32768 : ℝ)-(102675939523/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4513/32768 : ℝ) (9027/65536 : ℝ) (102675939523/125000000000 : ℝ) (504755216963/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0417; no trusted numerical premise.
theorem cover7_leaf0417_exp_radius : (124692886047568791/125000000000000000 : ℝ) ≤ Real.exp ((-2257/114688 : ℝ)/8) ∧ Real.exp ((-2257/114688 : ℝ)/8) ≤ (997543088380550329/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2257/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0417_exp_lower : (459044842712854377/500000000000000000 : ℝ) ≤ Real.exp ((-10938905163709/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938905163709/16000000000000 : ℝ)/8) ≤ (183617937085141751/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938905163709/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0417_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019021096757/1000000000000 : ℝ) ≤ 4*Real.exp (9027/65536 : ℝ)*Real.exp (-mu (radius 7 (2257/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019021096757/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2257/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0417_exp_radius
  have hrNumeric : (980512898669/1000000000000 : ℝ) ≤ Real.exp (-2257/114688 : ℝ) ∧ Real.exp (-2257/114688 : ℝ) ≤ (98051289867/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980512898669/1000000000000 : ℝ) ≤ (radius 7 (2257/16384 : ℝ)) ∧ (radius 7 (2257/16384 : ℝ)) ≤ (98051289867/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2257/16384 : ℝ)) (980512898669/1000000000000 : ℝ) (98051289867/100000000000 : ℝ) (98227358131/500000000000 : ℝ) (49113679067/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2257/16384 : ℝ)) (980512898669/1000000000000 : ℝ) (98051289867/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980512898669/1000000000000 : ℝ) (98051289867/100000000000 : ℝ) (495128224667/500000000000 : ℝ) (198051289867/200000000000 : ℝ) (495104256361/500000000000 : ℝ) (247552128181/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 1 (495128224667/500000000000 : ℝ) (198051289867/200000000000 : ℝ) (495104256361/500000000000 : ℝ) (247552128181/250000000000 : ℝ) (247558120257/250000000000 : ℝ) (99023248103/100000000000 : ℝ) (990232480737/1000000000000 : ℝ) (49511624037/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 2 (247558120257/250000000000 : ℝ) (99023248103/100000000000 : ℝ) (990232480737/1000000000000 : ℝ) (49511624037/50000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 3 (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 4 (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 5 (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 6 (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2257/16384 : ℝ)) 7 (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2257/16384 : ℝ))) (98227358131/500000000000 : ℝ) (49113679067/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98227358131/500000000000 : ℝ) (49113679067/250000000000 : ℝ) (598227358131/1000000000000 : ℝ) (299113679067/500000000000 : ℝ) (221616062291/500000000000 : ℝ) (44323212459/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 1 (598227358131/1000000000000 : ℝ) (299113679067/500000000000 : ℝ) (221616062291/500000000000 : ℝ) (44323212459/100000000000 : ℝ) (130182435339/250000000000 : ℝ) (260364870681/500000000000 : ℝ) (8045791537/15625000000 : ℝ) (4119445267/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 2 (130182435339/250000000000 : ℝ) (260364870681/500000000000 : ℝ) (8045791537/15625000000 : ℝ) (4119445267/8000000000 : ℝ) (258915099931/500000000000 : ℝ) (517830199869/1000000000000 : ℝ) (517822081943/1000000000000 : ℝ) (10356441639/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 3 (258915099931/500000000000 : ℝ) (517830199869/1000000000000 : ℝ) (517822081943/1000000000000 : ℝ) (10356441639/20000000000 : ℝ) (258913070451/500000000000 : ℝ) (51782614091/100000000000 : ℝ) (258913070443/500000000000 : ℝ) (258913070447/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 4 (258913070451/500000000000 : ℝ) (51782614091/100000000000 : ℝ) (258913070443/500000000000 : ℝ) (258913070447/500000000000 : ℝ) (258913070447/500000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 5 (258913070447/500000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 6 (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2257/16384 : ℝ))) 7 (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2257/16384 : ℝ)) hmem 8 (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2257/16384 : ℝ))) hcmem 8 (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2257/16384 : ℝ)) (495116240441/500000000000 : ℝ) (198046496177/200000000000 : ℝ) (517826140893/1000000000000 : ℝ) (258913070451/500000000000 : ℝ) (821422661581/1000000000000 : ℝ) (821422661599/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0417_exp_lower
  have heNumeric : (2019021096757/1000000000000 : ℝ)/4 ≤ Real.exp (-10938905163709/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019021096757/1000000000000 : ℝ)/4 ≤ Real.exp ((9027/65536 : ℝ)-(821422661599/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9027/65536 : ℝ) (2257/16384 : ℝ) (821422661599/1000000000000 : ℝ) (2019021096757/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0418; no trusted numerical premise.
theorem cover7_leaf0418_exp_radius : (997542816571666531/1000000000000000000 : ℝ) ≤ Real.exp ((-9029/458752 : ℝ)/8) ∧ Real.exp ((-9029/458752 : ℝ)/8) ≤ (249385704142916633/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9029/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0418_exp_lower : (918089698565530359/1000000000000000000 : ℝ) ≤ Real.exp ((-2734725832939/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734725832939/4000000000000 : ℝ)/8) ≤ (22952242464138259/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734725832939/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0418_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019021327929/1000000000000 : ℝ) ≤ 4*Real.exp (2257/16384 : ℝ)*Real.exp (-mu (radius 7 (9029/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019021327929/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9029/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0418_exp_radius
  have hrNumeric : (980510761323/1000000000000 : ℝ) ≤ Real.exp (-9029/458752 : ℝ) ∧ Real.exp (-9029/458752 : ℝ) ≤ (245127690331/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980510761323/1000000000000 : ℝ) ≤ (radius 7 (9029/65536 : ℝ)) ∧ (radius 7 (9029/65536 : ℝ)) ≤ (245127690331/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9029/65536 : ℝ)) (980510761323/1000000000000 : ℝ) (245127690331/250000000000 : ℝ) (39293076707/200000000000 : ℝ) (196465383541/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9029/65536 : ℝ)) (980510761323/1000000000000 : ℝ) (245127690331/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980510761323/1000000000000 : ℝ) (245127690331/250000000000 : ℝ) (990255380661/1000000000000 : ℝ) (495127690331/500000000000 : ℝ) (990207433481/1000000000000 : ℝ) (990207433483/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 1 (990255380661/1000000000000 : ℝ) (495127690331/500000000000 : ℝ) (990207433481/1000000000000 : ℝ) (990207433483/1000000000000 : ℝ) (990231407071/1000000000000 : ℝ) (990231407073/1000000000000 : ℝ) (49511570339/50000000000 : ℝ) (990231406783/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 2 (990231407071/1000000000000 : ℝ) (990231407073/1000000000000 : ℝ) (49511570339/50000000000 : ℝ) (990231406783/1000000000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 3 (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 4 (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 5 (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 6 (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9029/65536 : ℝ)) 7 (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9029/65536 : ℝ))) (39293076707/200000000000 : ℝ) (196465383541/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39293076707/200000000000 : ℝ) (196465383541/1000000000000 : ℝ) (598232691767/1000000000000 : ℝ) (598232691771/1000000000000 : ℝ) (17729766317/40000000000 : ℝ) (443244157933/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 1 (598232691767/1000000000000 : ℝ) (598232691771/1000000000000 : ℝ) (17729766317/40000000000 : ℝ) (443244157933/1000000000000 : ℝ) (260369212423/500000000000 : ℝ) (130184606213/250000000000 : ℝ) (102987988757/200000000000 : ℝ) (32183746487/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 2 (260369212423/500000000000 : ℝ) (130184606213/250000000000 : ℝ) (102987988757/200000000000 : ℝ) (32183746487/62500000000 : ℝ) (103567836863/200000000000 : ℝ) (258919592161/500000000000 : ℝ) (258915534111/500000000000 : ℝ) (51783106823/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 3 (103567836863/200000000000 : ℝ) (258919592161/500000000000 : ℝ) (258915534111/500000000000 : ℝ) (51783106823/100000000000 : ℝ) (129458781567/250000000000 : ℝ) (129458781569/250000000000 : ℝ) (129458781563/250000000000 : ℝ) (517835126261/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 4 (129458781567/250000000000 : ℝ) (129458781569/250000000000 : ℝ) (129458781563/250000000000 : ℝ) (517835126261/1000000000000 : ℝ) (25891756313/50000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 5 (25891756313/50000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 6 (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9029/65536 : ℝ))) 7 (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9029/65536 : ℝ)) hmem 8 (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9029/65536 : ℝ))) hcmem 8 (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9029/65536 : ℝ)) (39609256277/40000000000 : ℝ) (61889462933/62500000000 : ℝ) (517835126259/1000000000000 : ℝ) (517835126269/1000000000000 : ℝ) (51339862867/62500000000 : ℝ) (821437805891/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0418_exp_lower
  have heNumeric : (2019021327929/1000000000000 : ℝ)/4 ≤ Real.exp (-2734725832939/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019021327929/1000000000000 : ℝ)/4 ≤ Real.exp ((2257/16384 : ℝ)-(821437805891/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2257/16384 : ℝ) (9029/65536 : ℝ) (821437805891/1000000000000 : ℝ) (2019021327929/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0419; no trusted numerical premise.
theorem cover7_leaf0419_exp_radius : (249385636190714199/250000000000000000 : ℝ) ≤ Real.exp ((-645/32768 : ℝ)/8) ∧ Real.exp ((-645/32768 : ℝ)/8) ≤ (997542544762856797/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-645/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0419_exp_lower : (183617942366639229/200000000000000000 : ℝ) ≤ Real.exp ((-10938901481979/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938901481979/16000000000000 : ℝ)/8) ≤ (459044855916598073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938901481979/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0419_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (40380431227/20000000000 : ℝ) ≤ 4*Real.exp (9029/65536 : ℝ)*Real.exp (-mu (radius 7 (4515/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (40380431227/20000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4515/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0419_exp_radius
  have hrNumeric : (980508623981/1000000000000 : ℝ) ≤ Real.exp (-645/32768 : ℝ) ∧ Real.exp (-645/32768 : ℝ) ≤ (490254311991/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980508623981/1000000000000 : ℝ) ≤ (radius 7 (4515/32768 : ℝ)) ∧ (radius 7 (4515/32768 : ℝ)) ≤ (490254311991/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4515/32768 : ℝ)) (980508623981/1000000000000 : ℝ) (490254311991/500000000000 : ℝ) (98238025093/500000000000 : ℝ) (12279753137/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4515/32768 : ℝ)) (980508623981/1000000000000 : ℝ) (490254311991/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980508623981/1000000000000 : ℝ) (490254311991/500000000000 : ℝ) (99025431199/100000000000 : ℝ) (990254311991/1000000000000 : ℝ) (990206354241/1000000000000 : ℝ) (990206354243/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 1 (99025431199/100000000000 : ℝ) (990254311991/1000000000000 : ℝ) (990206354241/1000000000000 : ℝ) (990206354243/1000000000000 : ℝ) (198046066623/200000000000 : ℝ) (990230333117/1000000000000 : ℝ) (39609213313/40000000000 : ℝ) (990230332827/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 2 (198046066623/200000000000 : ℝ) (990230333117/1000000000000 : ℝ) (39609213313/40000000000 : ℝ) (990230332827/1000000000000 : ℝ) (99023033297/100000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 3 (99023033297/100000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 4 (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 5 (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 6 (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4515/32768 : ℝ)) 7 (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4515/32768 : ℝ))) (98238025093/500000000000 : ℝ) (12279753137/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98238025093/500000000000 : ℝ) (12279753137/62500000000 : ℝ) (598238025093/1000000000000 : ℝ) (74779753137/125000000000 : ℝ) (443256190239/1000000000000 : ℝ) (443256190247/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 1 (598238025093/1000000000000 : ℝ) (74779753137/125000000000 : ℝ) (443256190239/1000000000000 : ℝ) (443256190247/1000000000000 : ℝ) (260373553833/500000000000 : ℝ) (65093388459/125000000000 : ℝ) (128737307107/250000000000 : ℝ) (102989845687/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 2 (260373553833/500000000000 : ℝ) (65093388459/125000000000 : ℝ) (128737307107/250000000000 : ℝ) (102989845687/200000000000 : ℝ) (517848168047/1000000000000 : ℝ) (258924084027/500000000000 : ℝ) (517840053779/1000000000000 : ℝ) (517840053787/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 3 (517848168047/1000000000000 : ℝ) (258924084027/500000000000 : ℝ) (517840053779/1000000000000 : ℝ) (517840053787/1000000000000 : ℝ) (517844110913/1000000000000 : ℝ) (517844110921/1000000000000 : ℝ) (517844110897/1000000000000 : ℝ) (103568822181/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 4 (517844110913/1000000000000 : ℝ) (517844110921/1000000000000 : ℝ) (517844110897/1000000000000 : ℝ) (103568822181/200000000000 : ℝ) (103568822181/200000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 5 (103568822181/200000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 6 (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4515/32768 : ℝ))) 7 (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4515/32768 : ℝ)) hmem 8 (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4515/32768 : ℝ))) hcmem 8 (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4515/32768 : ℝ)) (990230332969/1000000000000 : ℝ) (247557583243/250000000000 : ℝ) (64730513863/125000000000 : ℝ) (517844110913/1000000000000 : ℝ) (821452949051/1000000000000 : ℝ) (821452949069/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0419_exp_lower
  have heNumeric : (40380431227/20000000000 : ℝ)/4 ≤ Real.exp (-10938901481979/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (40380431227/20000000000 : ℝ)/4 ≤ Real.exp ((9029/65536 : ℝ)-(821452949069/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9029/65536 : ℝ) (4515/32768 : ℝ) (821452949069/1000000000000 : ℝ) (40380431227/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0420; no trusted numerical premise.
theorem cover7_leaf0420_exp_radius : (249385568238530281/250000000000000000 : ℝ) ≤ Real.exp ((-9031/458752 : ℝ)/8) ∧ Real.exp ((-9031/458752 : ℝ)/8) ≤ (7980338183632969/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9031/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0420_exp_lower : (918089725229624207/1000000000000000000 : ℝ) ≤ Real.exp ((-43755598457/64000000000 : ℝ)/8) ∧ Real.exp ((-43755598457/64000000000 : ℝ)/8) ≤ (57380607826851513/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-43755598457/64000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0420_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504755449259/250000000000 : ℝ) ≤ 4*Real.exp (4515/32768 : ℝ)*Real.exp (-mu (radius 7 (9031/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504755449259/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9031/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0420_exp_radius
  have hrNumeric : (245126621661/250000000000 : ℝ) ≤ Real.exp (-9031/458752 : ℝ) ∧ Real.exp (-9031/458752 : ℝ) ≤ (196101297329/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245126621661/250000000000 : ℝ) ≤ (radius 7 (9031/65536 : ℝ)) ∧ (radius 7 (9031/65536 : ℝ)) ≤ (196101297329/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9031/65536 : ℝ)) (245126621661/250000000000 : ℝ) (196101297329/200000000000 : ℝ) (19648671621/100000000000 : ℝ) (24560839527/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9031/65536 : ℝ)) (245126621661/250000000000 : ℝ) (196101297329/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245126621661/250000000000 : ℝ) (196101297329/200000000000 : ℝ) (495126621661/500000000000 : ℝ) (990253243323/1000000000000 : ℝ) (990205275003/1000000000000 : ℝ) (247551318751/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 1 (495126621661/500000000000 : ℝ) (990253243323/1000000000000 : ℝ) (990205275003/1000000000000 : ℝ) (247551318751/250000000000 : ℝ) (495114629581/500000000000 : ℝ) (247557314791/250000000000 : ℝ) (123778657359/125000000000 : ℝ) (495114629437/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 2 (495114629581/500000000000 : ℝ) (247557314791/250000000000 : ℝ) (123778657359/125000000000 : ℝ) (495114629437/500000000000 : ℝ) (990229259017/1000000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 3 (990229259017/1000000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 4 (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 5 (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 6 (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9031/65536 : ℝ)) 7 (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9031/65536 : ℝ))) (19648671621/100000000000 : ℝ) (24560839527/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19648671621/100000000000 : ℝ) (24560839527/125000000000 : ℝ) (119648671621/200000000000 : ℝ) (149560839527/250000000000 : ℝ) (5540852769/12500000000 : ℝ) (55408527691/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 1 (119648671621/200000000000 : ℝ) (149560839527/250000000000 : ℝ) (5540852769/12500000000 : ℝ) (55408527691/125000000000 : ℝ) (130188947453/250000000000 : ℝ) (260377894909/500000000000 : ℝ) (514958512293/1000000000000 : ℝ) (5149585123/10000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 2 (130188947453/250000000000 : ℝ) (260377894909/500000000000 : ℝ) (514958512293/1000000000000 : ℝ) (5149585123/10000000000 : ℝ) (129464287763/250000000000 : ℝ) (517857151059/1000000000000 : ℝ) (51784903861/100000000000 : ℝ) (517849038617/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 3 (129464287763/250000000000 : ℝ) (517857151059/1000000000000 : ℝ) (51784903861/100000000000 : ℝ) (517849038617/1000000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547419/500000000000 : ℝ) (103570618963/200000000000 : ℝ) (517853094823/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 4 (517853094831/1000000000000 : ℝ) (258926547419/500000000000 : ℝ) (103570618963/200000000000 : ℝ) (517853094823/1000000000000 : ℝ) (517853094823/1000000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 5 (517853094823/1000000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 6 (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9031/65536 : ℝ))) 7 (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9031/65536 : ℝ)) hmem 8 (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9031/65536 : ℝ))) hcmem 8 (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9031/65536 : ℝ)) (123778657377/125000000000 : ℝ) (990229259019/1000000000000 : ℝ) (258926547411/500000000000 : ℝ) (517853094831/1000000000000 : ℝ) (205367022777/250000000000 : ℝ) (6571744729/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0420_exp_lower
  have heNumeric : (504755449259/250000000000 : ℝ)/4 ≤ Real.exp (-43755598457/64000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504755449259/250000000000 : ℝ)/4 ≤ Real.exp ((4515/32768 : ℝ)-(6571744729/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4515/32768 : ℝ) (9031/65536 : ℝ) (6571744729/8000000000 : ℝ) (504755449259/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0421; no trusted numerical premise.
theorem cover7_leaf0421_exp_radius : (997542001145459513/1000000000000000000 : ℝ) ≤ Real.exp ((-1129/57344 : ℝ)/8) ∧ Real.exp ((-1129/57344 : ℝ)/8) ≤ (498771000572729757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1129/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0421_exp_lower : (229522434688646257/250000000000000000 : ℝ) ≤ Real.exp ((-10938897728601/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938897728601/16000000000000 : ℝ)/8) ≤ (918089738754585029/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938897728601/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0421_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252377754373/125000000000 : ℝ) ≤ 4*Real.exp (9031/65536 : ℝ)*Real.exp (-mu (radius 7 (1129/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (252377754373/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1129/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0421_exp_radius
  have hrNumeric : (7660190229/7812500000 : ℝ) ≤ Real.exp (-1129/57344 : ℝ) ∧ Real.exp (-1129/57344 : ℝ) ≤ (980504349313/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7660190229/7812500000 : ℝ) ≤ (radius 7 (1129/8192 : ℝ)) ∧ (radius 7 (1129/8192 : ℝ)) ≤ (980504349313/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1129/8192 : ℝ)) (7660190229/7812500000 : ℝ) (980504349313/1000000000000 : ℝ) (98248690803/500000000000 : ℝ) (49124345403/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1129/8192 : ℝ)) (7660190229/7812500000 : ℝ) (980504349313/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7660190229/7812500000 : ℝ) (980504349313/1000000000000 : ℝ) (15472690229/15625000000 : ℝ) (990252174657/1000000000000 : ℝ) (198040839153/200000000000 : ℝ) (990204195767/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 1 (15472690229/15625000000 : ℝ) (990252174657/1000000000000 : ℝ) (198040839153/200000000000 : ℝ) (990204195767/1000000000000 : ℝ) (99022818521/100000000000 : ℝ) (247557046303/250000000000 : ℝ) (990228184919/1000000000000 : ℝ) (495114092461/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 2 (99022818521/100000000000 : ℝ) (247557046303/250000000000 : ℝ) (990228184919/1000000000000 : ℝ) (495114092461/500000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 3 (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 4 (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 5 (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 6 (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1129/8192 : ℝ)) 7 (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1129/8192 : ℝ))) (98248690803/500000000000 : ℝ) (49124345403/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98248690803/500000000000 : ℝ) (49124345403/250000000000 : ℝ) (598248690803/1000000000000 : ℝ) (299124345403/500000000000 : ℝ) (221640125883/500000000000 : ℝ) (221640125887/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 1 (598248690803/1000000000000 : ℝ) (299124345403/500000000000 : ℝ) (221640125883/500000000000 : ℝ) (221640125887/500000000000 : ℝ) (130191117821/250000000000 : ℝ) (52076447129/100000000000 : ℝ) (514967795379/1000000000000 : ℝ) (257483897693/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 2 (130191117821/250000000000 : ℝ) (52076447129/100000000000 : ℝ) (514967795379/1000000000000 : ℝ) (257483897693/500000000000 : ℝ) (517866133331/1000000000000 : ℝ) (258933066669/500000000000 : ℝ) (517858022713/1000000000000 : ℝ) (517858022721/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 3 (517866133331/1000000000000 : ℝ) (258933066669/500000000000 : ℝ) (517858022713/1000000000000 : ℝ) (517858022721/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (51786207803/100000000000 : ℝ) (258931039003/500000000000 : ℝ) (258931039007/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 4 (258931039011/500000000000 : ℝ) (51786207803/100000000000 : ℝ) (258931039003/500000000000 : ℝ) (258931039007/500000000000 : ℝ) (258931039007/500000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 5 (258931039007/500000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 6 (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1129/8192 : ℝ))) 7 (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1129/8192 : ℝ)) hmem 8 (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1129/8192 : ℝ))) hcmem 8 (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1129/8192 : ℝ)) (123778523133/125000000000 : ℝ) (990228185067/1000000000000 : ℝ) (517862078013/1000000000000 : ℝ) (258931039011/500000000000 : ℝ) (821483232043/1000000000000 : ℝ) (821483232061/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0421_exp_lower
  have heNumeric : (252377754373/125000000000 : ℝ)/4 ≤ Real.exp (-10938897728601/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252377754373/125000000000 : ℝ)/4 ≤ Real.exp ((9031/65536 : ℝ)-(821483232061/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9031/65536 : ℝ) (1129/8192 : ℝ) (821483232061/1000000000000 : ℝ) (252377754373/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0422; no trusted numerical premise.
theorem cover7_leaf0422_exp_radius : (249385432334217991/250000000000000000 : ℝ) ≤ Real.exp ((-9033/458752 : ℝ)/8) ∧ Real.exp ((-9033/458752 : ℝ)/8) ≤ (199508345867374393/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9033/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0422_exp_lower : (918089752408078613/1000000000000000000 : ℝ) ≤ Real.exp ((-1367361978129/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367361978129/2000000000000 : ℝ)/8) ≤ (459044876204039307/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367361978129/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0422_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009511137597/500000000000 : ℝ) ≤ 4*Real.exp (1129/8192 : ℝ)*Real.exp (-mu (radius 7 (9033/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009511137597/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9033/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0422_exp_radius
  have hrNumeric : (196100442397/200000000000 : ℝ) ≤ Real.exp (-9033/458752 : ℝ) ∧ Real.exp (-9033/458752 : ℝ) ≤ (490251105993/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196100442397/200000000000 : ℝ) ≤ (radius 7 (9033/65536 : ℝ)) ∧ (radius 7 (9033/65536 : ℝ)) ≤ (490251105993/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9033/65536 : ℝ)) (196100442397/200000000000 : ℝ) (490251105993/500000000000 : ℝ) (24563505797/125000000000 : ℝ) (98254023191/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9033/65536 : ℝ)) (196100442397/200000000000 : ℝ) (490251105993/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196100442397/200000000000 : ℝ) (490251105993/500000000000 : ℝ) (123781388249/125000000000 : ℝ) (990251105993/1000000000000 : ℝ) (990203116529/1000000000000 : ℝ) (990203116531/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 1 (123781388249/125000000000 : ℝ) (990251105993/1000000000000 : ℝ) (990203116529/1000000000000 : ℝ) (990203116531/1000000000000 : ℝ) (49511355563/50000000000 : ℝ) (495113555631/500000000000 : ℝ) (990227110969/1000000000000 : ℝ) (247556777743/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 2 (49511355563/50000000000 : ℝ) (495113555631/500000000000 : ℝ) (990227110969/1000000000000 : ℝ) (247556777743/250000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 3 (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 4 (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 5 (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 6 (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9033/65536 : ℝ)) 7 (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9033/65536 : ℝ))) (24563505797/125000000000 : ℝ) (98254023191/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24563505797/125000000000 : ℝ) (98254023191/500000000000 : ℝ) (149563505797/250000000000 : ℝ) (598254023191/1000000000000 : ℝ) (443292280979/1000000000000 : ℝ) (443292280987/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 1 (149563505797/250000000000 : ℝ) (598254023191/1000000000000 : ℝ) (443292280979/1000000000000 : ℝ) (443292280987/1000000000000 : ℝ) (520773152083/1000000000000 : ℝ) (520773152089/1000000000000 : ℝ) (514977077687/1000000000000 : ℝ) (257488538847/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 2 (520773152083/1000000000000 : ℝ) (520773152089/1000000000000 : ℝ) (514977077687/1000000000000 : ℝ) (257488538847/500000000000 : ℝ) (103575022977/200000000000 : ℝ) (129468778723/250000000000 : ℝ) (51786700609/100000000000 : ℝ) (258933503049/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 3 (103575022977/200000000000 : ℝ) (129468778723/250000000000 : ℝ) (51786700609/100000000000 : ℝ) (258933503049/500000000000 : ℝ) (517871060487/1000000000000 : ℝ) (103574212099/200000000000 : ℝ) (517871060471/1000000000000 : ℝ) (202293383/390625000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 4 (517871060487/1000000000000 : ℝ) (103574212099/200000000000 : ℝ) (517871060471/1000000000000 : ℝ) (202293383/390625000 : ℝ) (517871060479/1000000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 5 (517871060479/1000000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 6 (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9033/65536 : ℝ))) 7 (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9033/65536 : ℝ)) hmem 8 (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9033/65536 : ℝ))) hcmem 8 (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9033/65536 : ℝ)) (495113555557/500000000000 : ℝ) (990227111117/1000000000000 : ℝ) (258935530239/500000000000 : ℝ) (64733882561/125000000000 : ℝ) (821498371857/1000000000000 : ℝ) (821498371877/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0422_exp_lower
  have heNumeric : (1009511137597/500000000000 : ℝ)/4 ≤ Real.exp (-1367361978129/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009511137597/500000000000 : ℝ)/4 ≤ Real.exp ((1129/8192 : ℝ)-(821498371877/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1129/8192 : ℝ) (9033/65536 : ℝ) (821498371877/1000000000000 : ℝ) (1009511137597/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0423; no trusted numerical premise.
theorem cover7_leaf0423_exp_radius : (997541457528358477/1000000000000000000 : ℝ) ≤ Real.exp ((-4517/229376 : ℝ)/8) ∧ Real.exp ((-4517/229376 : ℝ)/8) ≤ (498770728764179239/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4517/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0423_exp_lower : (229522441547411481/250000000000000000 : ℝ) ≤ Real.exp ((-10938893903607/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938893903607/16000000000000 : ℝ)/8) ≤ (36723590647585837/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938893903607/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0423_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252377814707/125000000000 : ℝ) ≤ 4*Real.exp (9033/65536 : ℝ)*Real.exp (-mu (radius 7 (4517/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252377814707/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4517/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0423_exp_radius
  have hrNumeric : (490250037331/500000000000 : ℝ) ≤ Real.exp (-4517/229376 : ℝ) ∧ Real.exp (-4517/229376 : ℝ) ≤ (980500074663/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490250037331/500000000000 : ℝ) ≤ (radius 7 (4517/32768 : ℝ)) ∧ (radius 7 (4517/32768 : ℝ)) ≤ (980500074663/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4517/32768 : ℝ)) (490250037331/500000000000 : ℝ) (980500074663/1000000000000 : ℝ) (196518710523/1000000000000 : ℝ) (196518710529/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4517/32768 : ℝ)) (490250037331/500000000000 : ℝ) (980500074663/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490250037331/500000000000 : ℝ) (980500074663/1000000000000 : ℝ) (990250037331/1000000000000 : ℝ) (247562509333/250000000000 : ℝ) (495101018647/500000000000 : ℝ) (198040407459/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 1 (990250037331/1000000000000 : ℝ) (247562509333/250000000000 : ℝ) (495101018647/500000000000 : ℝ) (198040407459/200000000000 : ℝ) (15472281833/15625000000 : ℝ) (495113018657/500000000000 : ℝ) (990226037021/1000000000000 : ℝ) (990226037023/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 2 (15472281833/15625000000 : ℝ) (495113018657/500000000000 : ℝ) (990226037021/1000000000000 : ℝ) (990226037023/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 3 (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 4 (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 5 (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 6 (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4517/32768 : ℝ)) 7 (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4517/32768 : ℝ))) (196518710523/1000000000000 : ℝ) (196518710529/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196518710523/1000000000000 : ℝ) (196518710529/1000000000000 : ℝ) (598259355261/1000000000000 : ℝ) (119651871053/200000000000 : ℝ) (443304309163/1000000000000 : ℝ) (443304309171/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 1 (598259355261/1000000000000 : ℝ) (119651871053/200000000000 : ℝ) (443304309163/1000000000000 : ℝ) (443304309171/1000000000000 : ℝ) (130195458053/250000000000 : ℝ) (260390916109/500000000000 : ℝ) (514986359221/1000000000000 : ℝ) (128746589807/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 2 (130195458053/250000000000 : ℝ) (260390916109/500000000000 : ℝ) (514986359221/1000000000000 : ℝ) (128746589807/250000000000 : ℝ) (129471023929/250000000000 : ℝ) (517884095723/1000000000000 : ℝ) (103575197749/200000000000 : ℝ) (517875988753/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 3 (129471023929/250000000000 : ℝ) (517884095723/1000000000000 : ℝ) (103575197749/200000000000 : ℝ) (517875988753/1000000000000 : ℝ) (51788004223/100000000000 : ℝ) (258940021119/500000000000 : ℝ) (258940021107/500000000000 : ℝ) (517880042223/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 4 (51788004223/100000000000 : ℝ) (258940021119/500000000000 : ℝ) (258940021107/500000000000 : ℝ) (517880042223/1000000000000 : ℝ) (258940021111/500000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 5 (258940021111/500000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 6 (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4517/32768 : ℝ))) 7 (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4517/32768 : ℝ)) hmem 8 (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4517/32768 : ℝ))) hcmem 8 (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4517/32768 : ℝ)) (495113018583/500000000000 : ℝ) (990226037169/1000000000000 : ℝ) (517880042221/1000000000000 : ℝ) (517880042231/1000000000000 : ℝ) (410756755279/500000000000 : ℝ) (821513510577/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0423_exp_lower
  have heNumeric : (252377814707/125000000000 : ℝ)/4 ≤ Real.exp (-10938893903607/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252377814707/125000000000 : ℝ)/4 ≤ Real.exp ((9033/65536 : ℝ)-(821513510577/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9033/65536 : ℝ) (4517/32768 : ℝ) (821513510577/1000000000000 : ℝ) (252377814707/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0424; no trusted numerical premise.
theorem cover7_leaf0424_exp_radius : (997541185719919053/1000000000000000000 : ℝ) ≤ Real.exp ((-9035/458752 : ℝ)/8) ∧ Real.exp ((-9035/458752 : ℝ)/8) ≤ (498770592859959527/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9035/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0424_exp_lower : (918089780098713159/1000000000000000000 : ℝ) ≤ Real.exp ((-5469445982203/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469445982203/8000000000000 : ℝ)/8) ≤ (22952244502467829/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469445982203/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0424_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009511381181/500000000000 : ℝ) ≤ 4*Real.exp (4517/32768 : ℝ)*Real.exp (-mu (radius 7 (9035/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009511381181/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9035/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0424_exp_radius
  have hrNumeric : (980497937343/1000000000000 : ℝ) ≤ Real.exp (-9035/458752 : ℝ) ∧ Real.exp (-9035/458752 : ℝ) ≤ (15320280271/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980497937343/1000000000000 : ℝ) ≤ (radius 7 (9035/65536 : ℝ)) ∧ (radius 7 (9035/65536 : ℝ)) ≤ (15320280271/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9035/65536 : ℝ)) (980497937343/1000000000000 : ℝ) (15320280271/15625000000 : ℝ) (196529374049/1000000000000 : ℝ) (39305874811/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9035/65536 : ℝ)) (980497937343/1000000000000 : ℝ) (15320280271/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980497937343/1000000000000 : ℝ) (15320280271/15625000000 : ℝ) (990248968671/1000000000000 : ℝ) (30945280271/31250000000 : ℝ) (49510047903/50000000000 : ℝ) (990200958061/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 1 (990248968671/1000000000000 : ℝ) (30945280271/31250000000 : ℝ) (49510047903/50000000000 : ℝ) (990200958061/1000000000000 : ℝ) (198044992673/200000000000 : ℝ) (990224963367/1000000000000 : ℝ) (495112481537/500000000000 : ℝ) (247556240769/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 2 (198044992673/200000000000 : ℝ) (990224963367/1000000000000 : ℝ) (495112481537/500000000000 : ℝ) (247556240769/250000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 3 (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 4 (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 5 (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 6 (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9035/65536 : ℝ)) 7 (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9035/65536 : ℝ))) (196529374049/1000000000000 : ℝ) (39305874811/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (196529374049/1000000000000 : ℝ) (39305874811/200000000000 : ℝ) (37391542939/62500000000 : ℝ) (149566171757/250000000000 : ℝ) (1385363551/3125000000 : ℝ) (55414542041/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 1 (37391542939/62500000000 : ℝ) (149566171757/250000000000 : ℝ) (1385363551/3125000000 : ℝ) (55414542041/125000000000 : ℝ) (65098813959/125000000000 : ℝ) (260395255839/500000000000 : ℝ) (257497819991/500000000000 : ℝ) (514995639989/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 2 (65098813959/125000000000 : ℝ) (260395255839/500000000000 : ℝ) (257497819991/500000000000 : ℝ) (514995639989/1000000000000 : ℝ) (517893075827/1000000000000 : ℝ) (258946537917/500000000000 : ℝ) (258942485339/500000000000 : ℝ) (258942485343/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 3 (517893075827/1000000000000 : ℝ) (258946537917/500000000000 : ℝ) (258942485339/500000000000 : ℝ) (258942485343/500000000000 : ℝ) (129472255813/250000000000 : ℝ) (25894451163/50000000000 : ℝ) (129472255809/250000000000 : ℝ) (103577804649/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 4 (129472255813/250000000000 : ℝ) (25894451163/50000000000 : ℝ) (129472255809/250000000000 : ℝ) (103577804649/200000000000 : ℝ) (129472255811/250000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 5 (129472255811/250000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 6 (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9035/65536 : ℝ))) 7 (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9035/65536 : ℝ)) hmem 8 (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9035/65536 : ℝ))) hcmem 8 (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9035/65536 : ℝ)) (990224963219/1000000000000 : ℝ) (495112481611/500000000000 : ℝ) (517889023243/1000000000000 : ℝ) (517889023253/1000000000000 : ℝ) (821528648147/1000000000000 : ℝ) (410764324083/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0424_exp_lower
  have heNumeric : (1009511381181/500000000000 : ℝ)/4 ≤ Real.exp (-5469445982203/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009511381181/500000000000 : ℝ)/4 ≤ Real.exp ((4517/32768 : ℝ)-(410764324083/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4517/32768 : ℝ) (9035/65536 : ℝ) (410764324083/500000000000 : ℝ) (1009511381181/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0400_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0400_certificate
#check SmaleRate.Proofs.cover7_leaf0401_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0401_certificate
#check SmaleRate.Proofs.cover7_leaf0402_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0402_certificate
#check SmaleRate.Proofs.cover7_leaf0403_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0403_certificate
#check SmaleRate.Proofs.cover7_leaf0404_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0404_certificate
#check SmaleRate.Proofs.cover7_leaf0405_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0405_certificate
#check SmaleRate.Proofs.cover7_leaf0406_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0406_certificate
#check SmaleRate.Proofs.cover7_leaf0407_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0407_certificate
#check SmaleRate.Proofs.cover7_leaf0408_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0408_certificate
#check SmaleRate.Proofs.cover7_leaf0409_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0409_certificate
#check SmaleRate.Proofs.cover7_leaf0410_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0410_certificate
#check SmaleRate.Proofs.cover7_leaf0411_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0411_certificate
#check SmaleRate.Proofs.cover7_leaf0412_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0412_certificate
#check SmaleRate.Proofs.cover7_leaf0413_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0413_certificate
#check SmaleRate.Proofs.cover7_leaf0414_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0414_certificate
#check SmaleRate.Proofs.cover7_leaf0415_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0415_certificate
#check SmaleRate.Proofs.cover7_leaf0416_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0416_certificate
#check SmaleRate.Proofs.cover7_leaf0417_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0417_certificate
#check SmaleRate.Proofs.cover7_leaf0418_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0418_certificate
#check SmaleRate.Proofs.cover7_leaf0419_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0419_certificate
#check SmaleRate.Proofs.cover7_leaf0420_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0420_certificate
#check SmaleRate.Proofs.cover7_leaf0421_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0421_certificate
#check SmaleRate.Proofs.cover7_leaf0422_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0422_certificate
#check SmaleRate.Proofs.cover7_leaf0423_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0423_certificate
#check SmaleRate.Proofs.cover7_leaf0424_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0424_certificate
