/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0625; no trusted numerical premise.
theorem cover8_leaf0625_exp_radius : (249503554744651439/250000000000000000 : ℝ) ≤ Real.exp ((-33349/2097152 : ℝ)/8) ∧ Real.exp ((-33349/2097152 : ℝ)/8) ≤ (998014218978605757/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33349/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0625_exp_lower : (460056754559826991/500000000000000000 : ℝ) ≤ Real.exp ((-85256434761511/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256434761511/128000000000000 : ℝ)/8) ≤ (920113509119653983/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256434761511/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0625_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451314707/500000000000 : ℝ) ≤ 4*Real.exp (66697/524288 : ℝ)*Real.exp (-mu (radius 8 (33349/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451314707/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33349/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0625_exp_radius
  have hrNumeric : (492111863769/500000000000 : ℝ) ≤ Real.exp (-33349/2097152 : ℝ) ∧ Real.exp (-33349/2097152 : ℝ) ≤ (984223727539/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492111863769/500000000000 : ℝ) ≤ (radius 8 (33349/262144 : ℝ)) ∧ (radius 8 (33349/262144 : ℝ)) ≤ (984223727539/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33349/262144 : ℝ)) (492111863769/500000000000 : ℝ) (984223727539/1000000000000 : ℝ) (22116048383/125000000000 : ℝ) (176928387071/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33349/262144 : ℝ)) (492111863769/500000000000 : ℝ) (984223727539/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492111863769/500000000000 : ℝ) (984223727539/1000000000000 : ℝ) (992111863769/1000000000000 : ℝ) (99211186377/100000000000 : ℝ) (198416100913/200000000000 : ℝ) (496040252283/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 1 (992111863769/1000000000000 : ℝ) (99211186377/100000000000 : ℝ) (198416100913/200000000000 : ℝ) (496040252283/500000000000 : ℝ) (992096184167/1000000000000 : ℝ) (124012023021/125000000000 : ℝ) (992096184043/1000000000000 : ℝ) (198419236809/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 2 (992096184167/1000000000000 : ℝ) (124012023021/125000000000 : ℝ) (992096184043/1000000000000 : ℝ) (198419236809/200000000000 : ℝ) (198419236821/200000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 3 (198419236821/200000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 4 (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 5 (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 6 (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33349/262144 : ℝ)) 7 (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33349/262144 : ℝ))) (22116048383/125000000000 : ℝ) (176928387071/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22116048383/125000000000 : ℝ) (176928387071/1000000000000 : ℝ) (147116048383/250000000000 : ℝ) (143668016/244140625 : ℝ) (420628561873/1000000000000 : ℝ) (420628561883/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 1 (147116048383/250000000000 : ℝ) (143668016/244140625 : ℝ) (420628561873/1000000000000 : ℝ) (420628561883/1000000000000 : ℝ) (252273188851/500000000000 : ℝ) (50454637771/100000000000 : ℝ) (248759345271/500000000000 : ℝ) (497518690551/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 2 (252273188851/500000000000 : ℝ) (50454637771/100000000000 : ℝ) (248759345271/500000000000 : ℝ) (497518690551/1000000000000 : ℝ) (250516267061/500000000000 : ℝ) (501032534131/1000000000000 : ℝ) (250510106159/500000000000 : ℝ) (62627526541/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 3 (250516267061/500000000000 : ℝ) (501032534131/1000000000000 : ℝ) (250510106159/500000000000 : ℝ) (62627526541/125000000000 : ℝ) (25051318661/50000000000 : ℝ) (50102637323/100000000000 : ℝ) (250513186591/500000000000 : ℝ) (62628296649/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 4 (25051318661/50000000000 : ℝ) (50102637323/100000000000 : ℝ) (250513186591/500000000000 : ℝ) (62628296649/125000000000 : ℝ) (501026373201/1000000000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 5 (501026373201/1000000000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 6 (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33349/262144 : ℝ))) 7 (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33349/262144 : ℝ)) hmem 8 (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33349/262144 : ℝ))) hcmem 8 (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33349/262144 : ℝ)) (124012023013/125000000000 : ℝ) (992096184107/1000000000000 : ℝ) (1252565933/2500000000 : ℝ) (501026373211/1000000000000 : ℝ) (198320082079/250000000000 : ℝ) (793280328337/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0625_exp_lower
  have heNumeric : (1027451314707/500000000000 : ℝ)/4 ≤ Real.exp (-85256434761511/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451314707/500000000000 : ℝ)/4 ≤ Real.exp ((66697/524288 : ℝ)-(793280328337/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66697/524288 : ℝ) (33349/262144 : ℝ) (793280328337/1000000000000 : ℝ) (1027451314707/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0626; no trusted numerical premise.
theorem cover8_leaf0626_exp_radius : (499007094617732349/500000000000000000 : ℝ) ≤ Real.exp ((-66699/4194304 : ℝ)/8) ∧ Real.exp ((-66699/4194304 : ℝ)/8) ≤ (998014189235464699/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66699/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0626_exp_lower : (230028377149275573/250000000000000000 : ℝ) ≤ Real.exp ((-42628217671531/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628217671531/64000000000000 : ℝ)/8) ≤ (920113508597102293/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628217671531/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0626_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451310039/500000000000 : ℝ) ≤ 4*Real.exp (33349/262144 : ℝ)*Real.exp (-mu (radius 8 (66699/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451310039/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66699/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0626_exp_radius
  have hrNumeric : (984223492881/1000000000000 : ℝ) ≤ Real.exp (-66699/4194304 : ℝ) ∧ Real.exp (-66699/4194304 : ℝ) ≤ (492111746441/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984223492881/1000000000000 : ℝ) ≤ (radius 8 (66699/524288 : ℝ)) ∧ (radius 8 (66699/524288 : ℝ)) ≤ (492111746441/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66699/524288 : ℝ)) (984223492881/1000000000000 : ℝ) (492111746441/500000000000 : ℝ) (88464846209/500000000000 : ℝ) (22116211553/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66699/524288 : ℝ)) (984223492881/1000000000000 : ℝ) (492111746441/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984223492881/1000000000000 : ℝ) (492111746441/500000000000 : ℝ) (24802793661/25000000000 : ℝ) (992111746441/1000000000000 : ℝ) (992080386299/1000000000000 : ℝ) (992080386301/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 1 (24802793661/25000000000 : ℝ) (992111746441/1000000000000 : ℝ) (992080386299/1000000000000 : ℝ) (992080386301/1000000000000 : ℝ) (992096066369/1000000000000 : ℝ) (992096066371/1000000000000 : ℝ) (198419213249/200000000000 : ℝ) (124012008281/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 2 (992096066369/1000000000000 : ℝ) (992096066371/1000000000000 : ℝ) (198419213249/200000000000 : ℝ) (124012008281/125000000000 : ℝ) (992096066307/1000000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 3 (992096066307/1000000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 4 (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 5 (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 6 (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66699/524288 : ℝ)) 7 (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66699/524288 : ℝ))) (88464846209/500000000000 : ℝ) (22116211553/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88464846209/500000000000 : ℝ) (22116211553/125000000000 : ℝ) (588464846209/1000000000000 : ℝ) (147116211553/250000000000 : ℝ) (420630113541/1000000000000 : ℝ) (420630113549/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 1 (588464846209/1000000000000 : ℝ) (147116211553/250000000000 : ℝ) (420630113541/1000000000000 : ℝ) (420630113549/1000000000000 : ℝ) (4036379839/8000000000 : ℝ) (504547479881/1000000000000 : ℝ) (4975198841/10000000000 : ℝ) (497519884107/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 2 (4036379839/8000000000 : ℝ) (504547479881/1000000000000 : ℝ) (4975198841/10000000000 : ℝ) (497519884107/1000000000000 : ℝ) (501033681987/1000000000000 : ℝ) (250516840997/500000000000 : ℝ) (501021360533/1000000000000 : ℝ) (25051068027/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 3 (501033681987/1000000000000 : ℝ) (250516840997/500000000000 : ℝ) (501021360533/1000000000000 : ℝ) (25051068027/50000000000 : ℝ) (25051376063/50000000000 : ℝ) (501027521267/1000000000000 : ℝ) (250513760611/500000000000 : ℝ) (50102752123/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 4 (25051376063/50000000000 : ℝ) (501027521267/1000000000000 : ℝ) (250513760611/500000000000 : ℝ) (50102752123/100000000000 : ℝ) (501027521241/1000000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 5 (501027521241/1000000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 6 (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66699/524288 : ℝ))) 7 (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66699/524288 : ℝ)) hmem 8 (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66699/524288 : ℝ))) hcmem 8 (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66699/524288 : ℝ)) (496048033153/500000000000 : ℝ) (99209606631/100000000000 : ℝ) (12525688031/25000000000 : ℝ) (501027521249/1000000000000 : ℝ) (793282240211/1000000000000 : ℝ) (793282240229/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0626_exp_lower
  have heNumeric : (1027451310039/500000000000 : ℝ)/4 ≤ Real.exp (-42628217671531/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451310039/500000000000 : ℝ)/4 ≤ Real.exp ((33349/262144 : ℝ)-(793282240229/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33349/262144 : ℝ) (66699/524288 : ℝ) (793282240229/1000000000000 : ℝ) (1027451310039/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0627; no trusted numerical premise.
theorem cover8_leaf0627_exp_radius : (499007079746162263/500000000000000000 : ℝ) ≤ Real.exp ((-16675/1048576 : ℝ)/8) ∧ Real.exp ((-16675/1048576 : ℝ)/8) ≤ (998014159492324527/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16675/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0627_exp_lower : (920113508076620857/1000000000000000000 : ℝ) ≤ Real.exp ((-85256435922309/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256435922309/128000000000000 : ℝ)/8) ≤ (460056754038310429/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256435922309/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0627_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902610779/1000000000000 : ℝ) ≤ 4*Real.exp (66699/524288 : ℝ)*Real.exp (-mu (radius 8 (16675/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902610779/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16675/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0627_exp_radius
  have hrNumeric : (61513953639/62500000000 : ℝ) ≤ Real.exp (-16675/1048576 : ℝ) ∧ Real.exp (-16675/1048576 : ℝ) ≤ (39368930329/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61513953639/62500000000 : ℝ) ≤ (radius 8 (16675/131072 : ℝ)) ∧ (radius 8 (16675/131072 : ℝ)) ≤ (39368930329/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16675/131072 : ℝ)) (61513953639/62500000000 : ℝ) (39368930329/40000000000 : ℝ) (176930997761/1000000000000 : ℝ) (22116374721/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16675/131072 : ℝ)) (61513953639/62500000000 : ℝ) (39368930329/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61513953639/62500000000 : ℝ) (39368930329/40000000000 : ℝ) (124013953639/125000000000 : ℝ) (992111629113/1000000000000 : ℝ) (496040134017/500000000000 : ℝ) (248020067009/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 1 (124013953639/125000000000 : ℝ) (992111629113/1000000000000 : ℝ) (496040134017/500000000000 : ℝ) (248020067009/250000000000 : ℝ) (992095948573/1000000000000 : ℝ) (39683837943/40000000000 : ℝ) (992095948449/1000000000000 : ℝ) (992095948451/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 2 (992095948573/1000000000000 : ℝ) (39683837943/40000000000 : ℝ) (992095948449/1000000000000 : ℝ) (992095948451/1000000000000 : ℝ) (992095948511/1000000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 3 (992095948511/1000000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 4 (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 5 (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 6 (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16675/131072 : ℝ)) 7 (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16675/131072 : ℝ))) (176930997761/1000000000000 : ℝ) (22116374721/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176930997761/1000000000000 : ℝ) (22116374721/125000000000 : ℝ) (459738671/781250000 : ℝ) (147116374721/250000000000 : ℝ) (42063166519/100000000000 : ℝ) (420631665199/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 1 (459738671/781250000 : ℝ) (147116374721/250000000000 : ℝ) (42063166519/100000000000 : ℝ) (420631665199/1000000000000 : ℝ) (100909716407/200000000000 : ℝ) (252274291021/500000000000 : ℝ) (124380269411/250000000000 : ℝ) (124380269413/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 2 (100909716407/200000000000 : ℝ) (252274291021/500000000000 : ℝ) (124380269411/250000000000 : ℝ) (124380269413/250000000000 : ℝ) (501034829839/1000000000000 : ℝ) (501034829847/1000000000000 : ℝ) (501022508733/1000000000000 : ℝ) (250511254371/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 3 (501034829839/1000000000000 : ℝ) (501034829847/1000000000000 : ℝ) (501022508733/1000000000000 : ℝ) (250511254371/500000000000 : ℝ) (250514334643/500000000000 : ℝ) (100205733859/200000000000 : ℝ) (7828572957/15625000000 : ℝ) (501028669257/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 4 (250514334643/500000000000 : ℝ) (100205733859/200000000000 : ℝ) (7828572957/15625000000 : ℝ) (501028669257/1000000000000 : ℝ) (501028669267/1000000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 5 (501028669267/1000000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 6 (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16675/131072 : ℝ))) 7 (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16675/131072 : ℝ)) hmem 8 (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16675/131072 : ℝ))) hcmem 8 (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16675/131072 : ℝ)) (99209594851/100000000000 : ℝ) (992095948513/1000000000000 : ℝ) (250514334633/500000000000 : ℝ) (125257167319/250000000000 : ℝ) (793284152083/1000000000000 : ℝ) (793284152103/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0627_exp_lower
  have heNumeric : (2054902610779/1000000000000 : ℝ)/4 ≤ Real.exp (-85256435922309/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902610779/1000000000000 : ℝ)/4 ≤ Real.exp ((66699/524288 : ℝ)-(793284152103/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66699/524288 : ℝ) (16675/131072 : ℝ) (793284152103/1000000000000 : ℝ) (2054902610779/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0628; no trusted numerical premise.
theorem cover8_leaf0628_exp_radius : (998014129749185241/1000000000000000000 : ℝ) ≤ Real.exp ((-66701/4194304 : ℝ)/8) ∧ Real.exp ((-66701/4194304 : ℝ)/8) ≤ (499007064874592621/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66701/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0628_exp_lower : (460056753778702289/500000000000000000 : ℝ) ≤ Real.exp ((-21314109125037/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314109125037/32000000000000 : ℝ)/8) ≤ (920113507557404579/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314109125037/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0628_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451300751/500000000000 : ℝ) ≤ 4*Real.exp (16675/131072 : ℝ)*Real.exp (-mu (radius 8 (66701/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451300751/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66701/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0628_exp_radius
  have hrNumeric : (492111511783/500000000000 : ℝ) ≤ Real.exp (-66701/4194304 : ℝ) ∧ Real.exp (-66701/4194304 : ℝ) ≤ (984223023567/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492111511783/500000000000 : ℝ) ≤ (radius 8 (66701/524288 : ℝ)) ∧ (radius 8 (66701/524288 : ℝ)) ≤ (984223023567/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66701/524288 : ℝ)) (492111511783/500000000000 : ℝ) (984223023567/1000000000000 : ℝ) (176932303101/1000000000000 : ℝ) (176932303107/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66701/524288 : ℝ)) (492111511783/500000000000 : ℝ) (984223023567/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492111511783/500000000000 : ℝ) (984223023567/1000000000000 : ℝ) (992111511783/1000000000000 : ℝ) (124013938973/125000000000 : ℝ) (992080149769/1000000000000 : ℝ) (99208014977/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 1 (992111511783/1000000000000 : ℝ) (124013938973/125000000000 : ℝ) (992080149769/1000000000000 : ℝ) (99208014977/100000000000 : ℝ) (124011978847/125000000000 : ℝ) (992095830777/1000000000000 : ℝ) (248023957663/250000000000 : ℝ) (496047915327/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 2 (124011978847/125000000000 : ℝ) (992095830777/1000000000000 : ℝ) (248023957663/250000000000 : ℝ) (496047915327/500000000000 : ℝ) (496047915357/500000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 3 (496047915357/500000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 4 (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 5 (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 6 (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66701/524288 : ℝ)) 7 (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66701/524288 : ℝ))) (176932303101/1000000000000 : ℝ) (176932303107/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176932303101/1000000000000 : ℝ) (176932303107/1000000000000 : ℝ) (11769323031/20000000000 : ℝ) (294233075777/500000000000 : ℝ) (42063321683/100000000000 : ℝ) (210316608419/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 1 (11769323031/20000000000 : ℝ) (294233075777/500000000000 : ℝ) (42063321683/100000000000 : ℝ) (210316608419/500000000000 : ℝ) (50454968419/100000000000 : ℝ) (126137421049/250000000000 : ℝ) (497522271181/1000000000000 : ℝ) (497522271189/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 2 (50454968419/100000000000 : ℝ) (126137421049/250000000000 : ℝ) (497522271181/1000000000000 : ℝ) (497522271189/1000000000000 : ℝ) (100207195537/200000000000 : ℝ) (501035977693/1000000000000 : ℝ) (15656989279/31250000000 : ℝ) (62627957117/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 3 (100207195537/200000000000 : ℝ) (501035977693/1000000000000 : ℝ) (15656989279/31250000000 : ℝ) (62627957117/125000000000 : ℝ) (250514908653/500000000000 : ℝ) (100205963463/200000000000 : ℝ) (125257454317/250000000000 : ℝ) (501029817277/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 4 (250514908653/500000000000 : ℝ) (100205963463/200000000000 : ℝ) (125257454317/250000000000 : ℝ) (501029817277/1000000000000 : ℝ) (501029817287/1000000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 5 (501029817287/1000000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 6 (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66701/524288 : ℝ))) 7 (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66701/524288 : ℝ)) hmem 8 (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66701/524288 : ℝ))) hcmem 8 (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66701/524288 : ℝ)) (992095830713/1000000000000 : ℝ) (248023957679/250000000000 : ℝ) (250514908643/500000000000 : ℝ) (31314363581/62500000000 : ℝ) (793286063947/1000000000000 : ℝ) (396643031983/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0628_exp_lower
  have heNumeric : (1027451300751/500000000000 : ℝ)/4 ≤ Real.exp (-21314109125037/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451300751/500000000000 : ℝ)/4 ≤ Real.exp ((16675/131072 : ℝ)-(396643031983/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16675/131072 : ℝ) (66701/524288 : ℝ) (396643031983/500000000000 : ℝ) (1027451300751/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0629; no trusted numerical premise.
theorem cover8_leaf0629_exp_radius : (499007050003023421/500000000000000000 : ℝ) ≤ Real.exp ((-33351/2097152 : ℝ)/8) ∧ Real.exp ((-33351/2097152 : ℝ)/8) ≤ (998014100006046843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33351/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0629_exp_lower : (184022701408212731/200000000000000000 : ℝ) ≤ Real.exp ((-85256437074787/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256437074787/128000000000000 : ℝ)/8) ≤ (115014188380132957/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256437074787/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0629_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902592277/1000000000000 : ℝ) ≤ 4*Real.exp (66701/524288 : ℝ)*Real.exp (-mu (radius 8 (33351/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902592277/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33351/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0629_exp_radius
  have hrNumeric : (984222788909/1000000000000 : ℝ) ≤ Real.exp (-33351/2097152 : ℝ) ∧ Real.exp (-33351/2097152 : ℝ) ≤ (98422278891/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984222788909/1000000000000 : ℝ) ≤ (radius 8 (33351/262144 : ℝ)) ∧ (radius 8 (33351/262144 : ℝ)) ≤ (98422278891/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33351/262144 : ℝ)) (984222788909/1000000000000 : ℝ) (98422278891/100000000000 : ℝ) (22116701053/125000000000 : ℝ) (176933608431/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33351/262144 : ℝ)) (984222788909/1000000000000 : ℝ) (98422278891/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984222788909/1000000000000 : ℝ) (98422278891/100000000000 : ℝ) (496055697227/500000000000 : ℝ) (198422278891/200000000000 : ℝ) (62005001969/62500000000 : ℝ) (198416006301/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 1 (496055697227/500000000000 : ℝ) (198422278891/200000000000 : ℝ) (62005001969/62500000000 : ℝ) (198416006301/200000000000 : ℝ) (992095712979/1000000000000 : ℝ) (49604785649/50000000000 : ℝ) (198419142571/200000000000 : ℝ) (992095712857/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 2 (992095712979/1000000000000 : ℝ) (49604785649/50000000000 : ℝ) (198419142571/200000000000 : ℝ) (992095712857/1000000000000 : ℝ) (992095712917/1000000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 3 (992095712917/1000000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 4 (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 5 (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 6 (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33351/262144 : ℝ)) 7 (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33351/262144 : ℝ))) (22116701053/125000000000 : ℝ) (176933608431/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22116701053/125000000000 : ℝ) (176933608431/1000000000000 : ℝ) (147116701053/250000000000 : ℝ) (73558350527/125000000000 : ℝ) (105158692111/250000000000 : ℝ) (420634768453/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 1 (147116701053/250000000000 : ℝ) (73558350527/125000000000 : ℝ) (105158692111/250000000000 : ℝ) (420634768453/1000000000000 : ℝ) (63068848291/125000000000 : ℝ) (100910157267/200000000000 : ℝ) (497523464699/1000000000000 : ℝ) (497523464707/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 2 (63068848291/125000000000 : ℝ) (100910157267/200000000000 : ℝ) (497523464699/1000000000000 : ℝ) (497523464707/1000000000000 : ℝ) (501037125513/1000000000000 : ℝ) (501037125521/1000000000000 : ℝ) (100204961021/200000000000 : ℝ) (501024805113/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 3 (501037125513/1000000000000 : ℝ) (501037125521/1000000000000 : ℝ) (100204961021/200000000000 : ℝ) (501024805113/1000000000000 : ℝ) (501030965309/1000000000000 : ℝ) (501030965317/1000000000000 : ℝ) (501030965271/1000000000000 : ℝ) (3131443533/6250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 4 (501030965309/1000000000000 : ℝ) (501030965317/1000000000000 : ℝ) (501030965271/1000000000000 : ℝ) (3131443533/6250000000 : ℝ) (50103096529/100000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 5 (50103096529/100000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 6 (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33351/262144 : ℝ))) 7 (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33351/262144 : ℝ)) hmem 8 (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33351/262144 : ℝ))) hcmem 8 (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33351/262144 : ℝ)) (248023928229/250000000000 : ℝ) (992095712919/1000000000000 : ℝ) (501030965289/1000000000000 : ℝ) (501030965299/1000000000000 : ℝ) (99160996973/125000000000 : ℝ) (198321993951/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0629_exp_lower
  have heNumeric : (2054902592277/1000000000000 : ℝ)/4 ≤ Real.exp (-85256437074787/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902592277/1000000000000 : ℝ)/4 ≤ Real.exp ((66701/524288 : ℝ)-(198321993951/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66701/524288 : ℝ) (33351/262144 : ℝ) (198321993951/250000000000 : ℝ) (2054902592277/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0630; no trusted numerical premise.
theorem cover8_leaf0630_exp_radius : (998014070262909329/1000000000000000000 : ℝ) ≤ Real.exp ((-66703/4194304 : ℝ)/8) ∧ Real.exp ((-66703/4194304 : ℝ)/8) ≤ (99801407026290933/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66703/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0630_exp_lower : (920113506527138029/1000000000000000000 : ℝ) ≤ Real.exp ((-42628218823369/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628218823369/64000000000000 : ℝ)/8) ≤ (92011350652713803/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628218823369/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0630_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980516619/200000000000 : ℝ) ≤ 4*Real.exp (33351/262144 : ℝ)*Real.exp (-mu (radius 8 (66703/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980516619/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66703/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0630_exp_radius
  have hrNumeric : (246055638563/250000000000 : ℝ) ≤ Real.exp (-66703/4194304 : ℝ) ∧ Real.exp (-66703/4194304 : ℝ) ≤ (984222554253/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246055638563/250000000000 : ℝ) ≤ (radius 8 (66703/524288 : ℝ)) ∧ (radius 8 (66703/524288 : ℝ)) ≤ (984222554253/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66703/524288 : ℝ)) (246055638563/250000000000 : ℝ) (984222554253/1000000000000 : ℝ) (88467456869/500000000000 : ℝ) (35386982749/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66703/524288 : ℝ)) (246055638563/250000000000 : ℝ) (984222554253/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246055638563/250000000000 : ℝ) (984222554253/1000000000000 : ℝ) (496055638563/500000000000 : ℝ) (992111277127/1000000000000 : ℝ) (496039956619/500000000000 : ℝ) (24801997831/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 1 (496055638563/500000000000 : ℝ) (992111277127/1000000000000 : ℝ) (496039956619/500000000000 : ℝ) (24801997831/25000000000 : ℝ) (496047797591/500000000000 : ℝ) (62005974699/62500000000 : ℝ) (496047797529/500000000000 : ℝ) (49604779753/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 2 (496047797591/500000000000 : ℝ) (62005974699/62500000000 : ℝ) (496047797529/500000000000 : ℝ) (49604779753/50000000000 : ℝ) (12401194939/12500000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 3 (12401194939/12500000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 4 (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 5 (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 6 (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66703/524288 : ℝ)) 7 (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66703/524288 : ℝ))) (88467456869/500000000000 : ℝ) (35386982749/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88467456869/500000000000 : ℝ) (35386982749/200000000000 : ℝ) (588467456869/1000000000000 : ℝ) (588467456873/1000000000000 : ℝ) (420636320041/1000000000000 : ℝ) (8412726401/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 1 (588467456869/1000000000000 : ℝ) (588467456873/1000000000000 : ℝ) (420636320041/1000000000000 : ℝ) (8412726401/20000000000 : ℝ) (100910377691/200000000000 : ℝ) (252275944231/500000000000 : ℝ) (124381164551/250000000000 : ℝ) (124381164553/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 2 (100910377691/200000000000 : ℝ) (252275944231/500000000000 : ℝ) (124381164551/250000000000 : ℝ) (124381164553/250000000000 : ℝ) (501038273329/1000000000000 : ℝ) (501038273337/1000000000000 : ℝ) (501025953269/1000000000000 : ℝ) (250512976639/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 3 (501038273329/1000000000000 : ℝ) (501038273337/1000000000000 : ℝ) (501025953269/1000000000000 : ℝ) (250512976639/500000000000 : ℝ) (501032113299/1000000000000 : ℝ) (125258028327/250000000000 : ℝ) (501032113261/1000000000000 : ℝ) (50103211327/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 4 (501032113299/1000000000000 : ℝ) (125258028327/250000000000 : ℝ) (501032113261/1000000000000 : ℝ) (50103211327/100000000000 : ℝ) (782862677/1562500000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 5 (782862677/1562500000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 6 (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66703/524288 : ℝ))) 7 (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66703/524288 : ℝ)) hmem 8 (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66703/524288 : ℝ))) hcmem 8 (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66703/524288 : ℝ)) (992095595119/1000000000000 : ℝ) (496047797561/500000000000 : ℝ) (501032113279/1000000000000 : ℝ) (501032113289/1000000000000 : ℝ) (396644943801/500000000000 : ℝ) (793289887621/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0630_exp_lower
  have heNumeric : (410980516619/200000000000 : ℝ)/4 ≤ Real.exp (-42628218823369/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980516619/200000000000 : ℝ)/4 ≤ Real.exp ((33351/262144 : ℝ)-(793289887621/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33351/262144 : ℝ) (66703/524288 : ℝ) (793289887621/1000000000000 : ℝ) (410980516619/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0631; no trusted numerical premise.
theorem cover8_leaf0631_exp_radius : (998014040519772703/1000000000000000000 : ℝ) ≤ Real.exp ((-4169/262144 : ℝ)/8) ∧ Real.exp ((-4169/262144 : ℝ)/8) ≤ (31187938766242897/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4169/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0631_exp_lower : (230028376504079447/250000000000000000 : ℝ) ≤ Real.exp ((-85256438215233/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256438215233/128000000000000 : ℝ)/8) ≤ (920113506016317789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256438215233/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0631_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431410873/62500000000 : ℝ) ≤ 4*Real.exp (66703/524288 : ℝ)*Real.exp (-mu (radius 8 (4169/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (128431410873/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4169/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0631_exp_radius
  have hrNumeric : (246055579899/250000000000 : ℝ) ≤ Real.exp (-4169/262144 : ℝ) ∧ Real.exp (-4169/262144 : ℝ) ≤ (984222319597/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246055579899/250000000000 : ℝ) ≤ (radius 8 (4169/32768 : ℝ)) ∧ (radius 8 (4169/32768 : ℝ)) ≤ (984222319597/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4169/32768 : ℝ)) (246055579899/250000000000 : ℝ) (984222319597/1000000000000 : ℝ) (44234054759/250000000000 : ℝ) (176936219043/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4169/32768 : ℝ)) (246055579899/250000000000 : ℝ) (984222319597/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246055579899/250000000000 : ℝ) (984222319597/1000000000000 : ℝ) (496055579899/500000000000 : ℝ) (992111159799/1000000000000 : ℝ) (496039897487/500000000000 : ℝ) (39683191799/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 1 (496055579899/500000000000 : ℝ) (992111159799/1000000000000 : ℝ) (496039897487/500000000000 : ℝ) (39683191799/40000000000 : ℝ) (496047738693/500000000000 : ℝ) (992095477387/1000000000000 : ℝ) (496047738631/500000000000 : ℝ) (62005967329/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 2 (496047738693/500000000000 : ℝ) (992095477387/1000000000000 : ℝ) (496047738631/500000000000 : ℝ) (62005967329/62500000000 : ℝ) (248023869331/250000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 3 (248023869331/250000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 4 (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 5 (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 6 (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4169/32768 : ℝ)) 7 (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4169/32768 : ℝ))) (44234054759/250000000000 : ℝ) (176936219043/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44234054759/250000000000 : ℝ) (176936219043/1000000000000 : ℝ) (294234054759/500000000000 : ℝ) (294234054761/500000000000 : ℝ) (210318935807/500000000000 : ℝ) (420637871623/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 1 (294234054759/500000000000 : ℝ) (294234054761/500000000000 : ℝ) (210318935807/500000000000 : ℝ) (420637871623/1000000000000 : ℝ) (252276495283/500000000000 : ℝ) (504552990573/1000000000000 : ℝ) (49752585169/100000000000 : ℝ) (248762925849/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 2 (252276495283/500000000000 : ℝ) (504552990573/1000000000000 : ℝ) (49752585169/100000000000 : ℝ) (248762925849/500000000000 : ℝ) (62629927641/125000000000 : ℝ) (31314963821/62500000000 : ℝ) (62628387677/125000000000 : ℝ) (20041084057/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 3 (62629927641/125000000000 : ℝ) (31314963821/62500000000 : ℝ) (62628387677/125000000000 : ℝ) (20041084057/40000000000 : ℝ) (62629157659/125000000000 : ℝ) (501033261281/1000000000000 : ℝ) (250516630617/500000000000 : ℝ) (501033261243/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 4 (62629157659/125000000000 : ℝ) (501033261281/1000000000000 : ℝ) (250516630617/500000000000 : ℝ) (501033261243/1000000000000 : ℝ) (501033261253/1000000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 5 (501033261253/1000000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 6 (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4169/32768 : ℝ))) 7 (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4169/32768 : ℝ)) hmem 8 (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4169/32768 : ℝ))) hcmem 8 (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4169/32768 : ℝ)) (992095477323/1000000000000 : ℝ) (496047738663/500000000000 : ℝ) (125258315313/250000000000 : ℝ) (250516630631/500000000000 : ℝ) (24790368731/31250000000 : ℝ) (793291799411/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0631_exp_lower
  have heNumeric : (128431410873/62500000000 : ℝ)/4 ≤ Real.exp (-85256438215233/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431410873/62500000000 : ℝ)/4 ≤ Real.exp ((66703/524288 : ℝ)-(793291799411/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66703/524288 : ℝ) (4169/32768 : ℝ) (793291799411/1000000000000 : ℝ) (128431410873/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0632; no trusted numerical premise.
theorem cover8_leaf0632_exp_radius : (998014010776636963/1000000000000000000 : ℝ) ≤ Real.exp ((-66705/4194304 : ℝ)/8) ∧ Real.exp ((-66705/4194304 : ℝ)/8) ≤ (249503502694159241/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66705/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0632_exp_lower : (460056752753381351/500000000000000000 : ℝ) ≤ Real.exp ((-1065705484779/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065705484779/1600000000000 : ℝ)/8) ≤ (920113505506762703/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065705484779/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0632_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1003370393/488281250 : ℝ) ≤ 4*Real.exp (4169/32768 : ℝ)*Real.exp (-mu (radius 8 (66705/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1003370393/488281250 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66705/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0632_exp_radius
  have hrNumeric : (984222084939/1000000000000 : ℝ) ≤ Real.exp (-66705/4194304 : ℝ) ∧ Real.exp (-66705/4194304 : ℝ) ≤ (49211104247/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984222084939/1000000000000 : ℝ) ≤ (radius 8 (66705/524288 : ℝ)) ∧ (radius 8 (66705/524288 : ℝ)) ≤ (49211104247/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66705/524288 : ℝ)) (984222084939/1000000000000 : ℝ) (49211104247/50000000000 : ℝ) (17693752433/100000000000 : ℝ) (176937524337/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66705/524288 : ℝ)) (984222084939/1000000000000 : ℝ) (49211104247/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984222084939/1000000000000 : ℝ) (49211104247/50000000000 : ℝ) (992111042469/1000000000000 : ℝ) (99211104247/100000000000 : ℝ) (248019919177/250000000000 : ℝ) (99207967671/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 1 (992111042469/1000000000000 : ℝ) (99211104247/100000000000 : ℝ) (248019919177/250000000000 : ℝ) (99207967671/100000000000 : ℝ) (248023839897/250000000000 : ℝ) (99209535959/100000000000 : ℝ) (124011919933/125000000000 : ℝ) (992095359467/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 2 (248023839897/250000000000 : ℝ) (99209535959/100000000000 : ℝ) (124011919933/125000000000 : ℝ) (992095359467/1000000000000 : ℝ) (496047679763/500000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 3 (496047679763/500000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 4 (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 5 (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 6 (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66705/524288 : ℝ)) 7 (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66705/524288 : ℝ))) (17693752433/100000000000 : ℝ) (176937524337/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17693752433/100000000000 : ℝ) (176937524337/1000000000000 : ℝ) (117693752433/200000000000 : ℝ) (588468762169/1000000000000 : ℝ) (52579927897/125000000000 : ℝ) (84127884637/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 1 (117693752433/200000000000 : ℝ) (588468762169/1000000000000 : ℝ) (52579927897/125000000000 : ℝ) (84127884637/200000000000 : ℝ) (50455409267/100000000000 : ℝ) (504554092677/1000000000000 : ℝ) (31095440323/62500000000 : ℝ) (62190880647/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 2 (50455409267/100000000000 : ℝ) (504554092677/1000000000000 : ℝ) (31095440323/62500000000 : ℝ) (62190880647/125000000000 : ℝ) (501040568919/1000000000000 : ℝ) (501040568927/1000000000000 : ℝ) (125257062389/250000000000 : ℝ) (125257062391/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 3 (501040568919/1000000000000 : ℝ) (501040568927/1000000000000 : ℝ) (125257062389/250000000000 : ℝ) (125257062391/250000000000 : ℝ) (501034409237/1000000000000 : ℝ) (250517204623/500000000000 : ℝ) (501034409199/1000000000000 : ℝ) (62629301151/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 4 (501034409237/1000000000000 : ℝ) (250517204623/500000000000 : ℝ) (501034409199/1000000000000 : ℝ) (62629301151/125000000000 : ℝ) (250517204609/500000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 5 (250517204609/500000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 6 (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66705/524288 : ℝ))) 7 (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66705/524288 : ℝ)) hmem 8 (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66705/524288 : ℝ))) hcmem 8 (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66705/524288 : ℝ)) (39683814381/40000000000 : ℝ) (992095359529/1000000000000 : ℝ) (501034409217/1000000000000 : ℝ) (501034409227/1000000000000 : ℝ) (79329371117/100000000000 : ℝ) (79329371119/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0632_exp_lower
  have heNumeric : (1003370393/488281250 : ℝ)/4 ≤ Real.exp (-1065705484779/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1003370393/488281250 : ℝ)/4 ≤ Real.exp ((4169/32768 : ℝ)-(79329371119/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4169/32768 : ℝ) (66705/524288 : ℝ) (79329371119/100000000000 : ℝ) (1003370393/488281250 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0633; no trusted numerical premise.
theorem cover8_leaf0633_exp_radius : (99801398103350211/100000000000000000 : ℝ) ≤ Real.exp ((-33353/2097152 : ℝ)/8) ∧ Real.exp ((-33353/2097152 : ℝ)/8) ≤ (998013981033502111/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33353/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0633_exp_lower : (57507094062454867/62500000000000000 : ℝ) ≤ Real.exp ((-85256439347103/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256439347103/128000000000000 : ℝ)/8) ≤ (920113504999277873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256439347103/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0633_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902555797/1000000000000 : ℝ) ≤ 4*Real.exp (66705/524288 : ℝ)*Real.exp (-mu (radius 8 (33353/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902555797/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33353/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0633_exp_radius
  have hrNumeric : (492110925141/500000000000 : ℝ) ≤ Real.exp (-33353/2097152 : ℝ) ∧ Real.exp (-33353/2097152 : ℝ) ≤ (984221850283/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492110925141/500000000000 : ℝ) ≤ (radius 8 (33353/262144 : ℝ)) ∧ (radius 8 (33353/262144 : ℝ)) ≤ (984221850283/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33353/262144 : ℝ)) (492110925141/500000000000 : ℝ) (984221850283/1000000000000 : ℝ) (88469414807/500000000000 : ℝ) (176938829621/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33353/262144 : ℝ)) (492110925141/500000000000 : ℝ) (984221850283/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492110925141/500000000000 : ℝ) (984221850283/1000000000000 : ℝ) (992110925141/1000000000000 : ℝ) (496055462571/500000000000 : ℝ) (992079558443/1000000000000 : ℝ) (198415911689/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 1 (992110925141/1000000000000 : ℝ) (496055462571/500000000000 : ℝ) (992079558443/1000000000000 : ℝ) (198415911689/200000000000 : ℝ) (15501488153/15625000000 : ℝ) (496047620897/500000000000 : ℝ) (248023810417/250000000000 : ℝ) (99209524167/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 2 (15501488153/15625000000 : ℝ) (496047620897/500000000000 : ℝ) (248023810417/250000000000 : ℝ) (99209524167/100000000000 : ℝ) (99209524173/100000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 3 (99209524173/100000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 4 (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 5 (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 6 (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33353/262144 : ℝ)) 7 (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33353/262144 : ℝ))) (88469414807/500000000000 : ℝ) (176938829621/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88469414807/500000000000 : ℝ) (176938829621/1000000000000 : ℝ) (588469414807/1000000000000 : ℝ) (588469414811/1000000000000 : ℝ) (657251523/1562500000 : ℝ) (42064097473/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 1 (588469414807/1000000000000 : ℝ) (588469414811/1000000000000 : ℝ) (657251523/1562500000 : ℝ) (42064097473/100000000000 : ℝ) (504555194763/1000000000000 : ℝ) (504555194771/1000000000000 : ℝ) (497528238633/1000000000000 : ℝ) (497528238641/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 2 (504555194763/1000000000000 : ℝ) (504555194771/1000000000000 : ℝ) (497528238633/1000000000000 : ℝ) (497528238641/1000000000000 : ℝ) (250520858349/500000000000 : ℝ) (250520858353/500000000000 : ℝ) (501029397683/1000000000000 : ℝ) (125257349423/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 3 (250520858349/500000000000 : ℝ) (250520858353/500000000000 : ℝ) (501029397683/1000000000000 : ℝ) (125257349423/250000000000 : ℝ) (50103555719/100000000000 : ℝ) (501035557199/1000000000000 : ℝ) (15657361161/31250000000 : ℝ) (250517778581/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 4 (50103555719/100000000000 : ℝ) (501035557199/1000000000000 : ℝ) (15657361161/31250000000 : ℝ) (250517778581/500000000000 : ℝ) (501035557171/1000000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 5 (501035557171/1000000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 6 (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33353/262144 : ℝ))) 7 (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33353/262144 : ℝ)) hmem 8 (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33353/262144 : ℝ))) hcmem 8 (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33353/262144 : ℝ)) (992095241729/1000000000000 : ℝ) (248023810433/250000000000 : ℝ) (50103555717/100000000000 : ℝ) (501035557181/1000000000000 : ℝ) (79329562293/100000000000 : ℝ) (793295622951/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0633_exp_lower
  have heNumeric : (2054902555797/1000000000000 : ℝ)/4 ≤ Real.exp (-85256439347103/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902555797/1000000000000 : ℝ)/4 ≤ Real.exp ((66705/524288 : ℝ)-(793295622951/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66705/524288 : ℝ) (33353/262144 : ℝ) (793295622951/1000000000000 : ℝ) (2054902555797/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0634; no trusted numerical premise.
theorem cover8_leaf0634_exp_radius : (998013951290368143/1000000000000000000 : ℝ) ≤ Real.exp ((-66707/4194304 : ℝ)/8) ∧ Real.exp ((-66707/4194304 : ℝ)/8) ≤ (62375871955648009/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66707/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0634_exp_lower : (46005675224710417/50000000000000000 : ℝ) ≤ Real.exp ((-42628219954599/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628219954599/64000000000000 : ℝ)/8) ≤ (920113504494208341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628219954599/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0634_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902546773/1000000000000 : ℝ) ≤ 4*Real.exp (33353/262144 : ℝ)*Real.exp (-mu (radius 8 (66707/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902546773/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66707/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0634_exp_radius
  have hrNumeric : (314950917/320000000 : ℝ) ≤ Real.exp (-66707/4194304 : ℝ) ∧ Real.exp (-66707/4194304 : ℝ) ≤ (492110807813/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (314950917/320000000 : ℝ) ≤ (radius 8 (66707/524288 : ℝ)) ∧ (radius 8 (66707/524288 : ℝ)) ≤ (492110807813/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66707/524288 : ℝ)) (314950917/320000000 : ℝ) (492110807813/500000000000 : ℝ) (176940134889/1000000000000 : ℝ) (35388026979/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66707/524288 : ℝ)) (314950917/320000000 : ℝ) (492110807813/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (314950917/320000000 : ℝ) (492110807813/500000000000 : ℝ) (248027701953/250000000000 : ℝ) (992110807813/1000000000000 : ℝ) (496039720089/500000000000 : ℝ) (49603972009/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 1 (248027701953/250000000000 : ℝ) (992110807813/1000000000000 : ℝ) (496039720089/500000000000 : ℝ) (49603972009/50000000000 : ℝ) (198419024799/200000000000 : ℝ) (992095123997/1000000000000 : ℝ) (992095123871/1000000000000 : ℝ) (992095123873/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 2 (198419024799/200000000000 : ℝ) (992095123997/1000000000000 : ℝ) (992095123871/1000000000000 : ℝ) (992095123873/1000000000000 : ℝ) (992095123933/1000000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 3 (992095123933/1000000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 4 (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 5 (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 6 (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66707/524288 : ℝ)) 7 (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66707/524288 : ℝ))) (176940134889/1000000000000 : ℝ) (35388026979/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176940134889/1000000000000 : ℝ) (35388026979/200000000000 : ℝ) (147117516861/250000000000 : ℝ) (73558758431/125000000000 : ℝ) (52580315781/125000000000 : ℝ) (26290157891/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 1 (147117516861/250000000000 : ℝ) (73558758431/125000000000 : ℝ) (52580315781/125000000000 : ℝ) (26290157891/62500000000 : ℝ) (252278148423/500000000000 : ℝ) (126139074213/250000000000 : ℝ) (99505886417/200000000000 : ℝ) (124382358023/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 2 (252278148423/500000000000 : ℝ) (126139074213/250000000000 : ℝ) (99505886417/200000000000 : ℝ) (124382358023/250000000000 : ℝ) (100208572893/200000000000 : ℝ) (62630358059/125000000000 : ℝ) (2505152729/5000000000 : ℝ) (501030545807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 3 (100208572893/200000000000 : ℝ) (62630358059/125000000000 : ℝ) (2505152729/5000000000 : ℝ) (501030545807/1000000000000 : ℝ) (125259176283/250000000000 : ℝ) (25051835257/50000000000 : ℝ) (250518352547/500000000000 : ℝ) (250518352551/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 4 (125259176283/250000000000 : ℝ) (25051835257/50000000000 : ℝ) (250518352547/500000000000 : ℝ) (250518352551/500000000000 : ℝ) (501036705113/1000000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 5 (501036705113/1000000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 6 (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66707/524288 : ℝ))) 7 (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66707/524288 : ℝ)) hmem 8 (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66707/524288 : ℝ))) hcmem 8 (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66707/524288 : ℝ)) (248023780983/250000000000 : ℝ) (198419024787/200000000000 : ℝ) (62629588139/125000000000 : ℝ) (501036705121/1000000000000 : ℝ) (793297534673/1000000000000 : ℝ) (793297534691/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0634_exp_lower
  have heNumeric : (2054902546773/1000000000000 : ℝ)/4 ≤ Real.exp (-42628219954599/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902546773/1000000000000 : ℝ)/4 ≤ Real.exp ((33353/262144 : ℝ)-(793297534691/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33353/262144 : ℝ) (66707/524288 : ℝ) (793297534691/1000000000000 : ℝ) (2054902546773/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0635; no trusted numerical premise.
theorem cover8_leaf0635_exp_radius : (499006960773617531/500000000000000000 : ℝ) ≤ Real.exp ((-16677/1048576 : ℝ)/8) ∧ Real.exp ((-16677/1048576 : ℝ)/8) ≤ (998013921547235063/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16677/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0635_exp_lower : (230028375997744759/250000000000000000 : ℝ) ≤ Real.exp ((-17051288093849/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051288093849/25600000000000 : ℝ)/8) ≤ (920113503990979037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051288093849/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0635_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451268891/500000000000 : ℝ) ≤ 4*Real.exp (66707/524288 : ℝ)*Real.exp (-mu (radius 8 (16677/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451268891/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16677/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0635_exp_radius
  have hrNumeric : (123027672621/125000000000 : ℝ) ≤ Real.exp (-16677/1048576 : ℝ) ∧ Real.exp (-16677/1048576 : ℝ) ≤ (984221380969/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123027672621/125000000000 : ℝ) ≤ (radius 8 (16677/131072 : ℝ)) ∧ (radius 8 (16677/131072 : ℝ)) ≤ (984221380969/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16677/131072 : ℝ)) (123027672621/125000000000 : ℝ) (984221380969/1000000000000 : ℝ) (176941440153/1000000000000 : ℝ) (176941440159/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16677/131072 : ℝ)) (123027672621/125000000000 : ℝ) (984221380969/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123027672621/125000000000 : ℝ) (984221380969/1000000000000 : ℝ) (248027672621/250000000000 : ℝ) (198422138097/200000000000 : ℝ) (992079321913/1000000000000 : ℝ) (496039660957/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 1 (248027672621/250000000000 : ℝ) (198422138097/200000000000 : ℝ) (992079321913/1000000000000 : ℝ) (496039660957/500000000000 : ℝ) (496047503099/500000000000 : ℝ) (4960475031/5000000000 : ℝ) (496047503037/500000000000 : ℝ) (248023751519/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 2 (496047503099/500000000000 : ℝ) (4960475031/5000000000 : ℝ) (496047503037/500000000000 : ℝ) (248023751519/250000000000 : ℝ) (124011875767/125000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 3 (124011875767/125000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 4 (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 5 (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 6 (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16677/131072 : ℝ)) 7 (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16677/131072 : ℝ))) (176941440153/1000000000000 : ℝ) (176941440159/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176941440153/1000000000000 : ℝ) (176941440159/1000000000000 : ℝ) (147117680019/250000000000 : ℝ) (7355884001/12500000000 : ℝ) (210322038879/500000000000 : ℝ) (210322038883/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 1 (147117680019/250000000000 : ℝ) (7355884001/12500000000 : ℝ) (210322038879/500000000000 : ℝ) (210322038883/500000000000 : ℝ) (504557398917/1000000000000 : ℝ) (504557398923/1000000000000 : ℝ) (497530625523/1000000000000 : ℝ) (497530625531/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 2 (504557398917/1000000000000 : ℝ) (504557398923/1000000000000 : ℝ) (497530625523/1000000000000 : ℝ) (497530625531/1000000000000 : ℝ) (25052200611/50000000000 : ℝ) (501044012227/1000000000000 : ℝ) (501031693903/1000000000000 : ℝ) (501031693911/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 3 (25052200611/50000000000 : ℝ) (501044012227/1000000000000 : ℝ) (501031693903/1000000000000 : ℝ) (501031693911/1000000000000 : ℝ) (501037853061/1000000000000 : ℝ) (501037853069/1000000000000 : ℝ) (501037853023/1000000000000 : ℝ) (62629731629/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 4 (501037853061/1000000000000 : ℝ) (501037853069/1000000000000 : ℝ) (501037853023/1000000000000 : ℝ) (62629731629/125000000000 : ℝ) (250518926521/500000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 5 (250518926521/500000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 6 (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16677/131072 : ℝ))) 7 (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16677/131072 : ℝ)) hmem 8 (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16677/131072 : ℝ))) hcmem 8 (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16677/131072 : ℝ)) (198419001227/200000000000 : ℝ) (496047503069/500000000000 : ℝ) (501037853041/1000000000000 : ℝ) (501037853051/1000000000000 : ℝ) (198324861599/250000000000 : ℝ) (158659889283/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0635_exp_lower
  have heNumeric : (1027451268891/500000000000 : ℝ)/4 ≤ Real.exp (-17051288093849/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451268891/500000000000 : ℝ)/4 ≤ Real.exp ((66707/524288 : ℝ)-(158659889283/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66707/524288 : ℝ) (16677/131072 : ℝ) (158659889283/200000000000 : ℝ) (1027451268891/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0636; no trusted numerical premise.
theorem cover8_leaf0636_exp_radius : (249503472951025717/250000000000000000 : ℝ) ≤ Real.exp ((-66709/4194304 : ℝ)/8) ∧ Real.exp ((-66709/4194304 : ℝ)/8) ≤ (998013891804102869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66709/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0636_exp_lower : (920113503490970129/1000000000000000000 : ℝ) ≤ Real.exp ((-21314110256427/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314110256427/32000000000000 : ℝ)/8) ≤ (92011350349097013/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314110256427/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0636_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902528849/1000000000000 : ℝ) ≤ 4*Real.exp (16677/131072 : ℝ)*Real.exp (-mu (radius 8 (66709/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902528849/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66709/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0636_exp_radius
  have hrNumeric : (123027643289/125000000000 : ℝ) ≤ Real.exp (-66709/4194304 : ℝ) ∧ Real.exp (-66709/4194304 : ℝ) ≤ (984221146313/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123027643289/125000000000 : ℝ) ≤ (radius 8 (66709/524288 : ℝ)) ∧ (radius 8 (66709/524288 : ℝ)) ≤ (984221146313/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66709/524288 : ℝ)) (123027643289/125000000000 : ℝ) (984221146313/1000000000000 : ℝ) (176942745401/1000000000000 : ℝ) (2764730397/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66709/524288 : ℝ)) (123027643289/125000000000 : ℝ) (984221146313/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123027643289/125000000000 : ℝ) (984221146313/1000000000000 : ℝ) (248027643289/250000000000 : ℝ) (992110573157/1000000000000 : ℝ) (15501237557/15625000000 : ℝ) (19841584073/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 1 (248027643289/250000000000 : ℝ) (992110573157/1000000000000 : ℝ) (15501237557/15625000000 : ℝ) (19841584073/20000000000 : ℝ) (496047444201/500000000000 : ℝ) (248023722101/250000000000 : ℝ) (496047444139/500000000000 : ℝ) (24802372207/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 2 (496047444201/500000000000 : ℝ) (248023722101/250000000000 : ℝ) (496047444139/500000000000 : ℝ) (24802372207/25000000000 : ℝ) (49604744417/50000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 3 (49604744417/50000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 4 (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 5 (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 6 (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66709/524288 : ℝ)) 7 (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66709/524288 : ℝ))) (176942745401/1000000000000 : ℝ) (2764730397/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176942745401/1000000000000 : ℝ) (2764730397/15625000000 : ℝ) (5884713727/10000000000 : ℝ) (18389730397/31250000000 : ℝ) (210322814621/500000000000 : ℝ) (105161407313/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 1 (5884713727/10000000000 : ℝ) (18389730397/31250000000 : ℝ) (210322814621/500000000000 : ℝ) (105161407313/250000000000 : ℝ) (504558500971/1000000000000 : ℝ) (252279250489/500000000000 : ℝ) (248765909471/500000000000 : ℝ) (497531818951/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 2 (504558500971/1000000000000 : ℝ) (252279250489/500000000000 : ℝ) (248765909471/500000000000 : ℝ) (497531818951/1000000000000 : ℝ) (125261289989/250000000000 : ℝ) (100209031993/200000000000 : ℝ) (125258210497/250000000000 : ℝ) (501032841997/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 3 (125261289989/250000000000 : ℝ) (100209031993/200000000000 : ℝ) (125258210497/250000000000 : ℝ) (501032841997/1000000000000 : ℝ) (125259750243/250000000000 : ℝ) (501039000981/1000000000000 : ℝ) (250519500467/500000000000 : ℝ) (31314937559/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 4 (125259750243/250000000000 : ℝ) (501039000981/1000000000000 : ℝ) (250519500467/500000000000 : ℝ) (31314937559/62500000000 : ℝ) (501039000953/1000000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 5 (501039000953/1000000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 6 (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66709/524288 : ℝ))) 7 (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66709/524288 : ℝ)) hmem 8 (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66709/524288 : ℝ))) hcmem 8 (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66709/524288 : ℝ)) (992094888339/1000000000000 : ℝ) (496047444171/500000000000 : ℝ) (62629875119/125000000000 : ℝ) (501039000963/1000000000000 : ℝ) (79330135809/100000000000 : ℝ) (793301358111/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0636_exp_lower
  have heNumeric : (2054902528849/1000000000000 : ℝ)/4 ≤ Real.exp (-21314110256427/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902528849/1000000000000 : ℝ)/4 ≤ Real.exp ((16677/131072 : ℝ)-(793301358111/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16677/131072 : ℝ) (66709/524288 : ℝ) (793301358111/1000000000000 : ℝ) (2054902528849/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0637; no trusted numerical premise.
theorem cover8_leaf0637_exp_radius : (24950346551524289/25000000000000000 : ℝ) ≤ Real.exp ((-33355/2097152 : ℝ)/8) ∧ Real.exp ((-33355/2097152 : ℝ)/8) ≤ (998013862060971561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33355/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0637_exp_lower : (920113502992571421/1000000000000000000 : ℝ) ≤ Real.exp ((-85256441580379/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256441580379/128000000000000 : ℝ)/8) ≤ (460056751496285711/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256441580379/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0637_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862814993/125000000000 : ℝ) ≤ 4*Real.exp (66709/524288 : ℝ)*Real.exp (-mu (radius 8 (33355/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862814993/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33355/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0637_exp_radius
  have hrNumeric : (196844182331/200000000000 : ℝ) ≤ Real.exp (-33355/2097152 : ℝ) ∧ Real.exp (-33355/2097152 : ℝ) ≤ (123027613957/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196844182331/200000000000 : ℝ) ≤ (radius 8 (33355/262144 : ℝ)) ∧ (radius 8 (33355/262144 : ℝ)) ≤ (123027613957/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33355/262144 : ℝ)) (196844182331/200000000000 : ℝ) (123027613957/125000000000 : ℝ) (88472025323/500000000000 : ℝ) (44236012663/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33355/262144 : ℝ)) (196844182331/200000000000 : ℝ) (123027613957/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196844182331/200000000000 : ℝ) (123027613957/125000000000 : ℝ) (992110455827/1000000000000 : ℝ) (248027613957/250000000000 : ℝ) (992079085383/1000000000000 : ℝ) (124009885673/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 1 (992110455827/1000000000000 : ℝ) (248027613957/250000000000 : ℝ) (992079085383/1000000000000 : ℝ) (124009885673/125000000000 : ℝ) (198418954121/200000000000 : ℝ) (496047385303/500000000000 : ℝ) (992094770481/1000000000000 : ℝ) (992094770483/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 2 (198418954121/200000000000 : ℝ) (496047385303/500000000000 : ℝ) (992094770481/1000000000000 : ℝ) (992094770483/1000000000000 : ℝ) (992094770543/1000000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 3 (992094770543/1000000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 4 (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 5 (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 6 (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33355/262144 : ℝ)) 7 (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33355/262144 : ℝ))) (88472025323/500000000000 : ℝ) (44236012663/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88472025323/500000000000 : ℝ) (44236012663/250000000000 : ℝ) (588472025323/1000000000000 : ℝ) (294236012663/500000000000 : ℝ) (420647180717/1000000000000 : ℝ) (210323590363/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 1 (588472025323/1000000000000 : ℝ) (294236012663/500000000000 : ℝ) (420647180717/1000000000000 : ℝ) (210323590363/500000000000 : ℝ) (25227980151/50000000000 : ℝ) (252279801513/500000000000 : ℝ) (248766506177/500000000000 : ℝ) (248766506181/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 2 (25227980151/50000000000 : ℝ) (252279801513/500000000000 : ℝ) (248766506177/500000000000 : ℝ) (248766506181/500000000000 : ℝ) (501046307687/1000000000000 : ℝ) (250523153847/500000000000 : ℝ) (501033990067/1000000000000 : ℝ) (20041359603/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 3 (501046307687/1000000000000 : ℝ) (250523153847/500000000000 : ℝ) (501033990067/1000000000000 : ℝ) (20041359603/40000000000 : ℝ) (501040148877/1000000000000 : ℝ) (100208029777/200000000000 : ℝ) (501040148839/1000000000000 : ℝ) (501040148847/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 4 (501040148877/1000000000000 : ℝ) (100208029777/200000000000 : ℝ) (501040148839/1000000000000 : ℝ) (501040148847/1000000000000 : ℝ) (250520074429/500000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 5 (250520074429/500000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 6 (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33355/262144 : ℝ))) 7 (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33355/262144 : ℝ)) hmem 8 (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33355/262144 : ℝ))) hcmem 8 (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33355/262144 : ℝ)) (496047385271/500000000000 : ℝ) (198418954109/200000000000 : ℝ) (501040148857/1000000000000 : ℝ) (250520074433/500000000000 : ℝ) (49581454361/62500000000 : ℝ) (793303269793/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0637_exp_lower
  have heNumeric : (256862814993/125000000000 : ℝ)/4 ≤ Real.exp (-85256441580379/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862814993/125000000000 : ℝ)/4 ≤ Real.exp ((66709/524288 : ℝ)-(793303269793/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66709/524288 : ℝ) (33355/262144 : ℝ) (793303269793/1000000000000 : ℝ) (256862814993/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0638; no trusted numerical premise.
theorem cover8_leaf0638_exp_radius : (998013832317841139/1000000000000000000 : ℝ) ≤ Real.exp ((-66711/4194304 : ℝ)/8) ∧ Real.exp ((-66711/4194304 : ℝ)/8) ≤ (49900691615892057/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66711/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0638_exp_lower : (460056751248466527/500000000000000000 : ℝ) ≤ Real.exp ((-42628221065989/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628221065989/64000000000000 : ℝ)/8) ≤ (184022700499386611/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628221065989/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0638_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902511089/1000000000000 : ℝ) ≤ 4*Real.exp (33355/262144 : ℝ)*Real.exp (-mu (radius 8 (66711/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902511089/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66711/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0638_exp_radius
  have hrNumeric : (984220676999/1000000000000 : ℝ) ≤ Real.exp (-66711/4194304 : ℝ) ∧ Real.exp (-66711/4194304 : ℝ) ≤ (984220677/1000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984220676999/1000000000000 : ℝ) ≤ (radius 8 (66711/524288 : ℝ)) ∧ (radius 8 (66711/524288 : ℝ)) ≤ (984220677/1000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66711/524288 : ℝ)) (984220676999/1000000000000 : ℝ) (984220677/1000000000 : ℝ) (88472677937/500000000000 : ℝ) (176945355881/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66711/524288 : ℝ)) (984220676999/1000000000000 : ℝ) (984220677/1000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984220676999/1000000000000 : ℝ) (984220677/1000000000 : ℝ) (992110338499/1000000000000 : ℝ) (1984220677/2000000000 : ℝ) (496039483559/500000000000 : ℝ) (12400987089/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 1 (992110338499/1000000000000 : ℝ) (1984220677/2000000000 : ℝ) (496039483559/500000000000 : ℝ) (12400987089/12500000000 : ℝ) (124011831601/125000000000 : ℝ) (99209465281/100000000000 : ℝ) (248023663171/250000000000 : ℝ) (496047326343/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 2 (124011831601/125000000000 : ℝ) (99209465281/100000000000 : ℝ) (248023663171/250000000000 : ℝ) (496047326343/500000000000 : ℝ) (496047326373/500000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 3 (496047326373/500000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 4 (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 5 (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 6 (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66711/524288 : ℝ)) 7 (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66711/524288 : ℝ))) (88472677937/500000000000 : ℝ) (176945355881/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88472677937/500000000000 : ℝ) (176945355881/1000000000000 : ℝ) (588472677937/1000000000000 : ℝ) (588472677941/1000000000000 : ℝ) (420648732167/1000000000000 : ℝ) (26290545761/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 1 (588472677937/1000000000000 : ℝ) (588472677941/1000000000000 : ℝ) (420648732167/1000000000000 : ℝ) (26290545761/62500000000 : ℝ) (126140176263/250000000000 : ℝ) (504560705059/1000000000000 : ℝ) (497534205747/1000000000000 : ℝ) (99506841151/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 2 (126140176263/250000000000 : ℝ) (504560705059/1000000000000 : ℝ) (497534205747/1000000000000 : ℝ) (99506841151/200000000000 : ℝ) (501047455399/1000000000000 : ℝ) (501047455407/1000000000000 : ℝ) (31314696133/62500000000 : ℝ) (62629392267/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 3 (501047455399/1000000000000 : ℝ) (501047455407/1000000000000 : ℝ) (31314696133/62500000000 : ℝ) (62629392267/125000000000 : ℝ) (501041296763/1000000000000 : ℝ) (125260324193/250000000000 : ℝ) (20041651869/40000000000 : ℝ) (250520648367/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 4 (501041296763/1000000000000 : ℝ) (125260324193/250000000000 : ℝ) (20041651869/40000000000 : ℝ) (250520648367/500000000000 : ℝ) (62630162093/125000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 5 (62630162093/125000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 6 (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66711/524288 : ℝ))) 7 (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66711/524288 : ℝ)) hmem 8 (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66711/524288 : ℝ))) hcmem 8 (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66711/524288 : ℝ)) (198418930549/200000000000 : ℝ) (248023663187/250000000000 : ℝ) (501041296743/1000000000000 : ℝ) (501041296753/1000000000000 : ℝ) (99163147679/125000000000 : ℝ) (793305181451/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0638_exp_lower
  have heNumeric : (2054902511089/1000000000000 : ℝ)/4 ≤ Real.exp (-42628221065989/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902511089/1000000000000 : ℝ)/4 ≤ Real.exp ((33355/262144 : ℝ)-(793305181451/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33355/262144 : ℝ) (66711/524288 : ℝ) (793305181451/1000000000000 : ℝ) (2054902511089/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0639; no trusted numerical premise.
theorem cover8_leaf0639_exp_radius : (249503450643677901/250000000000000000 : ℝ) ≤ Real.exp ((-8339/524288 : ℝ)/8) ∧ Real.exp ((-8339/524288 : ℝ)/8) ≤ (199602760514942321/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8339/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0639_exp_lower : (920113502002559843/1000000000000000000 : ℝ) ≤ Real.exp ((-85256442682169/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256442682169/128000000000000 : ℝ)/8) ≤ (230028375500639961/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256442682169/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0639_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431406391/62500000000 : ℝ) ≤ 4*Real.exp (66711/524288 : ℝ)*Real.exp (-mu (radius 8 (8339/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128431406391/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8339/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0639_exp_radius
  have hrNumeric : (492110221171/500000000000 : ℝ) ≤ Real.exp (-8339/524288 : ℝ) ∧ Real.exp (-8339/524288 : ℝ) ≤ (984220442343/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492110221171/500000000000 : ℝ) ≤ (radius 8 (8339/65536 : ℝ)) ∧ (radius 8 (8339/65536 : ℝ)) ≤ (984220442343/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8339/65536 : ℝ)) (492110221171/500000000000 : ℝ) (984220442343/1000000000000 : ℝ) (176946661099/1000000000000 : ℝ) (35389332221/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8339/65536 : ℝ)) (492110221171/500000000000 : ℝ) (984220442343/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492110221171/500000000000 : ℝ) (984220442343/1000000000000 : ℝ) (992110221171/1000000000000 : ℝ) (248027555293/250000000000 : ℝ) (992078848853/1000000000000 : ℝ) (496039424427/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 1 (992110221171/1000000000000 : ℝ) (248027555293/250000000000 : ℝ) (992078848853/1000000000000 : ℝ) (496039424427/500000000000 : ℝ) (248023633753/250000000000 : ℝ) (992094535013/1000000000000 : ℝ) (992094534887/1000000000000 : ℝ) (992094534889/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 2 (248023633753/250000000000 : ℝ) (992094535013/1000000000000 : ℝ) (992094534887/1000000000000 : ℝ) (992094534889/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 3 (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 4 (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 5 (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 6 (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8339/65536 : ℝ)) 7 (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8339/65536 : ℝ))) (176946661099/1000000000000 : ℝ) (35389332221/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176946661099/1000000000000 : ℝ) (35389332221/200000000000 : ℝ) (588473330549/1000000000000 : ℝ) (588473330553/1000000000000 : ℝ) (420650283607/1000000000000 : ℝ) (84130056723/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 1 (588473330549/1000000000000 : ℝ) (588473330553/1000000000000 : ℝ) (420650283607/1000000000000 : ℝ) (84130056723/200000000000 : ℝ) (252280903539/500000000000 : ℝ) (126140451771/250000000000 : ℝ) (497535399133/1000000000000 : ℝ) (24876769957/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 2 (252280903539/500000000000 : ℝ) (126140451771/250000000000 : ℝ) (497535399133/1000000000000 : ℝ) (24876769957/50000000000 : ℝ) (100209720621/200000000000 : ℝ) (62631075389/125000000000 : ℝ) (250518143091/500000000000 : ℝ) (50103628619/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 3 (100209720621/200000000000 : ℝ) (62631075389/125000000000 : ℝ) (250518143091/500000000000 : ℝ) (50103628619/100000000000 : ℝ) (501042444643/1000000000000 : ℝ) (501042444651/1000000000000 : ℝ) (100208488921/200000000000 : ℝ) (250521222307/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 4 (501042444643/1000000000000 : ℝ) (501042444651/1000000000000 : ℝ) (100208488921/200000000000 : ℝ) (250521222307/500000000000 : ℝ) (31315152789/62500000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 5 (31315152789/62500000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 6 (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8339/65536 : ℝ))) 7 (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8339/65536 : ℝ)) hmem 8 (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8339/65536 : ℝ))) hcmem 8 (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8339/65536 : ℝ)) (992094534949/1000000000000 : ℝ) (992094534951/1000000000000 : ℝ) (501042444623/1000000000000 : ℝ) (501042444633/1000000000000 : ℝ) (793307093079/1000000000000 : ℝ) (396653546549/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0639_exp_lower
  have heNumeric : (128431406391/62500000000 : ℝ)/4 ≤ Real.exp (-85256442682169/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431406391/62500000000 : ℝ)/4 ≤ Real.exp ((66711/524288 : ℝ)-(396653546549/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66711/524288 : ℝ) (8339/65536 : ℝ) (396653546549/500000000000 : ℝ) (128431406391/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0640; no trusted numerical premise.
theorem cover8_leaf0640_exp_radius : (249503443207895739/250000000000000000 : ℝ) ≤ Real.exp ((-66713/4194304 : ℝ)/8) ∧ Real.exp ((-66713/4194304 : ℝ)/8) ≤ (998013772831582957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66713/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0640_exp_lower : (92011350151140703/100000000000000000 : ℝ) ≤ Real.exp ((-10657055403597/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657055403597/16000000000000 : ℝ)/8) ≤ (920113501511407031/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657055403597/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0640_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902493481/1000000000000 : ℝ) ≤ 4*Real.exp (8339/65536 : ℝ)*Real.exp (-mu (radius 8 (66713/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902493481/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66713/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0640_exp_radius
  have hrNumeric : (492110103843/500000000000 : ℝ) ≤ Real.exp (-66713/4194304 : ℝ) ∧ Real.exp (-66713/4194304 : ℝ) ≤ (984220207687/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492110103843/500000000000 : ℝ) ≤ (radius 8 (66713/524288 : ℝ)) ∧ (radius 8 (66713/524288 : ℝ)) ≤ (984220207687/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66713/524288 : ℝ)) (492110103843/500000000000 : ℝ) (984220207687/1000000000000 : ℝ) (44236991577/250000000000 : ℝ) (88473983157/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66713/524288 : ℝ)) (492110103843/500000000000 : ℝ) (984220207687/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492110103843/500000000000 : ℝ) (984220207687/1000000000000 : ℝ) (992110103843/1000000000000 : ℝ) (248027525961/250000000000 : ℝ) (248019682647/250000000000 : ℝ) (992078730589/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 1 (992110103843/1000000000000 : ℝ) (248027525961/250000000000 : ℝ) (248019682647/250000000000 : ℝ) (992078730589/1000000000000 : ℝ) (198418883443/200000000000 : ℝ) (992094417217/1000000000000 : ℝ) (992094417091/1000000000000 : ℝ) (992094417093/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 2 (198418883443/200000000000 : ℝ) (992094417217/1000000000000 : ℝ) (992094417091/1000000000000 : ℝ) (992094417093/1000000000000 : ℝ) (992094417153/1000000000000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 3 (992094417153/1000000000000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 4 (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 5 (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 6 (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66713/524288 : ℝ)) 7 (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66713/524288 : ℝ))) (44236991577/250000000000 : ℝ) (88473983157/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44236991577/250000000000 : ℝ) (88473983157/500000000000 : ℝ) (294236991577/500000000000 : ℝ) (588473983157/1000000000000 : ℝ) (210325917511/500000000000 : ℝ) (42065183503/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 1 (294236991577/500000000000 : ℝ) (588473983157/1000000000000 : ℝ) (210325917511/500000000000 : ℝ) (42065183503/100000000000 : ℝ) (15767590909/31250000000 : ℝ) (252281454547/500000000000 : ℝ) (497536592499/1000000000000 : ℝ) (248768296253/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 2 (15767590909/31250000000 : ℝ) (252281454547/500000000000 : ℝ) (497536592499/1000000000000 : ℝ) (248768296253/500000000000 : ℝ) (501049750793/1000000000000 : ℝ) (1252624377/2500000000 : ℝ) (501037434219/1000000000000 : ℝ) (250518717113/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 3 (501049750793/1000000000000 : ℝ) (1252624377/2500000000 : ℝ) (501037434219/1000000000000 : ℝ) (250518717113/500000000000 : ℝ) (250521796253/500000000000 : ℝ) (501043592513/1000000000000 : ℝ) (125260898117/250000000000 : ℝ) (125260898119/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 4 (250521796253/500000000000 : ℝ) (501043592513/1000000000000 : ℝ) (125260898117/250000000000 : ℝ) (125260898119/250000000000 : ℝ) (501043592487/1000000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 5 (501043592487/1000000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 6 (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66713/524288 : ℝ))) 7 (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66713/524288 : ℝ)) hmem 8 (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66713/524288 : ℝ))) hcmem 8 (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66713/524288 : ℝ)) (3875368817/3906250000 : ℝ) (198418883431/200000000000 : ℝ) (250521796243/500000000000 : ℝ) (100208718499/200000000000 : ℝ) (793309004699/1000000000000 : ℝ) (793309004717/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0640_exp_lower
  have heNumeric : (2054902493481/1000000000000 : ℝ)/4 ≤ Real.exp (-10657055403597/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902493481/1000000000000 : ℝ)/4 ≤ Real.exp ((8339/65536 : ℝ)-(793309004717/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8339/65536 : ℝ) (66713/524288 : ℝ) (793309004717/1000000000000 : ℝ) (2054902493481/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0641; no trusted numerical premise.
theorem cover8_leaf0641_exp_radius : (998013743088455193/1000000000000000000 : ℝ) ≤ Real.exp ((-33357/2097152 : ℝ)/8) ∧ Real.exp ((-33357/2097152 : ℝ)/8) ≤ (499006871544227597/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33357/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0641_exp_lower : (115014187627790559/125000000000000000 : ℝ) ≤ Real.exp ((-85256443773079/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256443773079/128000000000000 : ℝ)/8) ≤ (920113501022324473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256443773079/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0641_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902484743/1000000000000 : ℝ) ≤ 4*Real.exp (66713/524288 : ℝ)*Real.exp (-mu (radius 8 (33357/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902484743/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33357/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0641_exp_radius
  have hrNumeric : (98421997303/100000000000 : ℝ) ≤ Real.exp (-33357/2097152 : ℝ) ∧ Real.exp (-33357/2097152 : ℝ) ≤ (984219973031/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98421997303/100000000000 : ℝ) ≤ (radius 8 (33357/262144 : ℝ)) ∧ (radius 8 (33357/262144 : ℝ)) ≤ (984219973031/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33357/262144 : ℝ)) (98421997303/100000000000 : ℝ) (984219973031/1000000000000 : ℝ) (88474635753/500000000000 : ℝ) (176949271513/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33357/262144 : ℝ)) (98421997303/100000000000 : ℝ) (984219973031/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98421997303/100000000000 : ℝ) (984219973031/1000000000000 : ℝ) (198421997303/200000000000 : ℝ) (248027496629/250000000000 : ℝ) (992078612323/1000000000000 : ℝ) (39683144493/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 1 (198421997303/200000000000 : ℝ) (248027496629/250000000000 : ℝ) (992078612323/1000000000000 : ℝ) (39683144493/40000000000 : ℝ) (992094299419/1000000000000 : ℝ) (992094299421/1000000000000 : ℝ) (496047149647/500000000000 : ℝ) (992094299297/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 2 (992094299419/1000000000000 : ℝ) (992094299421/1000000000000 : ℝ) (496047149647/500000000000 : ℝ) (992094299297/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 3 (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 4 (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 5 (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 6 (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33357/262144 : ℝ)) 7 (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33357/262144 : ℝ))) (88474635753/500000000000 : ℝ) (176949271513/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88474635753/500000000000 : ℝ) (176949271513/1000000000000 : ℝ) (588474635753/1000000000000 : ℝ) (588474635757/1000000000000 : ℝ) (420653386419/1000000000000 : ℝ) (105163346607/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 1 (588474635753/1000000000000 : ℝ) (588474635757/1000000000000 : ℝ) (420653386419/1000000000000 : ℝ) (105163346607/250000000000 : ℝ) (252282005543/500000000000 : ℝ) (504564011093/1000000000000 : ℝ) (124384446463/250000000000 : ℝ) (24876889293/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 2 (252282005543/500000000000 : ℝ) (504564011093/1000000000000 : ℝ) (124384446463/250000000000 : ℝ) (24876889293/50000000000 : ℝ) (501050898469/1000000000000 : ℝ) (501050898477/1000000000000 : ℝ) (501038582243/1000000000000 : ℝ) (501038582251/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 3 (501050898469/1000000000000 : ℝ) (501050898477/1000000000000 : ℝ) (501038582243/1000000000000 : ℝ) (501038582251/1000000000000 : ℝ) (125261185089/250000000000 : ℝ) (125261185091/250000000000 : ℝ) (250522370159/500000000000 : ℝ) (501044740327/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 4 (125261185089/250000000000 : ℝ) (125261185091/250000000000 : ℝ) (250522370159/500000000000 : ℝ) (501044740327/1000000000000 : ℝ) (501044740337/1000000000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 5 (501044740337/1000000000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 6 (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33357/262144 : ℝ))) 7 (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33357/262144 : ℝ)) hmem 8 (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33357/262144 : ℝ))) hcmem 8 (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33357/262144 : ℝ)) (248023574839/250000000000 : ℝ) (992094299359/1000000000000 : ℝ) (31315296271/62500000000 : ℝ) (250522370173/500000000000 : ℝ) (793310916299/1000000000000 : ℝ) (396655458159/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0641_exp_lower
  have heNumeric : (2054902484743/1000000000000 : ℝ)/4 ≤ Real.exp (-85256443773079/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902484743/1000000000000 : ℝ)/4 ≤ Real.exp ((66713/524288 : ℝ)-(396655458159/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66713/524288 : ℝ) (33357/262144 : ℝ) (396655458159/500000000000 : ℝ) (2054902484743/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0642; no trusted numerical premise.
theorem cover8_leaf0642_exp_radius : (499006856672664159/500000000000000000 : ℝ) ≤ Real.exp ((-66715/4194304 : ℝ)/8) ∧ Real.exp ((-66715/4194304 : ℝ)/8) ≤ (998013713345328319/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66715/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0642_exp_lower : (920113500534737099/1000000000000000000 : ℝ) ≤ Real.exp ((-42628222157859/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628222157859/64000000000000 : ℝ)/8) ≤ (9201135005347371/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628222157859/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0642_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902476031/1000000000000 : ℝ) ≤ 4*Real.exp (33357/262144 : ℝ)*Real.exp (-mu (radius 8 (66715/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902476031/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66715/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0642_exp_radius
  have hrNumeric : (984219738373/1000000000000 : ℝ) ≤ Real.exp (-66715/4194304 : ℝ) ∧ Real.exp (-66715/4194304 : ℝ) ≤ (492109869187/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984219738373/1000000000000 : ℝ) ≤ (radius 8 (66715/524288 : ℝ)) ∧ (radius 8 (66715/524288 : ℝ)) ≤ (492109869187/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66715/524288 : ℝ)) (984219738373/1000000000000 : ℝ) (492109869187/500000000000 : ℝ) (176950576701/1000000000000 : ℝ) (44237644177/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66715/524288 : ℝ)) (984219738373/1000000000000 : ℝ) (492109869187/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984219738373/1000000000000 : ℝ) (492109869187/500000000000 : ℝ) (496054934593/500000000000 : ℝ) (992109869187/1000000000000 : ℝ) (496039247029/500000000000 : ℝ) (992078494059/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 1 (496054934593/500000000000 : ℝ) (992109869187/1000000000000 : ℝ) (496039247029/500000000000 : ℝ) (992078494059/1000000000000 : ℝ) (496047090811/500000000000 : ℝ) (992094181623/1000000000000 : ℝ) (992094181497/1000000000000 : ℝ) (992094181499/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 2 (496047090811/500000000000 : ℝ) (992094181623/1000000000000 : ℝ) (992094181497/1000000000000 : ℝ) (992094181499/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 3 (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 4 (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 5 (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 6 (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66715/524288 : ℝ)) 7 (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66715/524288 : ℝ))) (176950576701/1000000000000 : ℝ) (44237644177/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176950576701/1000000000000 : ℝ) (44237644177/250000000000 : ℝ) (11769505767/20000000000 : ℝ) (294237644177/500000000000 : ℝ) (210327468903/500000000000 : ℝ) (84130987563/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 1 (11769505767/20000000000 : ℝ) (294237644177/500000000000 : ℝ) (210327468903/500000000000 : ℝ) (84130987563/200000000000 : ℝ) (252282556539/500000000000 : ℝ) (100913022617/200000000000 : ℝ) (497538979197/1000000000000 : ℝ) (99507795841/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 2 (252282556539/500000000000 : ℝ) (100913022617/200000000000 : ℝ) (497538979197/1000000000000 : ℝ) (99507795841/200000000000 : ℝ) (501052046137/1000000000000 : ℝ) (100210409229/200000000000 : ℝ) (25051986513/50000000000 : ℝ) (125259932567/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 3 (501052046137/1000000000000 : ℝ) (100210409229/200000000000 : ℝ) (25051986513/50000000000 : ℝ) (125259932567/250000000000 : ℝ) (250522944099/500000000000 : ℝ) (501045888207/1000000000000 : ℝ) (3131536801/6250000000 : ℝ) (501045888169/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 4 (250522944099/500000000000 : ℝ) (501045888207/1000000000000 : ℝ) (3131536801/6250000000 : ℝ) (501045888169/1000000000000 : ℝ) (501045888179/1000000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 5 (501045888179/1000000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 6 (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66715/524288 : ℝ))) 7 (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66715/524288 : ℝ)) hmem 8 (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66715/524288 : ℝ))) hcmem 8 (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66715/524288 : ℝ)) (992094181559/1000000000000 : ℝ) (992094181561/1000000000000 : ℝ) (250522944089/500000000000 : ℝ) (125261472047/250000000000 : ℝ) (49582051743/62500000000 : ℝ) (396656413953/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0642_exp_lower
  have heNumeric : (2054902476031/1000000000000 : ℝ)/4 ≤ Real.exp (-42628222157859/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902476031/1000000000000 : ℝ)/4 ≤ Real.exp ((33357/262144 : ℝ)-(396656413953/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33357/262144 : ℝ) (66715/524288 : ℝ) (396656413953/500000000000 : ℝ) (2054902476031/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0643; no trusted numerical premise.
theorem cover8_leaf0643_exp_radius : (998013683602202329/1000000000000000000 : ℝ) ≤ Real.exp ((-16679/1048576 : ℝ)/8) ∧ Real.exp ((-16679/1048576 : ℝ)/8) ≤ (99801368360220233/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16679/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0643_exp_lower : (920113500049795053/1000000000000000000 : ℝ) ≤ Real.exp ((-85256444855413/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256444855413/128000000000000 : ℝ)/8) ≤ (460056750024897527/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256444855413/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0643_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902467367/1000000000000 : ℝ) ≤ 4*Real.exp (66715/524288 : ℝ)*Real.exp (-mu (radius 8 (16679/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902467367/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16679/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0643_exp_radius
  have hrNumeric : (984219503717/1000000000000 : ℝ) ≤ Real.exp (-16679/1048576 : ℝ) ∧ Real.exp (-16679/1048576 : ℝ) ≤ (492109751859/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984219503717/1000000000000 : ℝ) ≤ (radius 8 (16679/131072 : ℝ)) ∧ (radius 8 (16679/131072 : ℝ)) ≤ (492109751859/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16679/131072 : ℝ)) (984219503717/1000000000000 : ℝ) (492109751859/500000000000 : ℝ) (4423797047/25000000000 : ℝ) (176951881887/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16679/131072 : ℝ)) (984219503717/1000000000000 : ℝ) (492109751859/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984219503717/1000000000000 : ℝ) (492109751859/500000000000 : ℝ) (496054875929/500000000000 : ℝ) (992109751859/1000000000000 : ℝ) (992078375793/1000000000000 : ℝ) (496039187897/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 1 (496054875929/500000000000 : ℝ) (992109751859/1000000000000 : ℝ) (992078375793/1000000000000 : ℝ) (496039187897/500000000000 : ℝ) (39683762553/40000000000 : ℝ) (992094063827/1000000000000 : ℝ) (992094063701/1000000000000 : ℝ) (992094063703/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 2 (39683762553/40000000000 : ℝ) (992094063827/1000000000000 : ℝ) (992094063701/1000000000000 : ℝ) (992094063703/1000000000000 : ℝ) (992094063763/1000000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 3 (992094063763/1000000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 4 (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 5 (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 6 (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16679/131072 : ℝ)) 7 (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16679/131072 : ℝ))) (4423797047/25000000000 : ℝ) (176951881887/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4423797047/25000000000 : ℝ) (176951881887/1000000000000 : ℝ) (29423797047/50000000000 : ℝ) (36779746309/62500000000 : ℝ) (420656489169/1000000000000 : ℝ) (210328244589/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 1 (29423797047/50000000000 : ℝ) (36779746309/62500000000 : ℝ) (420656489169/1000000000000 : ℝ) (210328244589/500000000000 : ℝ) (252283107527/500000000000 : ℝ) (504566215061/1000000000000 : ℝ) (19901606901/40000000000 : ℝ) (497540172533/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 2 (252283107527/500000000000 : ℝ) (504566215061/1000000000000 : ℝ) (19901606901/40000000000 : ℝ) (497540172533/1000000000000 : ℝ) (501053193789/1000000000000 : ℝ) (501053193797/1000000000000 : ℝ) (25052043913/50000000000 : ℝ) (501040878269/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 3 (501053193789/1000000000000 : ℝ) (501053193797/1000000000000 : ℝ) (25052043913/50000000000 : ℝ) (501040878269/1000000000000 : ℝ) (62630879503/125000000000 : ℝ) (501047036033/1000000000000 : ℝ) (250523517993/500000000000 : ℝ) (125261758999/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 4 (62630879503/125000000000 : ℝ) (501047036033/1000000000000 : ℝ) (250523517993/500000000000 : ℝ) (125261758999/250000000000 : ℝ) (100209407201/200000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 5 (100209407201/200000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 6 (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16679/131072 : ℝ))) 7 (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16679/131072 : ℝ)) hmem 8 (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16679/131072 : ℝ))) hcmem 8 (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16679/131072 : ℝ)) (496047031881/500000000000 : ℝ) (198418812753/200000000000 : ℝ) (125261759001/250000000000 : ℝ) (100209407203/200000000000 : ℝ) (15866294789/20000000000 : ℝ) (793314739471/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0643_exp_lower
  have heNumeric : (2054902467367/1000000000000 : ℝ)/4 ≤ Real.exp (-85256444855413/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902467367/1000000000000 : ℝ)/4 ≤ Real.exp ((66715/524288 : ℝ)-(793314739471/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66715/524288 : ℝ) (16679/131072 : ℝ) (793314739471/1000000000000 : ℝ) (2054902467367/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0644; no trusted numerical premise.
theorem cover8_leaf0644_exp_radius : (499006826929538613/500000000000000000 : ℝ) ≤ Real.exp ((-66717/4194304 : ℝ)/8) ∧ Real.exp ((-66717/4194304 : ℝ)/8) ≤ (998013653859077227/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66717/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0644_exp_lower : (920113499567383319/1000000000000000000 : ℝ) ≤ Real.exp ((-21314111348073/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314111348073/32000000000000 : ℝ)/8) ≤ (23002837489184583/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314111348073/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0644_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725614687/250000000000 : ℝ) ≤ 4*Real.exp (16679/131072 : ℝ)*Real.exp (-mu (radius 8 (66717/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725614687/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66717/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0644_exp_radius
  have hrNumeric : (984219269061/1000000000000 : ℝ) ≤ Real.exp (-66717/4194304 : ℝ) ∧ Real.exp (-66717/4194304 : ℝ) ≤ (492109634531/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984219269061/1000000000000 : ℝ) ≤ (radius 8 (66717/524288 : ℝ)) ∧ (radius 8 (66717/524288 : ℝ)) ≤ (492109634531/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66717/524288 : ℝ)) (984219269061/1000000000000 : ℝ) (492109634531/500000000000 : ℝ) (176953187049/1000000000000 : ℝ) (11059574191/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66717/524288 : ℝ)) (984219269061/1000000000000 : ℝ) (492109634531/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984219269061/1000000000000 : ℝ) (492109634531/500000000000 : ℝ) (99210963453/100000000000 : ℝ) (992109634531/1000000000000 : ℝ) (124009782191/125000000000 : ℝ) (99207825753/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 1 (99210963453/100000000000 : ℝ) (992109634531/1000000000000 : ℝ) (124009782191/125000000000 : ℝ) (99207825753/100000000000 : ℝ) (992093946029/1000000000000 : ℝ) (992093946031/1000000000000 : ℝ) (62005871619/62500000000 : ℝ) (992093945907/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 2 (992093946029/1000000000000 : ℝ) (992093946031/1000000000000 : ℝ) (62005871619/62500000000 : ℝ) (992093945907/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 3 (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 4 (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 5 (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 6 (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66717/524288 : ℝ)) 7 (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66717/524288 : ℝ))) (176953187049/1000000000000 : ℝ) (11059574191/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176953187049/1000000000000 : ℝ) (11059574191/62500000000 : ℝ) (147119148381/250000000000 : ℝ) (73559574191/125000000000 : ℝ) (420658040513/1000000000000 : ℝ) (420658040523/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 1 (147119148381/250000000000 : ℝ) (73559574191/125000000000 : ℝ) (420658040513/1000000000000 : ℝ) (420658040523/1000000000000 : ℝ) (252283658509/500000000000 : ℝ) (252283658513/500000000000 : ℝ) (497541365837/1000000000000 : ℝ) (248770682923/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 2 (252283658509/500000000000 : ℝ) (252283658513/500000000000 : ℝ) (497541365837/1000000000000 : ℝ) (248770682923/500000000000 : ℝ) (501054341427/1000000000000 : ℝ) (125263585359/250000000000 : ℝ) (501042026247/1000000000000 : ℝ) (31315126641/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 3 (501054341427/1000000000000 : ℝ) (125263585359/250000000000 : ℝ) (501042026247/1000000000000 : ℝ) (31315126641/62500000000 : ℝ) (501048183837/1000000000000 : ℝ) (250524091923/500000000000 : ℝ) (501048183799/1000000000000 : ℝ) (501048183809/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 4 (501048183837/1000000000000 : ℝ) (250524091923/500000000000 : ℝ) (501048183799/1000000000000 : ℝ) (501048183809/1000000000000 : ℝ) (250524091909/500000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 5 (250524091909/500000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 6 (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66717/524288 : ℝ))) 7 (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66717/524288 : ℝ)) hmem 8 (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66717/524288 : ℝ))) hcmem 8 (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66717/524288 : ℝ)) (496046972983/500000000000 : ℝ) (992093945969/1000000000000 : ℝ) (501048183817/1000000000000 : ℝ) (125262045957/250000000000 : ℝ) (793316650993/1000000000000 : ℝ) (396658325507/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0644_exp_lower
  have heNumeric : (513725614687/250000000000 : ℝ)/4 ≤ Real.exp (-21314111348073/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725614687/250000000000 : ℝ)/4 ≤ Real.exp ((16679/131072 : ℝ)-(396658325507/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16679/131072 : ℝ) (66717/524288 : ℝ) (396658325507/500000000000 : ℝ) (513725614687/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0645; no trusted numerical premise.
theorem cover8_leaf0645_exp_radius : (998013624115953009/1000000000000000000 : ℝ) ≤ Real.exp ((-33359/2097152 : ℝ)/8) ∧ Real.exp ((-33359/2097152 : ℝ)/8) ≤ (99801362411595301/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33359/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0645_exp_lower : (11501418738588023/12500000000000000 : ℝ) ≤ Real.exp ((-85256445926867/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256445926867/128000000000000 : ℝ)/8) ≤ (920113499087041841/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256445926867/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0645_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451225083/500000000000 : ℝ) ≤ 4*Real.exp (66717/524288 : ℝ)*Real.exp (-mu (radius 8 (33359/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451225083/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33359/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0645_exp_radius
  have hrNumeric : (196843806881/200000000000 : ℝ) ≤ Real.exp (-33359/2097152 : ℝ) ∧ Real.exp (-33359/2097152 : ℝ) ≤ (492109517203/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196843806881/200000000000 : ℝ) ≤ (radius 8 (33359/262144 : ℝ)) ∧ (radius 8 (33359/262144 : ℝ)) ≤ (492109517203/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33359/262144 : ℝ)) (196843806881/200000000000 : ℝ) (492109517203/500000000000 : ℝ) (11059655763/62500000000 : ℝ) (35390898443/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33359/262144 : ℝ)) (196843806881/200000000000 : ℝ) (492109517203/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196843806881/200000000000 : ℝ) (492109517203/500000000000 : ℝ) (496054758601/500000000000 : ℝ) (992109517203/1000000000000 : ℝ) (992078139263/1000000000000 : ℝ) (198415627853/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 1 (496054758601/500000000000 : ℝ) (992109517203/1000000000000 : ℝ) (992078139263/1000000000000 : ℝ) (198415627853/200000000000 : ℝ) (124011728529/125000000000 : ℝ) (496046914117/500000000000 : ℝ) (248023457027/250000000000 : ℝ) (99209382811/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 2 (124011728529/125000000000 : ℝ) (496046914117/500000000000 : ℝ) (248023457027/250000000000 : ℝ) (99209382811/100000000000 : ℝ) (99209382817/100000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 3 (99209382817/100000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 4 (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 5 (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 6 (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33359/262144 : ℝ)) 7 (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33359/262144 : ℝ))) (11059655763/62500000000 : ℝ) (35390898443/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11059655763/62500000000 : ℝ) (35390898443/200000000000 : ℝ) (73559655763/125000000000 : ℝ) (147119311527/250000000000 : ℝ) (420659591841/1000000000000 : ℝ) (8413191837/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 1 (73559655763/125000000000 : ℝ) (147119311527/250000000000 : ℝ) (420659591841/1000000000000 : ℝ) (8413191837/20000000000 : ℝ) (126142104743/250000000000 : ℝ) (504568418979/1000000000000 : ℝ) (248771279569/500000000000 : ℝ) (248771279573/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 2 (126142104743/250000000000 : ℝ) (504568418979/1000000000000 : ℝ) (248771279569/500000000000 : ℝ) (248771279573/500000000000 : ℝ) (100211097811/200000000000 : ℝ) (501055489063/1000000000000 : ℝ) (501043174223/1000000000000 : ℝ) (501043174231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 3 (100211097811/200000000000 : ℝ) (501055489063/1000000000000 : ℝ) (501043174223/1000000000000 : ℝ) (501043174231/1000000000000 : ℝ) (501049331639/1000000000000 : ℝ) (501049331647/1000000000000 : ℝ) (501049331601/1000000000000 : ℝ) (50104933161/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 4 (501049331639/1000000000000 : ℝ) (501049331647/1000000000000 : ℝ) (501049331601/1000000000000 : ℝ) (50104933161/100000000000 : ℝ) (25052466581/50000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 5 (25052466581/50000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 6 (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33359/262144 : ℝ))) 7 (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33359/262144 : ℝ)) hmem 8 (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33359/262144 : ℝ))) hcmem 8 (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33359/262144 : ℝ)) (992093828169/1000000000000 : ℝ) (248023457043/250000000000 : ℝ) (501049331619/1000000000000 : ℝ) (501049331629/1000000000000 : ℝ) (793318562519/1000000000000 : ℝ) (793318562539/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0645_exp_lower
  have heNumeric : (1027451225083/500000000000 : ℝ)/4 ≤ Real.exp (-85256445926867/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451225083/500000000000 : ℝ)/4 ≤ Real.exp ((66717/524288 : ℝ)-(793318562539/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66717/524288 : ℝ) (33359/262144 : ℝ) (793318562539/1000000000000 : ℝ) (1027451225083/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0646; no trusted numerical premise.
theorem cover8_leaf0646_exp_radius : (998013594372829679/1000000000000000000 : ℝ) ≤ Real.exp ((-66719/4194304 : ℝ)/8) ∧ Real.exp ((-66719/4194304 : ℝ)/8) ≤ (12475169929660371/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66719/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0646_exp_lower : (460056749304615337/500000000000000000 : ℝ) ≤ Real.exp ((-42628223229313/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628223229313/64000000000000 : ℝ)/8) ≤ (36804539944369227/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628223229313/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0646_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902441629/1000000000000 : ℝ) ≤ 4*Real.exp (33359/262144 : ℝ)*Real.exp (-mu (radius 8 (66719/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902441629/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66719/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0646_exp_radius
  have hrNumeric : (984218799749/1000000000000 : ℝ) ≤ Real.exp (-66719/4194304 : ℝ) ∧ Real.exp (-66719/4194304 : ℝ) ≤ (3936875199/4000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984218799749/1000000000000 : ℝ) ≤ (radius 8 (66719/524288 : ℝ)) ∧ (radius 8 (66719/524288 : ℝ)) ≤ (3936875199/4000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66719/524288 : ℝ)) (984218799749/1000000000000 : ℝ) (3936875199/4000000000 : ℝ) (88477898679/500000000000 : ℝ) (44238949341/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66719/524288 : ℝ)) (984218799749/1000000000000 : ℝ) (3936875199/4000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984218799749/1000000000000 : ℝ) (3936875199/4000000000 : ℝ) (496054699937/500000000000 : ℝ) (7936875199/8000000000 : ℝ) (496039010499/500000000000 : ℝ) (992078021/1000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 1 (496054699937/500000000000 : ℝ) (7936875199/8000000000 : ℝ) (496039010499/500000000000 : ℝ) (992078021/1000000000 : ℝ) (248023427609/250000000000 : ℝ) (496046855219/500000000000 : ℝ) (992093710311/1000000000000 : ℝ) (496046855157/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 2 (248023427609/250000000000 : ℝ) (496046855219/500000000000 : ℝ) (992093710311/1000000000000 : ℝ) (496046855157/500000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 3 (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 4 (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 5 (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 6 (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66719/524288 : ℝ)) 7 (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66719/524288 : ℝ))) (88477898679/500000000000 : ℝ) (44238949341/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88477898679/500000000000 : ℝ) (44238949341/250000000000 : ℝ) (588477898679/1000000000000 : ℝ) (294238949341/500000000000 : ℝ) (26291321447/62500000000 : ℝ) (10516528579/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 1 (588477898679/1000000000000 : ℝ) (294238949341/500000000000 : ℝ) (26291321447/62500000000 : ℝ) (10516528579/25000000000 : ℝ) (100913904183/200000000000 : ℝ) (504569520921/1000000000000 : ℝ) (19901750097/40000000000 : ℝ) (31096484527/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 2 (100913904183/200000000000 : ℝ) (504569520921/1000000000000 : ℝ) (19901750097/40000000000 : ℝ) (31096484527/62500000000 : ℝ) (50105663667/100000000000 : ℝ) (501056636677/1000000000000 : ℝ) (250522161093/500000000000 : ℝ) (250522161097/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 3 (50105663667/100000000000 : ℝ) (501056636677/1000000000000 : ℝ) (250522161093/500000000000 : ℝ) (250522161097/500000000000 : ℝ) (125262619857/250000000000 : ℝ) (125262619859/250000000000 : ℝ) (50105047939/100000000000 : ℝ) (250525239699/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 4 (125262619857/250000000000 : ℝ) (125262619859/250000000000 : ℝ) (50105047939/100000000000 : ℝ) (250525239699/500000000000 : ℝ) (501050479409/1000000000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 5 (501050479409/1000000000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 6 (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66719/524288 : ℝ))) 7 (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66719/524288 : ℝ)) hmem 8 (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66719/524288 : ℝ))) hcmem 8 (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66719/524288 : ℝ)) (992093710373/1000000000000 : ℝ) (124011713797/125000000000 : ℝ) (31315654963/62500000000 : ℝ) (501050479417/1000000000000 : ℝ) (31732818961/40000000000 : ℝ) (396660237021/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0646_exp_lower
  have heNumeric : (2054902441629/1000000000000 : ℝ)/4 ≤ Real.exp (-42628223229313/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902441629/1000000000000 : ℝ)/4 ≤ Real.exp ((33359/262144 : ℝ)-(396660237021/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33359/262144 : ℝ) (66719/524288 : ℝ) (396660237021/500000000000 : ℝ) (2054902441629/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0647; no trusted numerical premise.
theorem cover8_leaf0647_exp_radius : (249503391157426809/250000000000000000 : ℝ) ≤ Real.exp ((-2085/131072 : ℝ)/8) ∧ Real.exp ((-2085/131072 : ℝ)/8) ≤ (998013564629707237/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2085/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0647_exp_lower : (920113498133144721/1000000000000000000 : ℝ) ≤ Real.exp ((-17051289397693/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051289397693/25600000000000 : ℝ)/8) ≤ (460056749066572361/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051289397693/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0647_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902433123/1000000000000 : ℝ) ≤ 4*Real.exp (66719/524288 : ℝ)*Real.exp (-mu (radius 8 (2085/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902433123/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2085/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0647_exp_radius
  have hrNumeric : (984218565093/1000000000000 : ℝ) ≤ Real.exp (-2085/131072 : ℝ) ∧ Real.exp (-2085/131072 : ℝ) ≤ (492109282547/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984218565093/1000000000000 : ℝ) ≤ (radius 8 (2085/16384 : ℝ)) ∧ (radius 8 (2085/16384 : ℝ)) ≤ (492109282547/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2085/16384 : ℝ)) (984218565093/1000000000000 : ℝ) (492109282547/500000000000 : ℝ) (176957102497/1000000000000 : ℝ) (22119637813/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2085/16384 : ℝ)) (984218565093/1000000000000 : ℝ) (492109282547/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984218565093/1000000000000 : ℝ) (492109282547/500000000000 : ℝ) (496054641273/500000000000 : ℝ) (992109282547/1000000000000 : ℝ) (992077902733/1000000000000 : ℝ) (198415580547/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 1 (496054641273/500000000000 : ℝ) (992109282547/1000000000000 : ℝ) (992077902733/1000000000000 : ℝ) (198415580547/200000000000 : ℝ) (992093592639/1000000000000 : ℝ) (992093592641/1000000000000 : ℝ) (198418718503/200000000000 : ℝ) (992093592517/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 2 (992093592639/1000000000000 : ℝ) (992093592641/1000000000000 : ℝ) (198418718503/200000000000 : ℝ) (992093592517/1000000000000 : ℝ) (992093592577/1000000000000 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 3 (992093592577/1000000000000 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 4 (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 5 (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 6 (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2085/16384 : ℝ)) 7 (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2085/16384 : ℝ))) (176957102497/1000000000000 : ℝ) (22119637813/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176957102497/1000000000000 : ℝ) (22119637813/125000000000 : ℝ) (36779909453/62500000000 : ℝ) (147119637813/250000000000 : ℝ) (105165673611/250000000000 : ℝ) (420662694453/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 1 (36779909453/62500000000 : ℝ) (147119637813/250000000000 : ℝ) (105165673611/250000000000 : ℝ) (420662694453/1000000000000 : ℝ) (252285311423/500000000000 : ℝ) (504570622853/1000000000000 : ℝ) (248772472849/500000000000 : ℝ) (248772472853/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 2 (252285311423/500000000000 : ℝ) (504570622853/1000000000000 : ℝ) (248772472849/500000000000 : ℝ) (248772472853/500000000000 : ℝ) (31316111517/62500000000 : ℝ) (12526444607/25000000000 : ℝ) (62630683767/125000000000 : ℝ) (100209094029/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 3 (31316111517/62500000000 : ℝ) (12526444607/25000000000 : ℝ) (62630683767/125000000000 : ℝ) (100209094029/200000000000 : ℝ) (125262906801/250000000000 : ℝ) (501051627213/1000000000000 : ℝ) (250525813583/500000000000 : ℝ) (20042065087/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 4 (125262906801/250000000000 : ℝ) (501051627213/1000000000000 : ℝ) (250525813583/500000000000 : ℝ) (20042065087/40000000000 : ℝ) (100210325437/200000000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 5 (100210325437/200000000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 6 (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2085/16384 : ℝ))) 7 (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2085/16384 : ℝ)) hmem 8 (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2085/16384 : ℝ))) hcmem 8 (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2085/16384 : ℝ)) (968841399/976562500 : ℝ) (992093592579/1000000000000 : ℝ) (31315726699/62500000000 : ℝ) (250525813597/500000000000 : ℝ) (793322385511/1000000000000 : ℝ) (79332238553/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0647_exp_lower
  have heNumeric : (2054902433123/1000000000000 : ℝ)/4 ≤ Real.exp (-17051289397693/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902433123/1000000000000 : ℝ)/4 ≤ Real.exp ((66719/524288 : ℝ)-(79332238553/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66719/524288 : ℝ) (2085/16384 : ℝ) (79332238553/100000000000 : ℝ) (2054902433123/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0648; no trusted numerical premise.
theorem cover8_leaf0648_exp_radius : (998013534886585679/1000000000000000000 : ℝ) ≤ Real.exp ((-66721/4194304 : ℝ)/8) ∧ Real.exp ((-66721/4194304 : ℝ)/8) ≤ (12475169186082321/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66721/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0648_exp_lower : (460056748829737033/500000000000000000 : ℝ) ≤ Real.exp ((-2664263984863/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664263984863/4000000000000 : ℝ)/8) ≤ (920113497659474067/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664263984863/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0648_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902424661/1000000000000 : ℝ) ≤ 4*Real.exp (2085/16384 : ℝ)*Real.exp (-mu (radius 8 (66721/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902424661/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66721/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0648_exp_radius
  have hrNumeric : (984218330437/1000000000000 : ℝ) ≤ Real.exp (-66721/4194304 : ℝ) ∧ Real.exp (-66721/4194304 : ℝ) ≤ (492109165219/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984218330437/1000000000000 : ℝ) ≤ (radius 8 (66721/524288 : ℝ)) ∧ (radius 8 (66721/524288 : ℝ)) ≤ (492109165219/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66721/524288 : ℝ)) (984218330437/1000000000000 : ℝ) (492109165219/500000000000 : ℝ) (88479203813/500000000000 : ℝ) (176958407633/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66721/524288 : ℝ)) (984218330437/1000000000000 : ℝ) (492109165219/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984218330437/1000000000000 : ℝ) (492109165219/500000000000 : ℝ) (496054582609/500000000000 : ℝ) (992109165219/1000000000000 : ℝ) (992077784469/1000000000000 : ℝ) (99207778447/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 1 (496054582609/500000000000 : ℝ) (992109165219/1000000000000 : ℝ) (992077784469/1000000000000 : ℝ) (99207778447/100000000000 : ℝ) (992093474843/1000000000000 : ℝ) (198418694969/200000000000 : ℝ) (992093474719/1000000000000 : ℝ) (992093474721/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 2 (992093474843/1000000000000 : ℝ) (198418694969/200000000000 : ℝ) (992093474719/1000000000000 : ℝ) (992093474721/1000000000000 : ℝ) (992093474781/1000000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 3 (992093474781/1000000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 4 (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 5 (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 6 (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66721/524288 : ℝ)) 7 (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66721/524288 : ℝ))) (88479203813/500000000000 : ℝ) (176958407633/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88479203813/500000000000 : ℝ) (176958407633/1000000000000 : ℝ) (588479203813/1000000000000 : ℝ) (588479203817/1000000000000 : ℝ) (210332122859/500000000000 : ℝ) (420664245727/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 1 (588479203813/1000000000000 : ℝ) (588479203817/1000000000000 : ℝ) (210332122859/500000000000 : ℝ) (420664245727/1000000000000 : ℝ) (100914344953/200000000000 : ℝ) (126142931193/250000000000 : ℝ) (248773069479/500000000000 : ℝ) (248773069483/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 2 (100914344953/200000000000 : ℝ) (126142931193/250000000000 : ℝ) (248773069479/500000000000 : ℝ) (248773069483/500000000000 : ℝ) (501058931861/1000000000000 : ℝ) (501058931869/1000000000000 : ℝ) (250523309037/500000000000 : ℝ) (501046618083/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 3 (501058931861/1000000000000 : ℝ) (501058931869/1000000000000 : ℝ) (250523309037/500000000000 : ℝ) (501046618083/1000000000000 : ℝ) (501052774967/1000000000000 : ℝ) (7828949609/15625000000 : ℝ) (501052774929/1000000000000 : ℝ) (501052774939/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 4 (501052774967/1000000000000 : ℝ) (7828949609/15625000000 : ℝ) (501052774929/1000000000000 : ℝ) (501052774939/1000000000000 : ℝ) (125263193737/250000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 5 (125263193737/250000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 6 (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66721/524288 : ℝ))) 7 (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66721/524288 : ℝ)) hmem 8 (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66721/524288 : ℝ))) hcmem 8 (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66721/524288 : ℝ)) (49604673739/50000000000 : ℝ) (992093474783/1000000000000 : ℝ) (501052774947/1000000000000 : ℝ) (250526387479/500000000000 : ℝ) (49582768561/62500000000 : ℝ) (793324296997/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0648_exp_lower
  have heNumeric : (2054902424661/1000000000000 : ℝ)/4 ≤ Real.exp (-2664263984863/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902424661/1000000000000 : ℝ)/4 ≤ Real.exp ((2085/16384 : ℝ)-(793324296997/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2085/16384 : ℝ) (66721/524288 : ℝ) (793324296997/1000000000000 : ℝ) (2054902424661/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0649; no trusted numerical premise.
theorem cover8_leaf0649_exp_radius : (62375844071466563/62500000000000000 : ℝ) ≤ Real.exp ((-33361/2097152 : ℝ)/8) ∧ Real.exp ((-33361/2097152 : ℝ)/8) ≤ (998013505143465009/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33361/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0649_exp_lower : (920113497187988681/1000000000000000000 : ℝ) ≤ Real.exp ((-17051289608067/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051289608067/25600000000000 : ℝ)/8) ≤ (460056748593994341/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051289608067/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0649_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902416237/1000000000000 : ℝ) ≤ 4*Real.exp (66721/524288 : ℝ)*Real.exp (-mu (radius 8 (33361/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902416237/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33361/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0649_exp_radius
  have hrNumeric : (984218095781/1000000000000 : ℝ) ≤ Real.exp (-33361/2097152 : ℝ) ∧ Real.exp (-33361/2097152 : ℝ) ≤ (492109047891/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984218095781/1000000000000 : ℝ) ≤ (radius 8 (33361/262144 : ℝ)) ∧ (radius 8 (33361/262144 : ℝ)) ≤ (492109047891/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33361/262144 : ℝ)) (984218095781/1000000000000 : ℝ) (492109047891/500000000000 : ℝ) (88479856373/500000000000 : ℝ) (11059982047/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33361/262144 : ℝ)) (984218095781/1000000000000 : ℝ) (492109047891/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984218095781/1000000000000 : ℝ) (492109047891/500000000000 : ℝ) (99210904789/100000000000 : ℝ) (992109047891/1000000000000 : ℝ) (248019416551/250000000000 : ℝ) (198415533241/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 1 (99210904789/100000000000 : ℝ) (992109047891/1000000000000 : ℝ) (248019416551/250000000000 : ℝ) (198415533241/200000000000 : ℝ) (992093357047/1000000000000 : ℝ) (124011669631/125000000000 : ℝ) (496046678461/500000000000 : ℝ) (248023339231/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 2 (992093357047/1000000000000 : ℝ) (124011669631/125000000000 : ℝ) (496046678461/500000000000 : ℝ) (248023339231/250000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 3 (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 4 (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 5 (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 6 (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33361/262144 : ℝ)) 7 (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33361/262144 : ℝ))) (88479856373/500000000000 : ℝ) (11059982047/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88479856373/500000000000 : ℝ) (11059982047/62500000000 : ℝ) (588479856373/1000000000000 : ℝ) (73559982047/125000000000 : ℝ) (26291612311/62500000000 : ℝ) (52583224623/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 1 (588479856373/1000000000000 : ℝ) (73559982047/125000000000 : ℝ) (26291612311/62500000000 : ℝ) (52583224623/125000000000 : ℝ) (252286413337/500000000000 : ℝ) (12614320667/25000000000 : ℝ) (248773666103/500000000000 : ℝ) (497547332213/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 2 (252286413337/500000000000 : ℝ) (12614320667/25000000000 : ℝ) (248773666103/500000000000 : ℝ) (497547332213/1000000000000 : ℝ) (6263250993/12500000000 : ℝ) (501060079447/1000000000000 : ℝ) (501047766001/1000000000000 : ℝ) (501047766009/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 3 (6263250993/12500000000 : ℝ) (501060079447/1000000000000 : ℝ) (501047766001/1000000000000 : ℝ) (501047766009/1000000000000 : ℝ) (3131587017/6250000000 : ℝ) (62631740341/125000000000 : ℝ) (250526961341/500000000000 : ℝ) (501053922691/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 4 (3131587017/6250000000 : ℝ) (62631740341/125000000000 : ℝ) (250526961341/500000000000 : ℝ) (501053922691/1000000000000 : ℝ) (501053922701/1000000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 5 (501053922701/1000000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 6 (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33361/262144 : ℝ))) 7 (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33361/262144 : ℝ)) hmem 8 (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33361/262144 : ℝ))) hcmem 8 (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33361/262144 : ℝ)) (124011669623/125000000000 : ℝ) (496046678493/500000000000 : ℝ) (5010539227/10000000000 : ℝ) (50105392271/100000000000 : ℝ) (793326208427/1000000000000 : ℝ) (158665241689/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0649_exp_lower
  have heNumeric : (2054902416237/1000000000000 : ℝ)/4 ≤ Real.exp (-17051289608067/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902416237/1000000000000 : ℝ)/4 ≤ Real.exp ((66721/524288 : ℝ)-(158665241689/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66721/524288 : ℝ) (33361/262144 : ℝ) (158665241689/200000000000 : ℝ) (2054902416237/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0625_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0625_certificate
#check SmaleRate.Proofs.cover8_leaf0626_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0626_certificate
#check SmaleRate.Proofs.cover8_leaf0627_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0627_certificate
#check SmaleRate.Proofs.cover8_leaf0628_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0628_certificate
#check SmaleRate.Proofs.cover8_leaf0629_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0629_certificate
#check SmaleRate.Proofs.cover8_leaf0630_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0630_certificate
#check SmaleRate.Proofs.cover8_leaf0631_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0631_certificate
#check SmaleRate.Proofs.cover8_leaf0632_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0632_certificate
#check SmaleRate.Proofs.cover8_leaf0633_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0633_certificate
#check SmaleRate.Proofs.cover8_leaf0634_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0634_certificate
#check SmaleRate.Proofs.cover8_leaf0635_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0635_certificate
#check SmaleRate.Proofs.cover8_leaf0636_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0636_certificate
#check SmaleRate.Proofs.cover8_leaf0637_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0637_certificate
#check SmaleRate.Proofs.cover8_leaf0638_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0638_certificate
#check SmaleRate.Proofs.cover8_leaf0639_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0639_certificate
#check SmaleRate.Proofs.cover8_leaf0640_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0640_certificate
#check SmaleRate.Proofs.cover8_leaf0641_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0641_certificate
#check SmaleRate.Proofs.cover8_leaf0642_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0642_certificate
#check SmaleRate.Proofs.cover8_leaf0643_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0643_certificate
#check SmaleRate.Proofs.cover8_leaf0644_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0644_certificate
#check SmaleRate.Proofs.cover8_leaf0645_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0645_certificate
#check SmaleRate.Proofs.cover8_leaf0646_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0646_certificate
#check SmaleRate.Proofs.cover8_leaf0647_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0647_certificate
#check SmaleRate.Proofs.cover8_leaf0648_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0648_certificate
#check SmaleRate.Proofs.cover8_leaf0649_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0649_certificate
