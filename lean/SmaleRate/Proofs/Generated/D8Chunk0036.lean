/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0900; no trusted numerical premise.
theorem cover8_leaf0900_exp_radius : (998006039648210307/1000000000000000000 : ℝ) ≤ Real.exp ((-66973/4194304 : ℝ)/8) ∧ Real.exp ((-66973/4194304 : ℝ)/8) ≤ (249501509912052577/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66973/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0900_exp_lower : (920113449400841449/1000000000000000000 : ℝ) ≤ Real.exp ((-21314125305737/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125305737/32000000000000 : ℝ)/8) ≤ (18402268988016829/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125305737/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0900_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901562447/1000000000000 : ℝ) ≤ 4*Real.exp (16743/131072 : ℝ)*Real.exp (-mu (radius 8 (66973/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901562447/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66973/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0900_exp_radius
  have hrNumeric : (984159198917/1000000000000 : ℝ) ≤ Real.exp (-66973/4194304 : ℝ) ∧ Real.exp (-66973/4194304 : ℝ) ≤ (492079599459/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984159198917/1000000000000 : ℝ) ≤ (radius 8 (66973/524288 : ℝ)) ∧ (radius 8 (66973/524288 : ℝ)) ≤ (492079599459/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66973/524288 : ℝ)) (984159198917/1000000000000 : ℝ) (492079599459/500000000000 : ℝ) (88643487049/500000000000 : ℝ) (35457394821/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66973/524288 : ℝ)) (984159198917/1000000000000 : ℝ) (492079599459/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984159198917/1000000000000 : ℝ) (492079599459/500000000000 : ℝ) (496039799729/500000000000 : ℝ) (992079599459/1000000000000 : ℝ) (248011995541/250000000000 : ℝ) (496023991083/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 1 (496039799729/500000000000 : ℝ) (992079599459/1000000000000 : ℝ) (248011995541/250000000000 : ℝ) (496023991083/500000000000 : ℝ) (992063790811/1000000000000 : ℝ) (992063790813/1000000000000 : ℝ) (198412758137/200000000000 : ℝ) (992063790687/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 2 (992063790811/1000000000000 : ℝ) (992063790813/1000000000000 : ℝ) (198412758137/200000000000 : ℝ) (992063790687/1000000000000 : ℝ) (248015947687/250000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 3 (248015947687/250000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 4 (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 5 (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 6 (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66973/524288 : ℝ)) 7 (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66973/524288 : ℝ))) (88643487049/500000000000 : ℝ) (35457394821/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88643487049/500000000000 : ℝ) (35457394821/200000000000 : ℝ) (588643487049/1000000000000 : ℝ) (588643487053/1000000000000 : ℝ) (210527298763/500000000000 : ℝ) (84210919507/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 1 (588643487049/1000000000000 : ℝ) (588643487053/1000000000000 : ℝ) (210527298763/500000000000 : ℝ) (84210919507/200000000000 : ℝ) (504849042287/1000000000000 : ℝ) (252424521147/500000000000 : ℝ) (497846408569/1000000000000 : ℝ) (497846408577/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 2 (504849042287/1000000000000 : ℝ) (252424521147/500000000000 : ℝ) (497846408569/1000000000000 : ℝ) (497846408577/1000000000000 : ℝ) (125336931357/250000000000 : ℝ) (125336931359/250000000000 : ℝ) (250667749507/500000000000 : ℝ) (250667749511/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 3 (125336931357/250000000000 : ℝ) (125336931359/250000000000 : ℝ) (250667749507/500000000000 : ℝ) (250667749511/500000000000 : ℝ) (501341612221/1000000000000 : ℝ) (501341612229/1000000000000 : ℝ) (501341612183/1000000000000 : ℝ) (15666925381/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 4 (501341612221/1000000000000 : ℝ) (501341612229/1000000000000 : ℝ) (501341612183/1000000000000 : ℝ) (15666925381/31250000000 : ℝ) (250670806101/500000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 5 (250670806101/500000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 6 (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66973/524288 : ℝ))) 7 (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66973/524288 : ℝ)) hmem 8 (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66973/524288 : ℝ))) hcmem 8 (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66973/524288 : ℝ)) (992063790747/1000000000000 : ℝ) (3968255163/4000000000 : ℝ) (501341612201/1000000000000 : ℝ) (501341612211/1000000000000 : ℝ) (396902684211/500000000000 : ℝ) (793805368441/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0900_exp_lower
  have heNumeric : (2054901562447/1000000000000 : ℝ)/4 ≤ Real.exp (-21314125305737/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901562447/1000000000000 : ℝ)/4 ≤ Real.exp ((16743/131072 : ℝ)-(793805368441/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16743/131072 : ℝ) (66973/524288 : ℝ) (793805368441/1000000000000 : ℝ) (2054901562447/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0901; no trusted numerical premise.
theorem cover8_leaf0901_exp_radius : (998006009905313011/1000000000000000000 : ℝ) ≤ Real.exp ((-33487/2097152 : ℝ)/8) ∧ Real.exp ((-33487/2097152 : ℝ)/8) ≤ (249501502476328253/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33487/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0901_exp_lower : (920113449490855321/1000000000000000000 : ℝ) ≤ Real.exp ((-85256501122771/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501122771/128000000000000 : ℝ)/8) ≤ (460056724745427661/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501122771/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0901_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980312811/200000000000 : ℝ) ≤ 4*Real.exp (66973/524288 : ℝ)*Real.exp (-mu (radius 8 (33487/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980312811/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33487/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0901_exp_radius
  have hrNumeric : (39366358571/40000000000 : ℝ) ≤ Real.exp (-33487/2097152 : ℝ) ∧ Real.exp (-33487/2097152 : ℝ) ≤ (246039741069/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39366358571/40000000000 : ℝ) ≤ (radius 8 (33487/262144 : ℝ)) ∧ (radius 8 (33487/262144 : ℝ)) ≤ (246039741069/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33487/262144 : ℝ)) (39366358571/40000000000 : ℝ) (246039741069/250000000000 : ℝ) (177288276643/1000000000000 : ℝ) (177288276649/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33487/262144 : ℝ)) (39366358571/40000000000 : ℝ) (246039741069/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39366358571/40000000000 : ℝ) (246039741069/250000000000 : ℝ) (992079482137/1000000000000 : ℝ) (496039741069/500000000000 : ℝ) (992047863903/1000000000000 : ℝ) (31001495747/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 1 (992079482137/1000000000000 : ℝ) (496039741069/500000000000 : ℝ) (992047863903/1000000000000 : ℝ) (31001495747/31250000000 : ℝ) (49603183651/50000000000 : ℝ) (992063673021/1000000000000 : ℝ) (496031836447/500000000000 : ℝ) (15500994889/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 2 (49603183651/50000000000 : ℝ) (992063673021/1000000000000 : ℝ) (496031836447/500000000000 : ℝ) (15500994889/15625000000 : ℝ) (992063672957/1000000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 3 (992063672957/1000000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 4 (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 5 (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 6 (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33487/262144 : ℝ)) 7 (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33487/262144 : ℝ))) (177288276643/1000000000000 : ℝ) (177288276649/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177288276643/1000000000000 : ℝ) (177288276649/1000000000000 : ℝ) (588644138321/1000000000000 : ℝ) (23545765533/40000000000 : ℝ) (13158004509/31250000000 : ℝ) (52632018037/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 1 (588644138321/1000000000000 : ℝ) (23545765533/40000000000 : ℝ) (13158004509/31250000000 : ℝ) (52632018037/125000000000 : ℝ) (63106267663/125000000000 : ℝ) (504850141311/1000000000000 : ℝ) (248923799203/500000000000 : ℝ) (497847598413/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 2 (63106267663/125000000000 : ℝ) (504850141311/1000000000000 : ℝ) (248923799203/500000000000 : ℝ) (497847598413/1000000000000 : ℝ) (100269773971/200000000000 : ℝ) (250674434931/500000000000 : ℝ) (250668321893/500000000000 : ℝ) (250668321897/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 3 (100269773971/200000000000 : ℝ) (250674434931/500000000000 : ℝ) (250668321893/500000000000 : ℝ) (250668321897/500000000000 : ℝ) (25067137841/50000000000 : ℝ) (125335689207/250000000000 : ℝ) (501342756783/1000000000000 : ℝ) (501342756791/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 4 (25067137841/50000000000 : ℝ) (125335689207/250000000000 : ℝ) (501342756783/1000000000000 : ℝ) (501342756791/1000000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 5 (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 6 (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33487/262144 : ℝ))) 7 (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33487/262144 : ℝ)) hmem 8 (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33487/262144 : ℝ))) hcmem 8 (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33487/262144 : ℝ)) (248015918239/250000000000 : ℝ) (992063672959/1000000000000 : ℝ) (501342756801/1000000000000 : ℝ) (50134275681/100000000000 : ℝ) (79380727499/100000000000 : ℝ) (793807275007/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0901_exp_lower
  have heNumeric : (410980312811/200000000000 : ℝ)/4 ≤ Real.exp (-85256501122771/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980312811/200000000000 : ℝ)/4 ≤ Real.exp ((66973/524288 : ℝ)-(793807275007/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66973/524288 : ℝ) (33487/262144 : ℝ) (793807275007/1000000000000 : ℝ) (410980312811/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0902; no trusted numerical premise.
theorem cover8_leaf0902_exp_radius : (998005980162416603/1000000000000000000 : ℝ) ≤ Real.exp ((-66975/4194304 : ℝ)/8) ∧ Real.exp ((-66975/4194304 : ℝ)/8) ≤ (249501495040604151/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66975/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0902_exp_lower : (920113449583514519/1000000000000000000 : ℝ) ≤ Real.exp ((-1705130020393/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705130020393/2560000000000 : ℝ)/8) ≤ (23002836239587863/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705130020393/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0902_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901565711/1000000000000 : ℝ) ≤ 4*Real.exp (33487/262144 : ℝ)*Real.exp (-mu (radius 8 (66975/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901565711/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66975/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0902_exp_radius
  have hrNumeric : (492079364817/500000000000 : ℝ) ≤ Real.exp (-66975/4194304 : ℝ) ∧ Real.exp (-66975/4194304 : ℝ) ≤ (196831745927/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492079364817/500000000000 : ℝ) ≤ (radius 8 (66975/524288 : ℝ)) ∧ (radius 8 (66975/524288 : ℝ)) ≤ (196831745927/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66975/524288 : ℝ)) (492079364817/500000000000 : ℝ) (196831745927/200000000000 : ℝ) (44322394793/250000000000 : ℝ) (177289579179/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66975/524288 : ℝ)) (492079364817/500000000000 : ℝ) (196831745927/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492079364817/500000000000 : ℝ) (196831745927/200000000000 : ℝ) (992079364817/1000000000000 : ℝ) (496039682409/500000000000 : ℝ) (496023872821/500000000000 : ℝ) (992047745643/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 1 (992079364817/1000000000000 : ℝ) (496039682409/500000000000 : ℝ) (496023872821/500000000000 : ℝ) (992047745643/1000000000000 : ℝ) (992063555229/1000000000000 : ℝ) (992063555231/1000000000000 : ℝ) (992063555103/1000000000000 : ℝ) (198412711021/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 2 (992063555229/1000000000000 : ℝ) (992063555231/1000000000000 : ℝ) (992063555103/1000000000000 : ℝ) (198412711021/200000000000 : ℝ) (496031777583/500000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 3 (496031777583/500000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 4 (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 5 (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 6 (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66975/524288 : ℝ)) 7 (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66975/524288 : ℝ))) (44322394793/250000000000 : ℝ) (177289579179/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44322394793/250000000000 : ℝ) (177289579179/1000000000000 : ℝ) (294322394793/500000000000 : ℝ) (58864478959/100000000000 : ℝ) (16842307641/40000000000 : ℝ) (84211538207/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 1 (294322394793/500000000000 : ℝ) (58864478959/100000000000 : ℝ) (16842307641/40000000000 : ℝ) (84211538207/200000000000 : ℝ) (100970248061/200000000000 : ℝ) (504851240313/1000000000000 : ℝ) (1944721829/3906250000 : ℝ) (497848788233/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 2 (100970248061/200000000000 : ℝ) (504851240313/1000000000000 : ℝ) (1944721829/3906250000 : ℝ) (497848788233/1000000000000 : ℝ) (62668751783/125000000000 : ℝ) (501350014273/1000000000000 : ℝ) (501337788541/1000000000000 : ℝ) (10026755771/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 3 (62668751783/125000000000 : ℝ) (501350014273/1000000000000 : ℝ) (501337788541/1000000000000 : ℝ) (10026755771/20000000000 : ℝ) (250671950701/500000000000 : ℝ) (125335975353/250000000000 : ℝ) (100268780273/200000000000 : ℝ) (4010751211/8000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 4 (250671950701/500000000000 : ℝ) (125335975353/250000000000 : ℝ) (100268780273/200000000000 : ℝ) (4010751211/8000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 5 (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 6 (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66975/524288 : ℝ))) 7 (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66975/524288 : ℝ)) hmem 8 (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66975/524288 : ℝ))) hcmem 8 (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66975/524288 : ℝ)) (198412711033/200000000000 : ℝ) (31001986099/31250000000 : ℝ) (501343901383/1000000000000 : ℝ) (250671950697/500000000000 : ℝ) (793809181529/1000000000000 : ℝ) (15876183631/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0902_exp_lower
  have heNumeric : (2054901565711/1000000000000 : ℝ)/4 ≤ Real.exp (-1705130020393/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901565711/1000000000000 : ℝ)/4 ≤ Real.exp ((33487/262144 : ℝ)-(15876183631/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33487/262144 : ℝ) (66975/524288 : ℝ) (15876183631/20000000000 : ℝ) (2054901565711/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0903; no trusted numerical premise.
theorem cover8_leaf0903_exp_radius : (24950148760488027/25000000000000000 : ℝ) ≤ Real.exp ((-2093/131072 : ℝ)/8) ∧ Real.exp ((-2093/131072 : ℝ)/8) ≤ (998005950419521081/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2093/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0903_exp_lower : (92011344967789893/100000000000000000 : ℝ) ≤ Real.exp ((-85256500914609/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500914609/128000000000000 : ℝ)/8) ≤ (920113449677898931/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500914609/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0903_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901567397/1000000000000 : ℝ) ≤ 4*Real.exp (66975/524288 : ℝ)*Real.exp (-mu (radius 8 (2093/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901567397/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2093/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0903_exp_radius
  have hrNumeric : (61509905937/62500000000 : ℝ) ≤ Real.exp (-2093/131072 : ℝ) ∧ Real.exp (-2093/131072 : ℝ) ≤ (984158494993/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61509905937/62500000000 : ℝ) ≤ (radius 8 (2093/16384 : ℝ)) ∧ (radius 8 (2093/16384 : ℝ)) ≤ (984158494993/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2093/16384 : ℝ)) (61509905937/62500000000 : ℝ) (984158494993/1000000000000 : ℝ) (177290881697/1000000000000 : ℝ) (22161360213/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2093/16384 : ℝ)) (61509905937/62500000000 : ℝ) (984158494993/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61509905937/62500000000 : ℝ) (984158494993/1000000000000 : ℝ) (124009905937/125000000000 : ℝ) (992079247497/1000000000000 : ℝ) (49602381369/50000000000 : ℝ) (496023813691/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 1 (124009905937/125000000000 : ℝ) (992079247497/1000000000000 : ℝ) (49602381369/50000000000 : ℝ) (496023813691/500000000000 : ℝ) (496031718719/500000000000 : ℝ) (1550099121/1562500000 : ℝ) (1937623901/1953125000 : ℝ) (496031718657/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 2 (496031718719/500000000000 : ℝ) (1550099121/1562500000 : ℝ) (1937623901/1953125000 : ℝ) (496031718657/500000000000 : ℝ) (7936507499/8000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 3 (7936507499/8000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 4 (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 5 (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 6 (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2093/16384 : ℝ)) 7 (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2093/16384 : ℝ))) (177290881697/1000000000000 : ℝ) (22161360213/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177290881697/1000000000000 : ℝ) (22161360213/125000000000 : ℝ) (36790340053/62500000000 : ℝ) (147161360213/250000000000 : ℝ) (52632404719/125000000000 : ℝ) (210529618881/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 1 (36790340053/62500000000 : ℝ) (147161360213/250000000000 : ℝ) (52632404719/125000000000 : ℝ) (210529618881/500000000000 : ℝ) (5048523393/10000000000 : ℝ) (504852339307/1000000000000 : ℝ) (99569995607/200000000000 : ℝ) (497849978043/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 2 (5048523393/10000000000 : ℝ) (504852339307/1000000000000 : ℝ) (99569995607/200000000000 : ℝ) (497849978043/1000000000000 : ℝ) (501351158667/1000000000000 : ℝ) (20054046347/40000000000 : ℝ) (501338933289/1000000000000 : ℝ) (501338933297/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 3 (501351158667/1000000000000 : ℝ) (20054046347/40000000000 : ℝ) (501338933289/1000000000000 : ℝ) (501338933297/1000000000000 : ℝ) (250672522989/500000000000 : ℝ) (250672522993/500000000000 : ℝ) (25067252297/50000000000 : ℝ) (501345045949/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 4 (250672522989/500000000000 : ℝ) (250672522993/500000000000 : ℝ) (25067252297/50000000000 : ℝ) (501345045949/1000000000000 : ℝ) (501345045959/1000000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 5 (501345045959/1000000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 6 (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2093/16384 : ℝ))) 7 (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2093/16384 : ℝ)) hmem 8 (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2093/16384 : ℝ))) hcmem 8 (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2093/16384 : ℝ)) (496031718687/500000000000 : ℝ) (992063437377/1000000000000 : ℝ) (250672522979/500000000000 : ℝ) (31334065373/62500000000 : ℝ) (396905544029/500000000000 : ℝ) (396905544039/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0903_exp_lower
  have heNumeric : (2054901567397/1000000000000 : ℝ)/4 ≤ Real.exp (-85256500914609/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901567397/1000000000000 : ℝ)/4 ≤ Real.exp ((66975/524288 : ℝ)-(396905544039/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66975/524288 : ℝ) (2093/16384 : ℝ) (396905544039/500000000000 : ℝ) (2054901567397/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0904; no trusted numerical premise.
theorem cover8_leaf0904_exp_radius : (249501480169156611/250000000000000000 : ℝ) ≤ Real.exp ((-66977/4194304 : ℝ)/8) ∧ Real.exp ((-66977/4194304 : ℝ)/8) ≤ (199601184135325289/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66977/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0904_exp_lower : (57507090610882723/62500000000000000 : ℝ) ≤ Real.exp ((-532853130047/800000000000 : ℝ)/8) ∧ Real.exp ((-532853130047/800000000000 : ℝ)/8) ≤ (920113449774123569/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532853130047/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0904_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901569117/1000000000000 : ℝ) ≤ 4*Real.exp (2093/16384 : ℝ)*Real.exp (-mu (radius 8 (66977/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901569117/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66977/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0904_exp_radius
  have hrNumeric : (19683165207/20000000000 : ℝ) ≤ Real.exp (-66977/4194304 : ℝ) ∧ Real.exp (-66977/4194304 : ℝ) ≤ (984158260351/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19683165207/20000000000 : ℝ) ≤ (radius 8 (66977/524288 : ℝ)) ∧ (radius 8 (66977/524288 : ℝ)) ≤ (984158260351/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66977/524288 : ℝ)) (19683165207/20000000000 : ℝ) (984158260351/1000000000000 : ℝ) (44323046053/250000000000 : ℝ) (177292184219/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66977/524288 : ℝ)) (19683165207/20000000000 : ℝ) (984158260351/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19683165207/20000000000 : ℝ) (984158260351/1000000000000 : ℝ) (39683165207/40000000000 : ℝ) (15501236409/15625000000 : ℝ) (992047509119/1000000000000 : ℝ) (1550074233/1562500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 1 (39683165207/40000000000 : ℝ) (15501236409/15625000000 : ℝ) (992047509119/1000000000000 : ℝ) (1550074233/1562500000 : ℝ) (992063319647/1000000000000 : ℝ) (31001978739/31250000000 : ℝ) (992063319521/1000000000000 : ℝ) (992063319523/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 2 (992063319647/1000000000000 : ℝ) (31001978739/31250000000 : ℝ) (992063319521/1000000000000 : ℝ) (992063319523/1000000000000 : ℝ) (31001978737/31250000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 3 (31001978737/31250000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 4 (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 5 (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 6 (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66977/524288 : ℝ)) 7 (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66977/524288 : ℝ))) (44323046053/250000000000 : ℝ) (177292184219/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44323046053/250000000000 : ℝ) (177292184219/1000000000000 : ℝ) (294323046053/500000000000 : ℝ) (58864609211/100000000000 : ℝ) (210530392231/500000000000 : ℝ) (421060784471/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 1 (294323046053/500000000000 : ℝ) (58864609211/100000000000 : ℝ) (210530392231/500000000000 : ℝ) (421060784471/1000000000000 : ℝ) (126213359571/250000000000 : ℝ) (504853438291/1000000000000 : ℝ) (62231395979/125000000000 : ℝ) (3111569799/6250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 2 (126213359571/250000000000 : ℝ) (504853438291/1000000000000 : ℝ) (62231395979/125000000000 : ℝ) (3111569799/6250000000 : ℝ) (250676151529/500000000000 : ℝ) (250676151533/500000000000 : ℝ) (62667509753/125000000000 : ℝ) (501340078033/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 3 (250676151529/500000000000 : ℝ) (250676151533/500000000000 : ℝ) (62667509753/125000000000 : ℝ) (501340078033/1000000000000 : ℝ) (501346190541/1000000000000 : ℝ) (10026923811/20000000000 : ℝ) (501346190503/1000000000000 : ℝ) (501346190513/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 4 (501346190541/1000000000000 : ℝ) (10026923811/20000000000 : ℝ) (501346190503/1000000000000 : ℝ) (501346190513/1000000000000 : ℝ) (250673095261/500000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 5 (250673095261/500000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 6 (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66977/524288 : ℝ))) 7 (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66977/524288 : ℝ)) hmem 8 (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66977/524288 : ℝ))) hcmem 8 (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66977/524288 : ℝ)) (992063319583/1000000000000 : ℝ) (496031659793/500000000000 : ℝ) (501346190521/1000000000000 : ℝ) (125336547633/250000000000 : ℝ) (793812994569/1000000000000 : ℝ) (79381299459/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0904_exp_lower
  have heNumeric : (2054901569117/1000000000000 : ℝ)/4 ≤ Real.exp (-532853130047/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901569117/1000000000000 : ℝ)/4 ≤ Real.exp ((2093/16384 : ℝ)-(79381299459/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2093/16384 : ℝ) (66977/524288 : ℝ) (79381299459/100000000000 : ℝ) (2054901569117/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0905; no trusted numerical premise.
theorem cover8_leaf0905_exp_radius : (199601178186746539/200000000000000000 : ℝ) ≤ Real.exp ((-33489/2097152 : ℝ)/8) ∧ Real.exp ((-33489/2097152 : ℝ)/8) ≤ (124750736366716587/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33489/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0905_exp_lower : (920113449873798631/1000000000000000000 : ℝ) ≤ Real.exp ((-85256500696591/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500696591/128000000000000 : ℝ)/8) ≤ (115014181234224829/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500696591/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0905_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901570897/1000000000000 : ℝ) ≤ 4*Real.exp (66977/524288 : ℝ)*Real.exp (-mu (radius 8 (33489/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901570897/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33489/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0905_exp_radius
  have hrNumeric : (984158025709/1000000000000 : ℝ) ≤ Real.exp (-33489/2097152 : ℝ) ∧ Real.exp (-33489/2097152 : ℝ) ≤ (98415802571/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984158025709/1000000000000 : ℝ) ≤ (radius 8 (33489/262144 : ℝ)) ∧ (radius 8 (33489/262144 : ℝ)) ≤ (98415802571/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33489/262144 : ℝ)) (984158025709/1000000000000 : ℝ) (98415802571/100000000000 : ℝ) (22161685839/125000000000 : ℝ) (88646743359/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33489/262144 : ℝ)) (984158025709/1000000000000 : ℝ) (98415802571/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984158025709/1000000000000 : ℝ) (98415802571/100000000000 : ℝ) (496039506427/500000000000 : ℝ) (198415802571/200000000000 : ℝ) (496023695429/500000000000 : ℝ) (992047390859/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 1 (496039506427/500000000000 : ℝ) (198415802571/200000000000 : ℝ) (496023695429/500000000000 : ℝ) (992047390859/1000000000000 : ℝ) (15500987529/15625000000 : ℝ) (992063201857/1000000000000 : ℝ) (99206320173/100000000000 : ℝ) (248015800433/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 2 (15500987529/15625000000 : ℝ) (992063201857/1000000000000 : ℝ) (99206320173/100000000000 : ℝ) (248015800433/250000000000 : ℝ) (992063201793/1000000000000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 3 (992063201793/1000000000000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 4 (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 5 (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 6 (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33489/262144 : ℝ)) 7 (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33489/262144 : ℝ))) (22161685839/125000000000 : ℝ) (88646743359/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22161685839/125000000000 : ℝ) (88646743359/500000000000 : ℝ) (147161685839/250000000000 : ℝ) (588646743359/1000000000000 : ℝ) (105265582787/250000000000 : ℝ) (105265582789/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 1 (147161685839/250000000000 : ℝ) (588646743359/1000000000000 : ℝ) (105265582787/250000000000 : ℝ) (105265582789/250000000000 : ℝ) (126213634313/250000000000 : ℝ) (252427268629/500000000000 : ℝ) (124463089403/250000000000 : ℝ) (497852357619/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 2 (126213634313/250000000000 : ℝ) (252427268629/500000000000 : ℝ) (124463089403/250000000000 : ℝ) (497852357619/1000000000000 : ℝ) (62669180929/125000000000 : ℝ) (501353447439/1000000000000 : ℝ) (501341222743/1000000000000 : ℝ) (501341222751/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 3 (62669180929/125000000000 : ℝ) (501353447439/1000000000000 : ℝ) (501341222743/1000000000000 : ℝ) (501341222751/1000000000000 : ℝ) (501347335087/1000000000000 : ℝ) (100269467019/200000000000 : ℝ) (10026946701/20000000000 : ℝ) (250673667529/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 4 (501347335087/1000000000000 : ℝ) (100269467019/200000000000 : ℝ) (10026946701/20000000000 : ℝ) (250673667529/500000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 5 (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 6 (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33489/262144 : ℝ))) 7 (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33489/262144 : ℝ)) hmem 8 (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33489/262144 : ℝ))) hcmem 8 (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33489/262144 : ℝ)) (1937623441/1953125000 : ℝ) (198412640359/200000000000 : ℝ) (125336833767/250000000000 : ℝ) (501347335077/1000000000000 : ℝ) (158762980211/200000000000 : ℝ) (49613431317/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0905_exp_lower
  have heNumeric : (2054901570897/1000000000000 : ℝ)/4 ≤ Real.exp (-85256500696591/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901570897/1000000000000 : ℝ)/4 ≤ Real.exp ((66977/524288 : ℝ)-(49613431317/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66977/524288 : ℝ) (33489/262144 : ℝ) (49613431317/62500000000 : ℝ) (2054901570897/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0906; no trusted numerical premise.
theorem cover8_leaf0906_exp_radius : (998005861190839831/1000000000000000000 : ℝ) ≤ Real.exp ((-66979/4194304 : ℝ)/8) ∧ Real.exp ((-66979/4194304 : ℝ)/8) ≤ (124750732648854979/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66979/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0906_exp_lower : (57507090623399613/62500000000000000 : ℝ) ≤ Real.exp ((-42628250292319/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250292319/64000000000000 : ℝ)/8) ≤ (920113449974393809/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250292319/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0906_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980314539/200000000000 : ℝ) ≤ 4*Real.exp (33489/262144 : ℝ)*Real.exp (-mu (radius 8 (66979/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980314539/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66979/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0906_exp_radius
  have hrNumeric : (984157791067/1000000000000 : ℝ) ≤ Real.exp (-66979/4194304 : ℝ) ∧ Real.exp (-66979/4194304 : ℝ) ≤ (246039447767/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984157791067/1000000000000 : ℝ) ≤ (radius 8 (66979/524288 : ℝ)) ∧ (radius 8 (66979/524288 : ℝ)) ≤ (246039447767/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66979/524288 : ℝ)) (984157791067/1000000000000 : ℝ) (246039447767/250000000000 : ℝ) (177294789207/1000000000000 : ℝ) (88647394607/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66979/524288 : ℝ)) (984157791067/1000000000000 : ℝ) (246039447767/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984157791067/1000000000000 : ℝ) (246039447767/250000000000 : ℝ) (992078895533/1000000000000 : ℝ) (496039447767/500000000000 : ℝ) (248011818149/250000000000 : ℝ) (496023636299/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 1 (992078895533/1000000000000 : ℝ) (496039447767/500000000000 : ℝ) (248011818149/250000000000 : ℝ) (496023636299/500000000000 : ℝ) (31001971377/31250000000 : ℝ) (496031542033/500000000000 : ℝ) (496031541969/500000000000 : ℝ) (49603154197/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 2 (31001971377/31250000000 : ℝ) (496031542033/500000000000 : ℝ) (496031541969/500000000000 : ℝ) (49603154197/50000000000 : ℝ) (992063084001/1000000000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 3 (992063084001/1000000000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 4 (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 5 (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 6 (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66979/524288 : ℝ)) 7 (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66979/524288 : ℝ))) (177294789207/1000000000000 : ℝ) (88647394607/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177294789207/1000000000000 : ℝ) (88647394607/500000000000 : ℝ) (588647394603/1000000000000 : ℝ) (588647394607/1000000000000 : ℝ) (210531938911/500000000000 : ℝ) (421063877831/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 1 (588647394603/1000000000000 : ℝ) (588647394607/1000000000000 : ℝ) (210531938911/500000000000 : ℝ) (421063877831/1000000000000 : ℝ) (126213909053/250000000000 : ℝ) (504855636219/1000000000000 : ℝ) (248926773691/500000000000 : ℝ) (49785354739/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 2 (126213909053/250000000000 : ℝ) (504855636219/1000000000000 : ℝ) (248926773691/500000000000 : ℝ) (49785354739/100000000000 : ℝ) (501354591797/1000000000000 : ℝ) (100270918361/200000000000 : ℝ) (501342367453/1000000000000 : ℝ) (250671183731/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 3 (501354591797/1000000000000 : ℝ) (100270918361/200000000000 : ℝ) (501342367453/1000000000000 : ℝ) (250671183731/500000000000 : ℝ) (4010787837/8000000000 : ℝ) (250674239817/500000000000 : ℝ) (501348479587/1000000000000 : ℝ) (501348479597/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 4 (4010787837/8000000000 : ℝ) (250674239817/500000000000 : ℝ) (501348479587/1000000000000 : ℝ) (501348479597/1000000000000 : ℝ) (250674239803/500000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 5 (250674239803/500000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 6 (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66979/524288 : ℝ))) 7 (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66979/524288 : ℝ)) hmem 8 (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66979/524288 : ℝ))) hcmem 8 (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66979/524288 : ℝ)) (248015771/250000000 : ℝ) (992063084003/1000000000000 : ℝ) (100269695921/200000000000 : ℝ) (3916784997/7812500000 : ℝ) (396908403763/500000000000 : ℝ) (396908403773/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0906_exp_lower
  have heNumeric : (410980314539/200000000000 : ℝ)/4 ≤ Real.exp (-42628250292319/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980314539/200000000000 : ℝ)/4 ≤ Real.exp ((33489/262144 : ℝ)-(396908403773/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33489/262144 : ℝ) (66979/524288 : ℝ) (396908403773/500000000000 : ℝ) (410980314539/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0907; no trusted numerical premise.
theorem cover8_leaf0907_exp_radius : (499002915723973927/500000000000000000 : ℝ) ≤ Real.exp ((-16745/1048576 : ℝ)/8) ∧ Real.exp ((-16745/1048576 : ℝ)/8) ≤ (199601166289589571/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16745/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0907_exp_lower : (115014181259819303/125000000000000000 : ℝ) ≤ Real.exp ((-85256500468717/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500468717/128000000000000 : ℝ)/8) ≤ (36804538003142177/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500468717/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0907_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725393639/250000000000 : ℝ) ≤ 4*Real.exp (66979/524288 : ℝ)*Real.exp (-mu (radius 8 (16745/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725393639/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16745/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0907_exp_radius
  have hrNumeric : (492078778213/500000000000 : ℝ) ≤ Real.exp (-16745/1048576 : ℝ) ∧ Real.exp (-16745/1048576 : ℝ) ≤ (984157556427/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492078778213/500000000000 : ℝ) ≤ (radius 8 (16745/131072 : ℝ)) ∧ (radius 8 (16745/131072 : ℝ)) ≤ (984157556427/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16745/131072 : ℝ)) (492078778213/500000000000 : ℝ) (984157556427/1000000000000 : ℝ) (177296091687/1000000000000 : ℝ) (177296091693/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16745/131072 : ℝ)) (492078778213/500000000000 : ℝ) (984157556427/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492078778213/500000000000 : ℝ) (984157556427/1000000000000 : ℝ) (992078778213/1000000000000 : ℝ) (496039389107/500000000000 : ℝ) (198409430867/200000000000 : ℝ) (992047154337/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 1 (992078778213/1000000000000 : ℝ) (496039389107/500000000000 : ℝ) (198409430867/200000000000 : ℝ) (992047154337/1000000000000 : ℝ) (496031483137/500000000000 : ℝ) (248015741569/250000000000 : ℝ) (992062966147/1000000000000 : ℝ) (19841259323/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 2 (496031483137/500000000000 : ℝ) (248015741569/250000000000 : ℝ) (992062966147/1000000000000 : ℝ) (19841259323/20000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 3 (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 4 (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 5 (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 6 (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16745/131072 : ℝ)) 7 (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16745/131072 : ℝ))) (177296091687/1000000000000 : ℝ) (177296091693/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177296091687/1000000000000 : ℝ) (177296091693/1000000000000 : ℝ) (588648045843/1000000000000 : ℝ) (588648045847/1000000000000 : ℝ) (421065424473/1000000000000 : ℝ) (421065424481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 1 (588648045843/1000000000000 : ℝ) (588648045847/1000000000000 : ℝ) (421065424473/1000000000000 : ℝ) (421065424481/1000000000000 : ℝ) (252428367579/500000000000 : ℝ) (126214183791/250000000000 : ℝ) (99570947427/200000000000 : ℝ) (248927368571/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 2 (252428367579/500000000000 : ℝ) (126214183791/250000000000 : ℝ) (99570947427/200000000000 : ℝ) (248927368571/500000000000 : ℝ) (250677868073/500000000000 : ℝ) (501355736153/1000000000000 : ℝ) (125335878037/250000000000 : ℝ) (100268702431/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 3 (250677868073/500000000000 : ℝ) (501355736153/1000000000000 : ℝ) (125335878037/250000000000 : ℝ) (100268702431/200000000000 : ℝ) (501349624147/1000000000000 : ℝ) (250674812077/500000000000 : ℝ) (501349624109/1000000000000 : ℝ) (501349624117/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 4 (501349624147/1000000000000 : ℝ) (250674812077/500000000000 : ℝ) (501349624109/1000000000000 : ℝ) (501349624117/1000000000000 : ℝ) (7833587877/15625000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 5 (7833587877/15625000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 6 (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16745/131072 : ℝ))) 7 (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16745/131072 : ℝ)) hmem 8 (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16745/131072 : ℝ))) hcmem 8 (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16745/131072 : ℝ)) (99206296621/100000000000 : ℝ) (992062966213/1000000000000 : ℝ) (501349624127/1000000000000 : ℝ) (62668703017/125000000000 : ℝ) (198454678493/250000000000 : ℝ) (793818713989/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0907_exp_lower
  have heNumeric : (513725393639/250000000000 : ℝ)/4 ≤ Real.exp (-85256500468717/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725393639/250000000000 : ℝ)/4 ≤ Real.exp ((66979/524288 : ℝ)-(793818713989/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66979/524288 : ℝ) (16745/131072 : ℝ) (793818713989/1000000000000 : ℝ) (513725393639/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0908; no trusted numerical premise.
theorem cover8_leaf0908_exp_radius : (249501450426264191/250000000000000000 : ℝ) ≤ Real.exp ((-66981/4194304 : ℝ)/8) ∧ Real.exp ((-66981/4194304 : ℝ)/8) ≤ (199601160341011353/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66981/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0908_exp_lower : (460056725091702563/500000000000000000 : ℝ) ≤ Real.exp ((-21314125088007/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125088007/32000000000000 : ℝ)/8) ≤ (920113450183405127/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125088007/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0908_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901576429/1000000000000 : ℝ) ≤ 4*Real.exp (16745/131072 : ℝ)*Real.exp (-mu (radius 8 (66981/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901576429/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66981/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0908_exp_radius
  have hrNumeric : (123019665223/125000000000 : ℝ) ≤ Real.exp (-66981/4194304 : ℝ) ∧ Real.exp (-66981/4194304 : ℝ) ≤ (196831464357/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123019665223/125000000000 : ℝ) ≤ (radius 8 (66981/524288 : ℝ)) ∧ (radius 8 (66981/524288 : ℝ)) ≤ (196831464357/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66981/524288 : ℝ)) (123019665223/125000000000 : ℝ) (196831464357/200000000000 : ℝ) (88648697081/500000000000 : ℝ) (177297394169/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66981/524288 : ℝ)) (123019665223/125000000000 : ℝ) (196831464357/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123019665223/125000000000 : ℝ) (196831464357/200000000000 : ℝ) (248019665223/250000000000 : ℝ) (992078660893/1000000000000 : ℝ) (496023518037/500000000000 : ℝ) (39681881443/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 1 (248019665223/250000000000 : ℝ) (992078660893/1000000000000 : ℝ) (496023518037/500000000000 : ℝ) (39681881443/40000000000 : ℝ) (992062848483/1000000000000 : ℝ) (248015712121/250000000000 : ℝ) (248015712089/250000000000 : ℝ) (496031424179/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 2 (992062848483/1000000000000 : ℝ) (248015712121/250000000000 : ℝ) (248015712089/250000000000 : ℝ) (496031424179/500000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 3 (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 4 (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 5 (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 6 (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66981/524288 : ℝ)) 7 (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66981/524288 : ℝ))) (88648697081/500000000000 : ℝ) (177297394169/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88648697081/500000000000 : ℝ) (177297394169/1000000000000 : ℝ) (588648697081/1000000000000 : ℝ) (117729739417/200000000000 : ℝ) (52633371389/125000000000 : ℝ) (421066971121/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 1 (588648697081/1000000000000 : ℝ) (117729739417/200000000000 : ℝ) (52633371389/125000000000 : ℝ) (421066971121/1000000000000 : ℝ) (31553614631/62500000000 : ℝ) (504857834103/1000000000000 : ℝ) (497855926879/1000000000000 : ℝ) (497855926887/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 2 (31553614631/62500000000 : ℝ) (504857834103/1000000000000 : ℝ) (497855926879/1000000000000 : ℝ) (497855926887/1000000000000 : ℝ) (501356880487/1000000000000 : ℝ) (100271376099/200000000000 : ℝ) (501344656833/1000000000000 : ℝ) (250672328421/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 3 (501356880487/1000000000000 : ℝ) (100271376099/200000000000 : ℝ) (501344656833/1000000000000 : ℝ) (250672328421/500000000000 : ℝ) (25067538433/50000000000 : ℝ) (501350768669/1000000000000 : ℝ) (250675384311/500000000000 : ℝ) (62668846079/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 4 (25067538433/50000000000 : ℝ) (501350768669/1000000000000 : ℝ) (250675384311/500000000000 : ℝ) (62668846079/125000000000 : ℝ) (501350768641/1000000000000 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 5 (501350768641/1000000000000 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 6 (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66981/524288 : ℝ))) 7 (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66981/524288 : ℝ)) hmem 8 (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66981/524288 : ℝ))) hcmem 8 (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66981/524288 : ℝ)) (992062848419/1000000000000 : ℝ) (992062848421/1000000000000 : ℝ) (24480018/48828125 : ℝ) (501350768651/1000000000000 : ℝ) (396910310203/500000000000 : ℝ) (396910310213/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0908_exp_lower
  have heNumeric : (2054901576429/1000000000000 : ℝ)/4 ≤ Real.exp (-21314125088007/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901576429/1000000000000 : ℝ)/4 ≤ Real.exp ((16745/131072 : ℝ)-(396910310213/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16745/131072 : ℝ) (66981/524288 : ℝ) (396910310213/500000000000 : ℝ) (2054901576429/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0909; no trusted numerical premise.
theorem cover8_leaf0909_exp_radius : (6237536074763541/6250000000000000 : ℝ) ≤ Real.exp ((-33491/2097152 : ℝ)/8) ∧ Real.exp ((-33491/2097152 : ℝ)/8) ≤ (998005771962166561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33491/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0909_exp_lower : (920113450291591239/1000000000000000000 : ℝ) ≤ Real.exp ((-85256500231627/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256500231627/128000000000000 : ℝ)/8) ≤ (23002836257289781/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256500231627/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0909_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450789181/500000000000 : ℝ) ≤ 4*Real.exp (66981/524288 : ℝ)*Real.exp (-mu (radius 8 (33491/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450789181/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33491/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0909_exp_radius
  have hrNumeric : (984157087143/1000000000000 : ℝ) ≤ Real.exp (-33491/2097152 : ℝ) ∧ Real.exp (-33491/2097152 : ℝ) ≤ (123019635893/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984157087143/1000000000000 : ℝ) ≤ (radius 8 (33491/262144 : ℝ)) ∧ (radius 8 (33491/262144 : ℝ)) ≤ (123019635893/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33491/262144 : ℝ)) (984157087143/1000000000000 : ℝ) (123019635893/125000000000 : ℝ) (177298696623/1000000000000 : ℝ) (177298696629/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33491/262144 : ℝ)) (984157087143/1000000000000 : ℝ) (123019635893/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984157087143/1000000000000 : ℝ) (123019635893/125000000000 : ℝ) (992078543571/1000000000000 : ℝ) (248019635893/250000000000 : ℝ) (992046917813/1000000000000 : ℝ) (496023458907/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 1 (992078543571/1000000000000 : ℝ) (248019635893/250000000000 : ℝ) (992046917813/1000000000000 : ℝ) (496023458907/500000000000 : ℝ) (248015682673/250000000000 : ℝ) (992062730693/1000000000000 : ℝ) (198412546113/200000000000 : ℝ) (992062730567/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 2 (248015682673/250000000000 : ℝ) (992062730693/1000000000000 : ℝ) (198412546113/200000000000 : ℝ) (992062730567/1000000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 3 (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 4 (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 5 (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 6 (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33491/262144 : ℝ)) 7 (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33491/262144 : ℝ))) (177298696623/1000000000000 : ℝ) (177298696629/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177298696623/1000000000000 : ℝ) (177298696629/1000000000000 : ℝ) (588649348311/1000000000000 : ℝ) (117729869663/200000000000 : ℝ) (421068517729/1000000000000 : ℝ) (421068517737/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 1 (588649348311/1000000000000 : ℝ) (117729869663/200000000000 : ℝ) (421068517729/1000000000000 : ℝ) (421068517737/1000000000000 : ℝ) (25242946651/50000000000 : ℝ) (252429466513/500000000000 : ℝ) (248928558303/500000000000 : ℝ) (497857116613/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 2 (25242946651/50000000000 : ℝ) (252429466513/500000000000 : ℝ) (248928558303/500000000000 : ℝ) (497857116613/1000000000000 : ℝ) (501358024813/1000000000000 : ℝ) (25067901241/50000000000 : ℝ) (15667056297/31250000000 : ℝ) (501345801511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 3 (501358024813/1000000000000 : ℝ) (25067901241/50000000000 : ℝ) (15667056297/31250000000 : ℝ) (501345801511/1000000000000 : ℝ) (250675956579/500000000000 : ℝ) (250675956583/500000000000 : ℝ) (501351913121/1000000000000 : ℝ) (501351913129/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 4 (250675956579/500000000000 : ℝ) (250675956583/500000000000 : ℝ) (501351913121/1000000000000 : ℝ) (501351913129/1000000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 5 (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 6 (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33491/262144 : ℝ))) 7 (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33491/262144 : ℝ)) hmem 8 (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33491/262144 : ℝ))) hcmem 8 (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33491/262144 : ℝ)) (248015682657/250000000000 : ℝ) (99206273063/100000000000 : ℝ) (501351913139/1000000000000 : ℝ) (125337978287/250000000000 : ℝ) (793822526817/1000000000000 : ℝ) (396911263417/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0909_exp_lower
  have heNumeric : (1027450789181/500000000000 : ℝ)/4 ≤ Real.exp (-85256500231627/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450789181/500000000000 : ℝ)/4 ≤ Real.exp ((66981/524288 : ℝ)-(396911263417/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66981/524288 : ℝ) (33491/262144 : ℝ) (396911263417/500000000000 : ℝ) (1027450789181/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0910; no trusted numerical premise.
theorem cover8_leaf0910_exp_radius : (499002871109638621/500000000000000000 : ℝ) ≤ Real.exp ((-66983/4194304 : ℝ)/8) ∧ Real.exp ((-66983/4194304 : ℝ)/8) ≤ (998005742219277243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66983/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0910_exp_lower : (920113450401847607/1000000000000000000 : ℝ) ≤ Real.exp ((-42628250054461/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250054461/64000000000000 : ℝ)/8) ≤ (115014181300230951/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250054461/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0910_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725395083/250000000000 : ℝ) ≤ 4*Real.exp (33491/262144 : ℝ)*Real.exp (-mu (radius 8 (66983/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725395083/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66983/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0910_exp_radius
  have hrNumeric : (492078426251/500000000000 : ℝ) ≤ Real.exp (-66983/4194304 : ℝ) ∧ Real.exp (-66983/4194304 : ℝ) ≤ (984156852503/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492078426251/500000000000 : ℝ) ≤ (radius 8 (66983/524288 : ℝ)) ∧ (radius 8 (66983/524288 : ℝ)) ≤ (984156852503/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66983/524288 : ℝ)) (492078426251/500000000000 : ℝ) (984156852503/1000000000000 : ℝ) (177299999073/1000000000000 : ℝ) (177299999079/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66983/524288 : ℝ)) (492078426251/500000000000 : ℝ) (984156852503/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492078426251/500000000000 : ℝ) (984156852503/1000000000000 : ℝ) (992078426251/1000000000000 : ℝ) (248019606563/250000000000 : ℝ) (15500731243/15625000000 : ℝ) (992046799553/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 1 (992078426251/1000000000000 : ℝ) (248019606563/250000000000 : ℝ) (15500731243/15625000000 : ℝ) (992046799553/1000000000000 : ℝ) (992062612901/1000000000000 : ℝ) (992062612903/1000000000000 : ℝ) (39682504511/40000000000 : ℝ) (992062612777/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 2 (992062612901/1000000000000 : ℝ) (992062612903/1000000000000 : ℝ) (39682504511/40000000000 : ℝ) (992062612777/1000000000000 : ℝ) (496031306419/500000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 3 (496031306419/500000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 4 (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 5 (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 6 (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66983/524288 : ℝ)) 7 (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66983/524288 : ℝ))) (177299999073/1000000000000 : ℝ) (177299999079/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177299999073/1000000000000 : ℝ) (177299999079/1000000000000 : ℝ) (36790624971/62500000000 : ℝ) (29432499977/50000000000 : ℝ) (421070064327/1000000000000 : ℝ) (84214012867/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 1 (36790624971/62500000000 : ℝ) (29432499977/50000000000 : ℝ) (421070064327/1000000000000 : ℝ) (84214012867/200000000000 : ℝ) (504860031931/1000000000000 : ℝ) (252430015969/500000000000 : ℝ) (248929153159/500000000000 : ℝ) (248929153163/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 2 (504860031931/1000000000000 : ℝ) (252430015969/500000000000 : ℝ) (248929153159/500000000000 : ℝ) (248929153163/500000000000 : ℝ) (125339792281/250000000000 : ℝ) (125339792283/250000000000 : ℝ) (6266836827/12500000000 : ℝ) (501346946169/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 3 (125339792281/250000000000 : ℝ) (125339792283/250000000000 : ℝ) (6266836827/12500000000 : ℝ) (501346946169/1000000000000 : ℝ) (250676528821/500000000000 : ℝ) (501353057651/1000000000000 : ℝ) (125338264401/250000000000 : ℝ) (250676528807/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 4 (250676528821/500000000000 : ℝ) (501353057651/1000000000000 : ℝ) (125338264401/250000000000 : ℝ) (250676528807/500000000000 : ℝ) (501353057623/1000000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 5 (501353057623/1000000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 6 (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66983/524288 : ℝ))) 7 (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66983/524288 : ℝ)) hmem 8 (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66983/524288 : ℝ))) hcmem 8 (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66983/524288 : ℝ)) (992062612837/1000000000000 : ℝ) (24801565321/25000000000 : ℝ) (250676528811/500000000000 : ℝ) (501353057633/1000000000000 : ℝ) (793824433203/1000000000000 : ℝ) (99228054153/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0910_exp_lower
  have heNumeric : (513725395083/250000000000 : ℝ)/4 ≤ Real.exp (-42628250054461/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725395083/250000000000 : ℝ)/4 ≤ Real.exp ((33491/262144 : ℝ)-(99228054153/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33491/262144 : ℝ) (66983/524288 : ℝ) (99228054153/125000000000 : ℝ) (513725395083/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0911; no trusted numerical premise.
theorem cover8_leaf0911_exp_radius : (998005712476388811/1000000000000000000 : ℝ) ≤ Real.exp ((-8373/524288 : ℝ)/8) ∧ Real.exp ((-8373/524288 : ℝ)/8) ≤ (249501428119097203/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8373/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0911_exp_lower : (920113450513599159/1000000000000000000 : ℝ) ≤ Real.exp ((-85256499984553/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256499984553/128000000000000 : ℝ)/8) ≤ (23002836262839979/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256499984553/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0911_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862697791/125000000000 : ℝ) ≤ 4*Real.exp (66983/524288 : ℝ)*Real.exp (-mu (radius 8 (8373/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (256862697791/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8373/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0911_exp_radius
  have hrNumeric : (49207830893/50000000000 : ℝ) ≤ Real.exp (-8373/524288 : ℝ) ∧ Real.exp (-8373/524288 : ℝ) ≤ (984156617861/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49207830893/50000000000 : ℝ) ≤ (radius 8 (8373/65536 : ℝ)) ∧ (radius 8 (8373/65536 : ℝ)) ≤ (984156617861/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8373/65536 : ℝ)) (49207830893/50000000000 : ℝ) (984156617861/1000000000000 : ℝ) (177301301519/1000000000000 : ℝ) (7092052061/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8373/65536 : ℝ)) (49207830893/50000000000 : ℝ) (984156617861/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49207830893/50000000000 : ℝ) (984156617861/1000000000000 : ℝ) (99207830893/100000000000 : ℝ) (992078308931/1000000000000 : ℝ) (99204668129/100000000000 : ℝ) (248011670323/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 1 (99207830893/100000000000 : ℝ) (992078308931/1000000000000 : ℝ) (99204668129/100000000000 : ℝ) (248011670323/250000000000 : ℝ) (99206249511/100000000000 : ℝ) (124007811889/125000000000 : ℝ) (992062494983/1000000000000 : ℝ) (496031247493/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 2 (99206249511/100000000000 : ℝ) (124007811889/125000000000 : ℝ) (992062494983/1000000000000 : ℝ) (496031247493/500000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 3 (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 4 (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 5 (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 6 (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8373/65536 : ℝ)) 7 (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8373/65536 : ℝ))) (177301301519/1000000000000 : ℝ) (7092052061/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177301301519/1000000000000 : ℝ) (7092052061/40000000000 : ℝ) (588650650759/1000000000000 : ℝ) (588650650763/1000000000000 : ℝ) (84214322183/200000000000 : ℝ) (421071610923/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 1 (588650650759/1000000000000 : ℝ) (588650650763/1000000000000 : ℝ) (84214322183/200000000000 : ℝ) (421071610923/1000000000000 : ℝ) (504861130837/1000000000000 : ℝ) (504861130843/1000000000000 : ℝ) (497859496023/1000000000000 : ℝ) (497859496031/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 2 (504861130837/1000000000000 : ℝ) (504861130843/1000000000000 : ℝ) (497859496023/1000000000000 : ℝ) (497859496031/1000000000000 : ℝ) (50136031343/100000000000 : ℝ) (501360313437/1000000000000 : ℝ) (501348090811/1000000000000 : ℝ) (501348090819/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 3 (50136031343/100000000000 : ℝ) (501360313437/1000000000000 : ℝ) (501348090811/1000000000000 : ℝ) (501348090819/1000000000000 : ℝ) (12533855053/25000000000 : ℝ) (31334637633/62500000000 : ℝ) (501354202083/1000000000000 : ℝ) (501354202091/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 4 (12533855053/25000000000 : ℝ) (31334637633/62500000000 : ℝ) (501354202083/1000000000000 : ℝ) (501354202091/1000000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 5 (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 6 (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8373/65536 : ℝ))) 7 (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8373/65536 : ℝ)) hmem 8 (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8373/65536 : ℝ))) hcmem 8 (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8373/65536 : ℝ)) (496031247523/500000000000 : ℝ) (992062495049/1000000000000 : ℝ) (501354202101/1000000000000 : ℝ) (50135420211/100000000000 : ℝ) (3100884139/3906250000 : ℝ) (793826339601/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0911_exp_lower
  have heNumeric : (256862697791/125000000000 : ℝ)/4 ≤ Real.exp (-85256499984553/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862697791/125000000000 : ℝ)/4 ≤ Real.exp ((66983/524288 : ℝ)-(793826339601/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66983/524288 : ℝ) (8373/65536 : ℝ) (793826339601/1000000000000 : ℝ) (256862697791/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0912; no trusted numerical premise.
theorem cover8_leaf0912_exp_radius : (998005682733501267/1000000000000000000 : ℝ) ≤ Real.exp ((-66985/4194304 : ℝ)/8) ∧ Real.exp ((-66985/4194304 : ℝ)/8) ≤ (249501420683375317/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66985/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0912_exp_lower : (230028362657027763/250000000000000000 : ℝ) ≤ Real.exp ((-10657062482139/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062482139/16000000000000 : ℝ)/8) ≤ (920113450628111053/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062482139/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0912_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450792187/500000000000 : ℝ) ≤ 4*Real.exp (8373/65536 : ℝ)*Real.exp (-mu (radius 8 (66985/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450792187/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66985/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0912_exp_radius
  have hrNumeric : (984156383219/1000000000000 : ℝ) ≤ Real.exp (-66985/4194304 : ℝ) ∧ Real.exp (-66985/4194304 : ℝ) ≤ (49207819161/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984156383219/1000000000000 : ℝ) ≤ (radius 8 (66985/524288 : ℝ)) ∧ (radius 8 (66985/524288 : ℝ)) ≤ (49207819161/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66985/524288 : ℝ)) (984156383219/1000000000000 : ℝ) (49207819161/50000000000 : ℝ) (177302603949/1000000000000 : ℝ) (44325650989/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66985/524288 : ℝ)) (984156383219/1000000000000 : ℝ) (49207819161/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984156383219/1000000000000 : ℝ) (49207819161/50000000000 : ℝ) (992078191609/1000000000000 : ℝ) (99207819161/100000000000 : ℝ) (992046563029/1000000000000 : ℝ) (992046563031/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 1 (992078191609/1000000000000 : ℝ) (99207819161/100000000000 : ℝ) (992046563029/1000000000000 : ℝ) (992046563031/1000000000000 : ℝ) (992062377319/1000000000000 : ℝ) (992062377321/1000000000000 : ℝ) (124007797149/125000000000 : ℝ) (198412475439/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 2 (992062377319/1000000000000 : ℝ) (992062377321/1000000000000 : ℝ) (124007797149/125000000000 : ℝ) (198412475439/200000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 3 (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 4 (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 5 (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 6 (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66985/524288 : ℝ)) 7 (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66985/524288 : ℝ))) (177302603949/1000000000000 : ℝ) (44325650989/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177302603949/1000000000000 : ℝ) (44325650989/250000000000 : ℝ) (294325650987/500000000000 : ℝ) (294325650989/500000000000 : ℝ) (210536578739/500000000000 : ℝ) (421073157487/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 1 (294325650987/500000000000 : ℝ) (294325650989/500000000000 : ℝ) (210536578739/500000000000 : ℝ) (421073157487/1000000000000 : ℝ) (252431114863/500000000000 : ℝ) (504862229733/1000000000000 : ℝ) (49786068571/100000000000 : ℝ) (248930342859/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 2 (252431114863/500000000000 : ℝ) (504862229733/1000000000000 : ℝ) (49786068571/100000000000 : ℝ) (248930342859/500000000000 : ℝ) (250680728859/500000000000 : ℝ) (250680728863/500000000000 : ℝ) (125337308861/250000000000 : ℝ) (125337308863/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 3 (250680728859/500000000000 : ℝ) (250680728863/500000000000 : ℝ) (125337308861/250000000000 : ℝ) (125337308863/250000000000 : ℝ) (501355346581/1000000000000 : ℝ) (501355346589/1000000000000 : ℝ) (501355346543/1000000000000 : ℝ) (62669418319/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 4 (501355346581/1000000000000 : ℝ) (501355346589/1000000000000 : ℝ) (501355346543/1000000000000 : ℝ) (62669418319/125000000000 : ℝ) (250677673281/500000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 5 (250677673281/500000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 6 (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66985/524288 : ℝ))) 7 (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66985/524288 : ℝ)) hmem 8 (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66985/524288 : ℝ))) hcmem 8 (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66985/524288 : ℝ)) (198412475451/200000000000 : ℝ) (496031188629/500000000000 : ℝ) (501355346561/1000000000000 : ℝ) (501355346571/1000000000000 : ℝ) (158765649187/200000000000 : ℝ) (396914122977/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0912_exp_lower
  have heNumeric : (1027450792187/500000000000 : ℝ)/4 ≤ Real.exp (-10657062482139/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450792187/500000000000 : ℝ)/4 ≤ Real.exp ((8373/65536 : ℝ)-(396914122977/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8373/65536 : ℝ) (66985/524288 : ℝ) (396914122977/500000000000 : ℝ) (1027450792187/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0913; no trusted numerical premise.
theorem cover8_leaf0913_exp_radius : (62375353311913413/62500000000000000 : ℝ) ≤ Real.exp ((-33493/2097152 : ℝ)/8) ∧ Real.exp ((-33493/2097152 : ℝ)/8) ≤ (998005652990614609/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33493/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0913_exp_lower : (920113450745038243/1000000000000000000 : ℝ) ≤ Real.exp ((-85256499726983/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256499726983/128000000000000 : ℝ)/8) ≤ (230028362686259561/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256499726983/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0913_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901586463/1000000000000 : ℝ) ≤ 4*Real.exp (66985/524288 : ℝ)*Real.exp (-mu (radius 8 (33493/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901586463/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33493/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0913_exp_radius
  have hrNumeric : (492078074289/500000000000 : ℝ) ≤ Real.exp (-33493/2097152 : ℝ) ∧ Real.exp (-33493/2097152 : ℝ) ≤ (984156148579/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492078074289/500000000000 : ℝ) ≤ (radius 8 (33493/262144 : ℝ)) ∧ (radius 8 (33493/262144 : ℝ)) ≤ (984156148579/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33493/262144 : ℝ)) (492078074289/500000000000 : ℝ) (984156148579/1000000000000 : ℝ) (17730390637/100000000000 : ℝ) (22162988297/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33493/262144 : ℝ)) (492078074289/500000000000 : ℝ) (984156148579/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492078074289/500000000000 : ℝ) (984156148579/1000000000000 : ℝ) (992078074289/1000000000000 : ℝ) (99207807429/100000000000 : ℝ) (31001451399/31250000000 : ℝ) (99204644477/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 1 (992078074289/1000000000000 : ℝ) (99207807429/100000000000 : ℝ) (31001451399/31250000000 : ℝ) (99204644477/100000000000 : ℝ) (124007782441/125000000000 : ℝ) (99206225953/100000000000 : ℝ) (496031129701/500000000000 : ℝ) (248015564851/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 2 (124007782441/125000000000 : ℝ) (99206225953/100000000000 : ℝ) (496031129701/500000000000 : ℝ) (248015564851/250000000000 : ℝ) (198412451893/200000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 3 (198412451893/200000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 4 (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 5 (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 6 (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33493/262144 : ℝ)) 7 (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33493/262144 : ℝ))) (17730390637/100000000000 : ℝ) (22162988297/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17730390637/100000000000 : ℝ) (22162988297/125000000000 : ℝ) (117730390637/200000000000 : ℝ) (147162988297/250000000000 : ℝ) (16842988161/40000000000 : ℝ) (421074704033/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 1 (117730390637/200000000000 : ℝ) (147162988297/250000000000 : ℝ) (16842988161/40000000000 : ℝ) (421074704033/1000000000000 : ℝ) (100972665721/200000000000 : ℝ) (504863328611/1000000000000 : ℝ) (62232734423/125000000000 : ℝ) (497861875391/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 2 (100972665721/200000000000 : ℝ) (504863328611/1000000000000 : ℝ) (62232734423/125000000000 : ℝ) (497861875391/1000000000000 : ℝ) (250681300997/500000000000 : ℝ) (501362602001/1000000000000 : ℝ) (100270076013/200000000000 : ℝ) (501350380073/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 3 (250681300997/500000000000 : ℝ) (501362602001/1000000000000 : ℝ) (100270076013/200000000000 : ℝ) (501350380073/1000000000000 : ℝ) (501356491029/1000000000000 : ℝ) (501356491037/1000000000000 : ℝ) (31334780687/62500000000 : ℝ) (501356491/1000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 4 (501356491029/1000000000000 : ℝ) (501356491037/1000000000000 : ℝ) (31334780687/62500000000 : ℝ) (501356491/1000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 5 (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 6 (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33493/262144 : ℝ))) 7 (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33493/262144 : ℝ)) hmem 8 (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33493/262144 : ℝ))) hcmem 8 (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33493/262144 : ℝ)) (124007782433/125000000000 : ℝ) (992062259467/1000000000000 : ℝ) (50135649101/100000000000 : ℝ) (501356491019/1000000000000 : ℝ) (793830152269/1000000000000 : ℝ) (396915076143/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0913_exp_lower
  have heNumeric : (2054901586463/1000000000000 : ℝ)/4 ≤ Real.exp (-85256499726983/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901586463/1000000000000 : ℝ)/4 ≤ Real.exp ((66985/524288 : ℝ)-(396915076143/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66985/524288 : ℝ) (33493/262144 : ℝ) (396915076143/500000000000 : ℝ) (2054901586463/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0914; no trusted numerical premise.
theorem cover8_leaf0914_exp_radius : (249501405811932209/250000000000000000 : ℝ) ≤ Real.exp ((-66987/4194304 : ℝ)/8) ∧ Real.exp ((-66987/4194304 : ℝ)/8) ≤ (998005623247728837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66987/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0914_exp_lower : (920113450864035689/1000000000000000000 : ℝ) ≤ Real.exp ((-1705129991891/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705129991891/2560000000000 : ℝ)/8) ≤ (92011345086403569/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705129991891/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0914_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901588589/1000000000000 : ℝ) ≤ 4*Real.exp (33493/262144 : ℝ)*Real.exp (-mu (radius 8 (66987/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901588589/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66987/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0914_exp_radius
  have hrNumeric : (984155913937/1000000000000 : ℝ) ≤ Real.exp (-66987/4194304 : ℝ) ∧ Real.exp (-66987/4194304 : ℝ) ≤ (492077956969/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984155913937/1000000000000 : ℝ) ≤ (radius 8 (66987/524288 : ℝ)) ∧ (radius 8 (66987/524288 : ℝ)) ≤ (492077956969/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66987/524288 : ℝ)) (984155913937/1000000000000 : ℝ) (492077956969/500000000000 : ℝ) (8865260439/50000000000 : ℝ) (177305208787/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66987/524288 : ℝ)) (984155913937/1000000000000 : ℝ) (492077956969/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984155913937/1000000000000 : ℝ) (492077956969/500000000000 : ℝ) (124009744621/125000000000 : ℝ) (992077956969/1000000000000 : ℝ) (992046326507/1000000000000 : ℝ) (248011581627/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 1 (124009744621/125000000000 : ℝ) (992077956969/1000000000000 : ℝ) (992046326507/1000000000000 : ℝ) (248011581627/250000000000 : ℝ) (992062141737/1000000000000 : ℝ) (992062141739/1000000000000 : ℝ) (992062141611/1000000000000 : ℝ) (992062141613/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 2 (992062141737/1000000000000 : ℝ) (992062141739/1000000000000 : ℝ) (992062141611/1000000000000 : ℝ) (992062141613/1000000000000 : ℝ) (496031070837/500000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 3 (496031070837/500000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 4 (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 5 (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 6 (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66987/524288 : ℝ)) 7 (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66987/524288 : ℝ))) (8865260439/50000000000 : ℝ) (177305208787/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8865260439/50000000000 : ℝ) (177305208787/1000000000000 : ℝ) (58865260439/100000000000 : ℝ) (294326302197/500000000000 : ℝ) (421076250553/1000000000000 : ℝ) (210538125281/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 1 (58865260439/100000000000 : ℝ) (294326302197/500000000000 : ℝ) (421076250553/1000000000000 : ℝ) (210538125281/500000000000 : ℝ) (504864427471/1000000000000 : ℝ) (252432213739/500000000000 : ℝ) (497863065043/1000000000000 : ℝ) (497863065051/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 2 (504864427471/1000000000000 : ℝ) (252432213739/500000000000 : ℝ) (497863065043/1000000000000 : ℝ) (497863065051/1000000000000 : ℝ) (501363746257/1000000000000 : ℝ) (100272749253/200000000000 : ℝ) (7833617573/15625000000 : ℝ) (501351524681/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 3 (501363746257/1000000000000 : ℝ) (100272749253/200000000000 : ℝ) (7833617573/15625000000 : ℝ) (501351524681/1000000000000 : ℝ) (62669704433/125000000000 : ℝ) (501357635473/1000000000000 : ℝ) (501357635427/1000000000000 : ℝ) (125339408859/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 4 (62669704433/125000000000 : ℝ) (501357635473/1000000000000 : ℝ) (501357635427/1000000000000 : ℝ) (125339408859/250000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 5 (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 6 (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66987/524288 : ℝ))) 7 (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66987/524288 : ℝ)) hmem 8 (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66987/524288 : ℝ))) hcmem 8 (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66987/524288 : ℝ)) (992062141673/1000000000000 : ℝ) (248015535419/250000000000 : ℝ) (100271527089/200000000000 : ℝ) (100271527091/200000000000 : ℝ) (793832058581/1000000000000 : ℝ) (3969160293/5000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0914_exp_lower
  have heNumeric : (2054901588589/1000000000000 : ℝ)/4 ≤ Real.exp (-1705129991891/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901588589/1000000000000 : ℝ)/4 ≤ Real.exp ((33493/262144 : ℝ)-(3969160293/5000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33493/262144 : ℝ) (66987/524288 : ℝ) (3969160293/5000000000 : ℝ) (2054901588589/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0915; no trusted numerical premise.
theorem cover8_leaf0915_exp_radius : (998005593504843951/1000000000000000000 : ℝ) ≤ Real.exp ((-16747/1048576 : ℝ)/8) ∧ Real.exp ((-16747/1048576 : ℝ)/8) ≤ (62375349594052747/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16747/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0915_exp_lower : (230028362746304601/250000000000000000 : ℝ) ≤ Real.exp ((-17051299891937/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051299891937/25600000000000 : ℝ)/8) ≤ (184022690197043681/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051299891937/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0915_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980318151/200000000000 : ℝ) ≤ 4*Real.exp (66987/524288 : ℝ)*Real.exp (-mu (radius 8 (16747/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980318151/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16747/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0915_exp_radius
  have hrNumeric : (15377432489/15625000000 : ℝ) ≤ Real.exp (-16747/1048576 : ℝ) ∧ Real.exp (-16747/1048576 : ℝ) ≤ (984155679297/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15377432489/15625000000 : ℝ) ≤ (radius 8 (16747/131072 : ℝ)) ∧ (radius 8 (16747/131072 : ℝ)) ≤ (984155679297/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16747/131072 : ℝ)) (15377432489/15625000000 : ℝ) (984155679297/1000000000000 : ℝ) (177306511181/1000000000000 : ℝ) (44326627797/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16747/131072 : ℝ)) (15377432489/15625000000 : ℝ) (984155679297/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15377432489/15625000000 : ℝ) (984155679297/1000000000000 : ℝ) (31002432489/31250000000 : ℝ) (992077839649/1000000000000 : ℝ) (496023104123/500000000000 : ℝ) (992046208247/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 1 (31002432489/31250000000 : ℝ) (992077839649/1000000000000 : ℝ) (496023104123/500000000000 : ℝ) (992046208247/1000000000000 : ℝ) (992062023947/1000000000000 : ℝ) (248015505987/250000000000 : ℝ) (49603101191/50000000000 : ℝ) (496031011911/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 2 (992062023947/1000000000000 : ℝ) (248015505987/250000000000 : ℝ) (49603101191/50000000000 : ℝ) (496031011911/500000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 3 (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 4 (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 5 (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 6 (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16747/131072 : ℝ)) 7 (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16747/131072 : ℝ))) (177306511181/1000000000000 : ℝ) (44326627797/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177306511181/1000000000000 : ℝ) (44326627797/250000000000 : ℝ) (58865325559/100000000000 : ℝ) (294326627797/500000000000 : ℝ) (52634724633/125000000000 : ℝ) (210538898537/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 1 (58865325559/100000000000 : ℝ) (294326627797/500000000000 : ℝ) (52634724633/125000000000 : ℝ) (210538898537/500000000000 : ℝ) (504865526327/1000000000000 : ℝ) (252432763167/500000000000 : ℝ) (49786425469/100000000000 : ℝ) (248932127349/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 2 (504865526327/1000000000000 : ℝ) (252432763167/500000000000 : ℝ) (49786425469/100000000000 : ℝ) (248932127349/500000000000 : ℝ) (125341222627/250000000000 : ℝ) (125341222629/250000000000 : ℝ) (501352669269/1000000000000 : ℝ) (501352669277/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 3 (125341222627/250000000000 : ℝ) (125341222629/250000000000 : ℝ) (501352669269/1000000000000 : ℝ) (501352669277/1000000000000 : ℝ) (31334923743/62500000000 : ℝ) (501358779897/1000000000000 : ℝ) (501358779851/1000000000000 : ℝ) (25067938993/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 4 (31334923743/62500000000 : ℝ) (501358779897/1000000000000 : ℝ) (501358779851/1000000000000 : ℝ) (25067938993/50000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 5 (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 6 (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16747/131072 : ℝ))) 7 (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16747/131072 : ℝ)) hmem 8 (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16747/131072 : ℝ))) hcmem 8 (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16747/131072 : ℝ)) (992062023883/1000000000000 : ℝ) (198412404777/200000000000 : ℝ) (501358779869/1000000000000 : ℝ) (501358779879/1000000000000 : ℝ) (793833964877/1000000000000 : ℝ) (158766792979/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0915_exp_lower
  have heNumeric : (410980318151/200000000000 : ℝ)/4 ≤ Real.exp (-17051299891937/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980318151/200000000000 : ℝ)/4 ≤ Real.exp ((66987/524288 : ℝ)-(158766792979/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66987/524288 : ℝ) (16747/131072 : ℝ) (158766792979/200000000000 : ℝ) (410980318151/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0916; no trusted numerical premise.
theorem cover8_leaf0916_exp_radius : (998005563761959951/1000000000000000000 : ℝ) ≤ Real.exp ((-66989/4194304 : ℝ)/8) ∧ Real.exp ((-66989/4194304 : ℝ)/8) ≤ (62375347735122497/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66989/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0916_exp_lower : (7360907608867771/8000000000000000 : ℝ) ≤ Real.exp ((-21314124830629/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314124830629/32000000000000 : ℝ)/8) ≤ (57507090694279461/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314124830629/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0916_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901592957/1000000000000 : ℝ) ≤ 4*Real.exp (16747/131072 : ℝ)*Real.exp (-mu (radius 8 (66989/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901592957/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66989/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0916_exp_radius
  have hrNumeric : (196831088931/200000000000 : ℝ) ≤ Real.exp (-66989/4194304 : ℝ) ∧ Real.exp (-66989/4194304 : ℝ) ≤ (61509715291/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196831088931/200000000000 : ℝ) ≤ (radius 8 (66989/524288 : ℝ)) ∧ (radius 8 (66989/524288 : ℝ)) ≤ (61509715291/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66989/524288 : ℝ)) (196831088931/200000000000 : ℝ) (61509715291/62500000000 : ℝ) (44326953393/250000000000 : ℝ) (177307813579/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66989/524288 : ℝ)) (196831088931/200000000000 : ℝ) (61509715291/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196831088931/200000000000 : ℝ) (61509715291/62500000000 : ℝ) (992077722327/1000000000000 : ℝ) (124009715291/125000000000 : ℝ) (198409217997/200000000000 : ℝ) (496023044993/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 1 (992077722327/1000000000000 : ℝ) (124009715291/125000000000 : ℝ) (198409217997/200000000000 : ℝ) (496023044993/500000000000 : ℝ) (248015476539/250000000000 : ℝ) (992061906157/1000000000000 : ℝ) (992061906029/1000000000000 : ℝ) (992061906031/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 2 (248015476539/250000000000 : ℝ) (992061906157/1000000000000 : ℝ) (992061906029/1000000000000 : ℝ) (992061906031/1000000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 3 (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 4 (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 5 (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 6 (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66989/524288 : ℝ)) 7 (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66989/524288 : ℝ))) (44326953393/250000000000 : ℝ) (177307813579/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44326953393/250000000000 : ℝ) (177307813579/1000000000000 : ℝ) (294326953393/500000000000 : ℝ) (58865390679/100000000000 : ℝ) (210539671779/500000000000 : ℝ) (26317458973/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 1 (294326953393/500000000000 : ℝ) (58865390679/100000000000 : ℝ) (210539671779/500000000000 : ℝ) (26317458973/62500000000 : ℝ) (126216656293/250000000000 : ℝ) (504866625179/1000000000000 : ℝ) (124466361081/250000000000 : ℝ) (124466361083/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 2 (126216656293/250000000000 : ℝ) (504866625179/1000000000000 : ℝ) (124466361081/250000000000 : ℝ) (124466361083/250000000000 : ℝ) (125341508687/250000000000 : ℝ) (125341508689/250000000000 : ℝ) (501353813853/1000000000000 : ℝ) (250676906931/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 3 (125341508687/250000000000 : ℝ) (125341508689/250000000000 : ℝ) (501353813853/1000000000000 : ℝ) (250676906931/500000000000 : ℝ) (5013599243/10000000000 : ℝ) (501359924309/1000000000000 : ℝ) (501359924263/1000000000000 : ℝ) (31334995267/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 4 (5013599243/10000000000 : ℝ) (501359924309/1000000000000 : ℝ) (501359924263/1000000000000 : ℝ) (31334995267/62500000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 5 (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 6 (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66989/524288 : ℝ))) 7 (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66989/524288 : ℝ)) hmem 8 (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66989/524288 : ℝ))) hcmem 8 (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66989/524288 : ℝ)) (248015476523/250000000000 : ℝ) (496030953047/500000000000 : ℝ) (501359924281/1000000000000 : ℝ) (501359924291/1000000000000 : ℝ) (793835871153/1000000000000 : ℝ) (198458967793/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0916_exp_lower
  have heNumeric : (2054901592957/1000000000000 : ℝ)/4 ≤ Real.exp (-21314124830629/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901592957/1000000000000 : ℝ)/4 ≤ Real.exp ((16747/131072 : ℝ)-(198458967793/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16747/131072 : ℝ) (66989/524288 : ℝ) (198458967793/250000000000 : ℝ) (2054901592957/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0917; no trusted numerical premise.
theorem cover8_leaf0917_exp_radius : (998005534019076839/1000000000000000000 : ℝ) ≤ Real.exp ((-33495/2097152 : ℝ)/8) ∧ Real.exp ((-33495/2097152 : ℝ)/8) ≤ (24950138350476921/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33495/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0917_exp_lower : (920113451234024629/1000000000000000000 : ℝ) ≤ Real.exp ((-85256499182787/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256499182787/128000000000000 : ℝ)/8) ≤ (92011345123402463/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256499182787/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0917_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1284313497/625000000 : ℝ) ≤ 4*Real.exp (66989/524288 : ℝ)*Real.exp (-mu (radius 8 (33495/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1284313497/625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33495/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0917_exp_radius
  have hrNumeric : (492077605007/500000000000 : ℝ) ≤ Real.exp (-33495/2097152 : ℝ) ∧ Real.exp (-33495/2097152 : ℝ) ≤ (196831042003/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492077605007/500000000000 : ℝ) ≤ (radius 8 (33495/262144 : ℝ)) ∧ (radius 8 (33495/262144 : ℝ)) ≤ (196831042003/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33495/262144 : ℝ)) (492077605007/500000000000 : ℝ) (196831042003/200000000000 : ℝ) (177309115953/1000000000000 : ℝ) (4432727899/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33495/262144 : ℝ)) (492077605007/500000000000 : ℝ) (196831042003/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492077605007/500000000000 : ℝ) (196831042003/200000000000 : ℝ) (992077605007/1000000000000 : ℝ) (62004850313/62500000000 : ℝ) (248011492931/250000000000 : ℝ) (39681838869/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 1 (992077605007/1000000000000 : ℝ) (62004850313/62500000000 : ℝ) (248011492931/250000000000 : ℝ) (39681838869/40000000000 : ℝ) (198412357673/200000000000 : ℝ) (992061788367/1000000000000 : ℝ) (992061788239/1000000000000 : ℝ) (992061788241/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 2 (198412357673/200000000000 : ℝ) (992061788367/1000000000000 : ℝ) (992061788239/1000000000000 : ℝ) (992061788241/1000000000000 : ℝ) (496030894151/500000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 3 (496030894151/500000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 4 (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 5 (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 6 (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33495/262144 : ℝ)) 7 (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33495/262144 : ℝ))) (177309115953/1000000000000 : ℝ) (4432727899/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177309115953/1000000000000 : ℝ) (4432727899/25000000000 : ℝ) (73581819747/125000000000 : ℝ) (29432727899/50000000000 : ℝ) (84216178007/200000000000 : ℝ) (105270222511/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 1 (73581819747/125000000000 : ℝ) (29432727899/50000000000 : ℝ) (84216178007/200000000000 : ℝ) (105270222511/250000000000 : ℝ) (100973544801/200000000000 : ℝ) (126216931003/250000000000 : ℝ) (62233329243/125000000000 : ℝ) (15558332311/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 2 (100973544801/200000000000 : ℝ) (126216931003/250000000000 : ℝ) (62233329243/125000000000 : ℝ) (15558332311/31250000000 : ℝ) (250683589487/500000000000 : ℝ) (250683589491/500000000000 : ℝ) (20054198337/40000000000 : ℝ) (501354958433/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 3 (250683589487/500000000000 : ℝ) (250683589491/500000000000 : ℝ) (20054198337/40000000000 : ℝ) (501354958433/1000000000000 : ℝ) (501361068699/1000000000000 : ℝ) (125340267177/250000000000 : ℝ) (250680534331/500000000000 : ℝ) (501361068671/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 4 (501361068699/1000000000000 : ℝ) (125340267177/250000000000 : ℝ) (250680534331/500000000000 : ℝ) (501361068671/1000000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 5 (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 6 (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33495/262144 : ℝ))) 7 (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33495/262144 : ℝ)) hmem 8 (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33495/262144 : ℝ))) hcmem 8 (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33495/262144 : ℝ)) (992061788301/1000000000000 : ℝ) (62003861769/62500000000 : ℝ) (12534026717/25000000000 : ℝ) (50136106869/100000000000 : ℝ) (793837777409/1000000000000 : ℝ) (793837777429/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0917_exp_lower
  have heNumeric : (1284313497/625000000 : ℝ)/4 ≤ Real.exp (-85256499182787/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1284313497/625000000 : ℝ)/4 ≤ Real.exp ((66989/524288 : ℝ)-(793837777429/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66989/524288 : ℝ) (33495/262144 : ℝ) (793837777429/1000000000000 : ℝ) (1284313497/625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0918; no trusted numerical premise.
theorem cover8_leaf0918_exp_radius : (249501376069048653/250000000000000000 : ℝ) ≤ Real.exp ((-66991/4194304 : ℝ)/8) ∧ Real.exp ((-66991/4194304 : ℝ)/8) ≤ (998005504276194613/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66991/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0918_exp_lower : (920113451361648139/1000000000000000000 : ℝ) ≤ Real.exp ((-42628249520377/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628249520377/64000000000000 : ℝ)/8) ≤ (46005672568082407/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628249520377/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0918_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372539937/25000000000 : ℝ) ≤ 4*Real.exp (33495/262144 : ℝ)*Real.exp (-mu (radius 8 (66991/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (51372539937/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66991/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0918_exp_radius
  have hrNumeric : (984154975373/1000000000000 : ℝ) ≤ Real.exp (-66991/4194304 : ℝ) ∧ Real.exp (-66991/4194304 : ℝ) ≤ (492077487687/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984154975373/1000000000000 : ℝ) ≤ (radius 8 (66991/524288 : ℝ)) ∧ (radius 8 (66991/524288 : ℝ)) ≤ (492077487687/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66991/524288 : ℝ)) (984154975373/1000000000000 : ℝ) (492077487687/500000000000 : ℝ) (7092416733/40000000000 : ℝ) (177310418331/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66991/524288 : ℝ)) (984154975373/1000000000000 : ℝ) (492077487687/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984154975373/1000000000000 : ℝ) (492077487687/500000000000 : ℝ) (496038743843/500000000000 : ℝ) (992077487687/1000000000000 : ℝ) (496022926731/500000000000 : ℝ) (124005731683/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 1 (496038743843/500000000000 : ℝ) (992077487687/1000000000000 : ℝ) (496022926731/500000000000 : ℝ) (124005731683/125000000000 : ℝ) (496030835287/500000000000 : ℝ) (62003854411/62500000000 : ℝ) (992061670447/1000000000000 : ℝ) (19841233409/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 2 (496030835287/500000000000 : ℝ) (62003854411/62500000000 : ℝ) (992061670447/1000000000000 : ℝ) (19841233409/20000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 3 (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 4 (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 5 (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 6 (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66991/524288 : ℝ)) 7 (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66991/524288 : ℝ))) (7092416733/40000000000 : ℝ) (177310418331/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7092416733/40000000000 : ℝ) (177310418331/1000000000000 : ℝ) (294327604581/500000000000 : ℝ) (294327604583/500000000000 : ℝ) (84216487299/200000000000 : ℝ) (421082436503/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 1 (294327604581/500000000000 : ℝ) (294327604583/500000000000 : ℝ) (84216487299/200000000000 : ℝ) (421082436503/1000000000000 : ℝ) (126217205707/250000000000 : ℝ) (100973764567/200000000000 : ℝ) (497867823553/1000000000000 : ℝ) (12446695589/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 2 (126217205707/250000000000 : ℝ) (100973764567/200000000000 : ℝ) (497867823553/1000000000000 : ℝ) (12446695589/25000000000 : ℝ) (50136832319/100000000000 : ℝ) (250684161599/500000000000 : ℝ) (100271220597/200000000000 : ℝ) (501356102993/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 3 (50136832319/100000000000 : ℝ) (250684161599/500000000000 : ℝ) (100271220597/200000000000 : ℝ) (501356102993/1000000000000 : ℝ) (501362213087/1000000000000 : ℝ) (62670276637/125000000000 : ℝ) (10027244261/20000000000 : ℝ) (501362213059/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 4 (501362213087/1000000000000 : ℝ) (62670276637/125000000000 : ℝ) (10027244261/20000000000 : ℝ) (501362213059/1000000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 5 (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 6 (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66991/524288 : ℝ))) 7 (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66991/524288 : ℝ)) hmem 8 (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66991/524288 : ℝ))) hcmem 8 (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66991/524288 : ℝ)) (99206167051/100000000000 : ℝ) (992061670513/1000000000000 : ℝ) (125340553267/250000000000 : ℝ) (250681106539/500000000000 : ℝ) (793839683649/1000000000000 : ℝ) (198459920917/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0918_exp_lower
  have heNumeric : (51372539937/25000000000 : ℝ)/4 ≤ Real.exp (-42628249520377/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372539937/25000000000 : ℝ)/4 ≤ Real.exp ((33495/262144 : ℝ)-(198459920917/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33495/262144 : ℝ) (66991/524288 : ℝ) (198459920917/250000000000 : ℝ) (51372539937/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0919; no trusted numerical premise.
theorem cover8_leaf0919_exp_radius : (124750684316664159/125000000000000000 : ℝ) ≤ Real.exp ((-4187/262144 : ℝ)/8) ∧ Real.exp ((-4187/262144 : ℝ)/8) ≤ (998005474533313273/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4187/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0919_exp_lower : (460056725745728459/500000000000000000 : ℝ) ≤ Real.exp ((-85256498896289/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256498896289/128000000000000 : ℝ)/8) ≤ (920113451491456919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256498896289/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0919_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901599799/1000000000000 : ℝ) ≤ 4*Real.exp (66991/524288 : ℝ)*Real.exp (-mu (radius 8 (4187/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901599799/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4187/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0919_exp_radius
  have hrNumeric : (246038685183/250000000000 : ℝ) ≤ Real.exp (-4187/262144 : ℝ) ∧ Real.exp (-4187/262144 : ℝ) ≤ (984154740733/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246038685183/250000000000 : ℝ) ≤ (radius 8 (4187/32768 : ℝ)) ∧ (radius 8 (4187/32768 : ℝ)) ≤ (984154740733/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4187/32768 : ℝ)) (246038685183/250000000000 : ℝ) (984154740733/1000000000000 : ℝ) (88655860343/500000000000 : ℝ) (44327930173/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4187/32768 : ℝ)) (246038685183/250000000000 : ℝ) (984154740733/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246038685183/250000000000 : ℝ) (984154740733/1000000000000 : ℝ) (496038685183/500000000000 : ℝ) (992077370367/1000000000000 : ℝ) (992045735201/1000000000000 : ℝ) (992045735203/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 1 (496038685183/500000000000 : ℝ) (992077370367/1000000000000 : ℝ) (992045735201/1000000000000 : ℝ) (992045735203/1000000000000 : ℝ) (992061552783/1000000000000 : ℝ) (198412310557/200000000000 : ℝ) (992061552657/1000000000000 : ℝ) (992061552659/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 2 (992061552783/1000000000000 : ℝ) (198412310557/200000000000 : ℝ) (992061552657/1000000000000 : ℝ) (992061552659/1000000000000 : ℝ) (12400769409/12500000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 3 (12400769409/12500000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 4 (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 5 (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 6 (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4187/32768 : ℝ)) 7 (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4187/32768 : ℝ))) (88655860343/500000000000 : ℝ) (44327930173/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88655860343/500000000000 : ℝ) (44327930173/250000000000 : ℝ) (588655860343/1000000000000 : ℝ) (294327930173/500000000000 : ℝ) (52635497867/125000000000 : ℝ) (84216796589/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 1 (588655860343/1000000000000 : ℝ) (294327930173/500000000000 : ℝ) (52635497867/125000000000 : ℝ) (84216796589/200000000000 : ℝ) (504869921639/1000000000000 : ℝ) (252434960823/500000000000 : ℝ) (248934506573/500000000000 : ℝ) (248934506577/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 2 (504869921639/1000000000000 : ℝ) (252434960823/500000000000 : ℝ) (248934506573/500000000000 : ℝ) (248934506577/500000000000 : ℝ) (979237241/1953125000 : ℝ) (2506847337/5000000000 : ℝ) (125339311883/250000000000 : ℝ) (501357247541/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 3 (979237241/1953125000 : ℝ) (2506847337/5000000000 : ℝ) (125339311883/250000000000 : ℝ) (501357247541/1000000000000 : ℝ) (250681678731/500000000000 : ℝ) (501363357471/1000000000000 : ℝ) (31335209839/62500000000 : ℝ) (250681678717/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 4 (250681678731/500000000000 : ℝ) (501363357471/1000000000000 : ℝ) (31335209839/62500000000 : ℝ) (250681678717/500000000000 : ℝ) (501363357443/1000000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 5 (501363357443/1000000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 6 (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4187/32768 : ℝ))) 7 (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4187/32768 : ℝ)) hmem 8 (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4187/32768 : ℝ))) hcmem 8 (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4187/32768 : ℝ)) (992061552719/1000000000000 : ℝ) (496030776361/500000000000 : ℝ) (250681678721/500000000000 : ℝ) (501363357453/1000000000000 : ℝ) (793841589867/1000000000000 : ℝ) (6201887421/7812500000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0919_exp_lower
  have heNumeric : (2054901599799/1000000000000 : ℝ)/4 ≤ Real.exp (-85256498896289/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901599799/1000000000000 : ℝ)/4 ≤ Real.exp ((66991/524288 : ℝ)-(6201887421/7812500000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66991/524288 : ℝ) (4187/32768 : ℝ) (6201887421/7812500000 : ℝ) (2054901599799/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0920; no trusted numerical premise.
theorem cover8_leaf0920_exp_radius : (998005444790432819/1000000000000000000 : ℝ) ≤ Real.exp ((-66993/4194304 : ℝ)/8) ∧ Real.exp ((-66993/4194304 : ℝ)/8) ≤ (49900272239521641/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66993/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0920_exp_lower : (230028362906150277/250000000000000000 : ℝ) ≤ Real.exp ((-5328531171757/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328531171757/8000000000000 : ℝ)/8) ≤ (920113451624601109/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328531171757/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0920_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450801089/500000000000 : ℝ) ≤ 4*Real.exp (4187/32768 : ℝ)*Real.exp (-mu (radius 8 (66993/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450801089/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66993/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0920_exp_radius
  have hrNumeric : (246038626523/250000000000 : ℝ) ≤ Real.exp (-66993/4194304 : ℝ) ∧ Real.exp (-66993/4194304 : ℝ) ≤ (984154506093/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246038626523/250000000000 : ℝ) ≤ (radius 8 (66993/524288 : ℝ)) ∧ (radius 8 (66993/524288 : ℝ)) ≤ (984154506093/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66993/524288 : ℝ)) (246038626523/250000000000 : ℝ) (984154506093/1000000000000 : ℝ) (22164127879/125000000000 : ℝ) (88656511519/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66993/524288 : ℝ)) (246038626523/250000000000 : ℝ) (984154506093/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246038626523/250000000000 : ℝ) (984154506093/1000000000000 : ℝ) (496038626523/500000000000 : ℝ) (992077253047/1000000000000 : ℝ) (992045616941/1000000000000 : ℝ) (496022808471/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 1 (496038626523/500000000000 : ℝ) (992077253047/1000000000000 : ℝ) (992045616941/1000000000000 : ℝ) (496022808471/500000000000 : ℝ) (992061434993/1000000000000 : ℝ) (198412286999/200000000000 : ℝ) (992061434867/1000000000000 : ℝ) (992061434869/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 2 (992061434993/1000000000000 : ℝ) (198412286999/200000000000 : ℝ) (992061434867/1000000000000 : ℝ) (992061434869/1000000000000 : ℝ) (99206143493/100000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 3 (99206143493/100000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 4 (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 5 (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 6 (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66993/524288 : ℝ)) 7 (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66993/524288 : ℝ))) (22164127879/125000000000 : ℝ) (88656511519/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22164127879/125000000000 : ℝ) (88656511519/500000000000 : ℝ) (147164127879/250000000000 : ℝ) (588656511519/1000000000000 : ℝ) (210542764677/500000000000 : ℝ) (210542764681/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 1 (147164127879/250000000000 : ℝ) (588656511519/1000000000000 : ℝ) (210542764677/500000000000 : ℝ) (210542764681/500000000000 : ℝ) (100974204087/200000000000 : ℝ) (504871020441/1000000000000 : ℝ) (248935101361/500000000000 : ℝ) (497870202729/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 2 (100974204087/200000000000 : ℝ) (504871020441/1000000000000 : ℝ) (248935101361/500000000000 : ℝ) (497870202729/1000000000000 : ℝ) (250685305789/500000000000 : ℝ) (100274122317/200000000000 : ℝ) (501358392063/1000000000000 : ℝ) (50135839207/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 3 (250685305789/500000000000 : ℝ) (100274122317/200000000000 : ℝ) (501358392063/1000000000000 : ℝ) (50135839207/100000000000 : ℝ) (25068225091/50000000000 : ℝ) (125341125457/250000000000 : ℝ) (501364501783/1000000000000 : ℝ) (501364501791/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 4 (25068225091/50000000000 : ℝ) (125341125457/250000000000 : ℝ) (501364501783/1000000000000 : ℝ) (501364501791/1000000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 5 (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 6 (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66993/524288 : ℝ))) 7 (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66993/524288 : ℝ)) hmem 8 (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66993/524288 : ℝ))) hcmem 8 (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66993/524288 : ℝ)) (992061434929/1000000000000 : ℝ) (248015358733/250000000000 : ℝ) (501364501801/1000000000000 : ℝ) (50136450181/100000000000 : ℝ) (793843496061/1000000000000 : ℝ) (793843496079/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0920_exp_lower
  have heNumeric : (1027450801089/500000000000 : ℝ)/4 ≤ Real.exp (-5328531171757/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450801089/500000000000 : ℝ)/4 ≤ Real.exp ((4187/32768 : ℝ)-(793843496079/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4187/32768 : ℝ) (66993/524288 : ℝ) (793843496079/1000000000000 : ℝ) (1027450801089/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0921; no trusted numerical premise.
theorem cover8_leaf0921_exp_radius : (249501353761888313/250000000000000000 : ℝ) ≤ Real.exp ((-33497/2097152 : ℝ)/8) ∧ Real.exp ((-33497/2097152 : ℝ)/8) ≤ (998005415047553253/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33497/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0921_exp_lower : (460056725879390213/500000000000000000 : ℝ) ≤ Real.exp ((-85256498598783/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256498598783/128000000000000 : ℝ)/8) ≤ (920113451758780427/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256498598783/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0921_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196064183/40000000000 : ℝ) ≤ 4*Real.exp (66993/524288 : ℝ)*Real.exp (-mu (radius 8 (33497/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (82196064183/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33497/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0921_exp_radius
  have hrNumeric : (984154271451/1000000000000 : ℝ) ≤ Real.exp (-33497/2097152 : ℝ) ∧ Real.exp (-33497/2097152 : ℝ) ≤ (246038567863/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984154271451/1000000000000 : ℝ) ≤ (radius 8 (33497/262144 : ℝ)) ∧ (radius 8 (33497/262144 : ℝ)) ≤ (246038567863/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33497/262144 : ℝ)) (984154271451/1000000000000 : ℝ) (246038567863/250000000000 : ℝ) (177314325373/1000000000000 : ℝ) (8865716269/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33497/262144 : ℝ)) (984154271451/1000000000000 : ℝ) (246038567863/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984154271451/1000000000000 : ℝ) (246038567863/250000000000 : ℝ) (39683085429/40000000000 : ℝ) (496038567863/500000000000 : ℝ) (992045498679/1000000000000 : ℝ) (992045498681/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 1 (39683085429/40000000000 : ℝ) (496038567863/500000000000 : ℝ) (992045498679/1000000000000 : ℝ) (992045498681/1000000000000 : ℝ) (496030658601/500000000000 : ℝ) (248015329301/250000000000 : ℝ) (39682452683/40000000000 : ℝ) (496030658539/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 2 (496030658601/500000000000 : ℝ) (248015329301/250000000000 : ℝ) (39682452683/40000000000 : ℝ) (496030658539/500000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 3 (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 4 (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 5 (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 6 (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33497/262144 : ℝ)) 7 (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33497/262144 : ℝ))) (177314325373/1000000000000 : ℝ) (8865716269/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177314325373/1000000000000 : ℝ) (8865716269/50000000000 : ℝ) (294328581343/500000000000 : ℝ) (58865716269/100000000000 : ℝ) (421087075761/1000000000000 : ℝ) (42108707577/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 1 (294328581343/500000000000 : ℝ) (58865716269/100000000000 : ℝ) (421087075761/1000000000000 : ℝ) (42108707577/100000000000 : ℝ) (504872119223/1000000000000 : ℝ) (50487211923/100000000000 : ℝ) (49787139229/100000000000 : ℝ) (248935696149/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 2 (504872119223/1000000000000 : ℝ) (50487211923/100000000000 : ℝ) (49787139229/100000000000 : ℝ) (248935696149/500000000000 : ℝ) (125342938939/250000000000 : ℝ) (125342938941/250000000000 : ℝ) (250679768293/500000000000 : ℝ) (250679768297/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 3 (125342938939/250000000000 : ℝ) (125342938941/250000000000 : ℝ) (250679768293/500000000000 : ℝ) (250679768297/500000000000 : ℝ) (501365646171/1000000000000 : ℝ) (501365646179/1000000000000 : ℝ) (501365646133/1000000000000 : ℝ) (250682823071/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 4 (501365646171/1000000000000 : ℝ) (501365646179/1000000000000 : ℝ) (501365646133/1000000000000 : ℝ) (250682823071/500000000000 : ℝ) (62670705769/125000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 5 (62670705769/125000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 6 (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33497/262144 : ℝ))) 7 (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33497/262144 : ℝ)) hmem 8 (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33497/262144 : ℝ))) hcmem 8 (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33497/262144 : ℝ)) (496030658569/500000000000 : ℝ) (992061317141/1000000000000 : ℝ) (501365646151/1000000000000 : ℝ) (501365646161/1000000000000 : ℝ) (396922701121/500000000000 : ℝ) (793845402261/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0921_exp_lower
  have heNumeric : (82196064183/40000000000 : ℝ)/4 ≤ Real.exp (-85256498598783/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196064183/40000000000 : ℝ)/4 ≤ Real.exp ((66993/524288 : ℝ)-(793845402261/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66993/524288 : ℝ) (33497/262144 : ℝ) (793845402261/1000000000000 : ℝ) (82196064183/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0922; no trusted numerical premise.
theorem cover8_leaf0922_exp_radius : (998005385304674571/1000000000000000000 : ℝ) ≤ Real.exp ((-66995/4194304 : ℝ)/8) ∧ Real.exp ((-66995/4194304 : ℝ)/8) ≤ (249501346326168643/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66995/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0922_exp_lower : (920113451894799971/1000000000000000000 : ℝ) ≤ Real.exp ((-42628249223703/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628249223703/64000000000000 : ℝ)/8) ≤ (230028362973699993/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628249223703/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0922_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450803503/500000000000 : ℝ) ≤ 4*Real.exp (33497/262144 : ℝ)*Real.exp (-mu (radius 8 (66995/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450803503/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66995/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0922_exp_radius
  have hrNumeric : (98415403681/100000000000 : ℝ) ≤ Real.exp (-66995/4194304 : ℝ) ∧ Real.exp (-66995/4194304 : ℝ) ≤ (984154036811/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98415403681/100000000000 : ℝ) ≤ (radius 8 (66995/524288 : ℝ)) ∧ (radius 8 (66995/524288 : ℝ)) ≤ (984154036811/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66995/524288 : ℝ)) (98415403681/100000000000 : ℝ) (984154036811/1000000000000 : ℝ) (35463125541/200000000000 : ℝ) (2770556683/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66995/524288 : ℝ)) (98415403681/100000000000 : ℝ) (984154036811/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98415403681/100000000000 : ℝ) (984154036811/1000000000000 : ℝ) (198415403681/200000000000 : ℝ) (496038509203/500000000000 : ℝ) (496022690209/500000000000 : ℝ) (49602269021/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 1 (198415403681/200000000000 : ℝ) (496038509203/500000000000 : ℝ) (496022690209/500000000000 : ℝ) (49602269021/50000000000 : ℝ) (992061199411/1000000000000 : ℝ) (992061199413/1000000000000 : ℝ) (198412239857/200000000000 : ℝ) (992061199287/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 2 (992061199411/1000000000000 : ℝ) (992061199413/1000000000000 : ℝ) (198412239857/200000000000 : ℝ) (992061199287/1000000000000 : ℝ) (248015299837/250000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 3 (248015299837/250000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 4 (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 5 (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 6 (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66995/524288 : ℝ)) 7 (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66995/524288 : ℝ))) (35463125541/200000000000 : ℝ) (2770556683/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35463125541/200000000000 : ℝ) (2770556683/15625000000 : ℝ) (147164453463/250000000000 : ℝ) (18395556683/31250000000 : ℝ) (8421772443/20000000000 : ℝ) (5263607777/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 1 (147164453463/250000000000 : ℝ) (18395556683/31250000000 : ℝ) (8421772443/20000000000 : ℝ) (5263607777/12500000000 : ℝ) (504873218001/1000000000000 : ℝ) (63109152251/125000000000 : ℝ) (124468145461/250000000000 : ℝ) (497872581853/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 2 (504873218001/1000000000000 : ℝ) (63109152251/125000000000 : ℝ) (124468145461/250000000000 : ℝ) (497872581853/1000000000000 : ℝ) (250686449961/500000000000 : ℝ) (501372899931/1000000000000 : ℝ) (62670085137/125000000000 : ℝ) (250680340553/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 3 (250686449961/500000000000 : ℝ) (501372899931/1000000000000 : ℝ) (62670085137/125000000000 : ℝ) (250680340553/500000000000 : ℝ) (501366790509/1000000000000 : ℝ) (501366790519/1000000000000 : ℝ) (501366790471/1000000000000 : ℝ) (250683395241/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 4 (501366790509/1000000000000 : ℝ) (501366790519/1000000000000 : ℝ) (501366790471/1000000000000 : ℝ) (250683395241/500000000000 : ℝ) (50136679049/100000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 5 (50136679049/100000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 6 (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66995/524288 : ℝ))) 7 (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66995/524288 : ℝ)) hmem 8 (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66995/524288 : ℝ))) hcmem 8 (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66995/524288 : ℝ)) (992061199347/1000000000000 : ℝ) (19841223987/20000000000 : ℝ) (501366790489/1000000000000 : ℝ) (501366790501/1000000000000 : ℝ) (158769461681/200000000000 : ℝ) (793847308427/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0922_exp_lower
  have heNumeric : (1027450803503/500000000000 : ℝ)/4 ≤ Real.exp (-42628249223703/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450803503/500000000000 : ℝ)/4 ≤ Real.exp ((33497/262144 : ℝ)-(793847308427/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33497/262144 : ℝ) (66995/524288 : ℝ) (793847308427/1000000000000 : ℝ) (1027450803503/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0923; no trusted numerical premise.
theorem cover8_leaf0923_exp_radius : (998005355561796777/1000000000000000000 : ℝ) ≤ Real.exp ((-16749/1048576 : ℝ)/8) ∧ Real.exp ((-16749/1048576 : ℝ)/8) ≤ (499002677780898389/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16749/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0923_exp_lower : (230028363008596239/250000000000000000 : ℝ) ≤ Real.exp ((-85256498292061/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256498292061/128000000000000 : ℝ)/8) ≤ (920113452034384957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256498292061/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0923_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901609499/1000000000000 : ℝ) ≤ 4*Real.exp (66995/524288 : ℝ)*Real.exp (-mu (radius 8 (16749/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901609499/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16749/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0923_exp_radius
  have hrNumeric : (98415380217/100000000000 : ℝ) ≤ Real.exp (-16749/1048576 : ℝ) ∧ Real.exp (-16749/1048576 : ℝ) ≤ (984153802171/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98415380217/100000000000 : ℝ) ≤ (radius 8 (16749/131072 : ℝ)) ∧ (radius 8 (16749/131072 : ℝ)) ≤ (984153802171/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16749/131072 : ℝ)) (98415380217/100000000000 : ℝ) (984153802171/1000000000000 : ℝ) (177316930021/1000000000000 : ℝ) (44329232507/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16749/131072 : ℝ)) (98415380217/100000000000 : ℝ) (984153802171/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98415380217/100000000000 : ℝ) (984153802171/1000000000000 : ℝ) (198415380217/200000000000 : ℝ) (496038450543/500000000000 : ℝ) (992045262157/1000000000000 : ℝ) (992045262159/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 1 (198415380217/200000000000 : ℝ) (496038450543/500000000000 : ℝ) (992045262157/1000000000000 : ℝ) (992045262159/1000000000000 : ℝ) (992061081621/1000000000000 : ℝ) (992061081623/1000000000000 : ℝ) (496030540747/500000000000 : ℝ) (992061081497/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 2 (992061081621/1000000000000 : ℝ) (992061081623/1000000000000 : ℝ) (496030540747/500000000000 : ℝ) (992061081497/1000000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 3 (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 4 (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 5 (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 6 (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16749/131072 : ℝ)) 7 (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16749/131072 : ℝ))) (177316930021/1000000000000 : ℝ) (44329232507/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177316930021/1000000000000 : ℝ) (44329232507/250000000000 : ℝ) (58865846501/100000000000 : ℝ) (294329232507/500000000000 : ℝ) (105272542129/250000000000 : ℝ) (16843606741/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 1 (58865846501/100000000000 : ℝ) (294329232507/500000000000 : ℝ) (105272542129/250000000000 : ℝ) (16843606741/40000000000 : ℝ) (504874316763/1000000000000 : ℝ) (50487431677/100000000000 : ℝ) (497873771381/1000000000000 : ℝ) (497873771389/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 2 (504874316763/1000000000000 : ℝ) (50487431677/100000000000 : ℝ) (497873771381/1000000000000 : ℝ) (497873771389/1000000000000 : ℝ) (62671755509/125000000000 : ℝ) (6267175551/12500000000 : ℝ) (501361825591/1000000000000 : ℝ) (501361825599/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 3 (62671755509/125000000000 : ℝ) (6267175551/12500000000 : ℝ) (501361825591/1000000000000 : ℝ) (501361825599/1000000000000 : ℝ) (501367934831/1000000000000 : ℝ) (12534198371/25000000000 : ℝ) (250683967397/500000000000 : ℝ) (501367934803/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 4 (501367934831/1000000000000 : ℝ) (12534198371/25000000000 : ℝ) (250683967397/500000000000 : ℝ) (501367934803/1000000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 5 (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 6 (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16749/131072 : ℝ))) 7 (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16749/131072 : ℝ)) hmem 8 (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16749/131072 : ℝ))) hcmem 8 (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16749/131072 : ℝ)) (992061081557/1000000000000 : ℝ) (24801527039/25000000000 : ℝ) (125341983703/250000000000 : ℝ) (250683967411/500000000000 : ℝ) (793849214543/1000000000000 : ℝ) (396924607281/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0923_exp_lower
  have heNumeric : (2054901609499/1000000000000 : ℝ)/4 ≤ Real.exp (-85256498292061/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901609499/1000000000000 : ℝ)/4 ≤ Real.exp ((66995/524288 : ℝ)-(396924607281/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66995/524288 : ℝ) (16749/131072 : ℝ) (396924607281/500000000000 : ℝ) (2054901609499/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0924; no trusted numerical premise.
theorem cover8_leaf0924_exp_radius : (998005325818919869/1000000000000000000 : ℝ) ≤ Real.exp ((-66997/4194304 : ℝ)/8) ∧ Real.exp ((-66997/4194304 : ℝ)/8) ≤ (99800532581891987/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66997/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0924_exp_lower : (460056726087560041/500000000000000000 : ℝ) ≤ Real.exp ((-21314124533859/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314124533859/32000000000000 : ℝ)/8) ≤ (920113452175120083/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314124533859/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0924_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450806007/500000000000 : ℝ) ≤ 4*Real.exp (16749/131072 : ℝ)*Real.exp (-mu (radius 8 (66997/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450806007/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66997/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0924_exp_radius
  have hrNumeric : (984153567529/1000000000000 : ℝ) ≤ Real.exp (-66997/4194304 : ℝ) ∧ Real.exp (-66997/4194304 : ℝ) ≤ (98415356753/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984153567529/1000000000000 : ℝ) ≤ (radius 8 (66997/524288 : ℝ)) ∧ (radius 8 (66997/524288 : ℝ)) ≤ (98415356753/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66997/524288 : ℝ)) (984153567529/1000000000000 : ℝ) (98415356753/100000000000 : ℝ) (177318232333/1000000000000 : ℝ) (8865911617/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66997/524288 : ℝ)) (984153567529/1000000000000 : ℝ) (98415356753/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984153567529/1000000000000 : ℝ) (98415356753/100000000000 : ℝ) (248019195941/250000000000 : ℝ) (198415356753/200000000000 : ℝ) (124005642987/125000000000 : ℝ) (496022571949/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 1 (248019195941/250000000000 : ℝ) (198415356753/200000000000 : ℝ) (124005642987/125000000000 : ℝ) (496022571949/500000000000 : ℝ) (99206096383/100000000000 : ℝ) (124007620479/125000000000 : ℝ) (992060963703/1000000000000 : ℝ) (496030481853/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 2 (99206096383/100000000000 : ℝ) (124007620479/125000000000 : ℝ) (992060963703/1000000000000 : ℝ) (496030481853/500000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 3 (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 4 (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 5 (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 6 (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66997/524288 : ℝ)) 7 (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66997/524288 : ℝ))) (177318232333/1000000000000 : ℝ) (8865911617/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177318232333/1000000000000 : ℝ) (8865911617/50000000000 : ℝ) (294329558083/500000000000 : ℝ) (58865911617/100000000000 : ℝ) (421091714871/1000000000000 : ℝ) (1315911609/3125000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 1 (294329558083/500000000000 : ℝ) (58865911617/100000000000 : ℝ) (421091714871/1000000000000 : ℝ) (1315911609/3125000000 : ℝ) (252437707759/500000000000 : ℝ) (20195016621/40000000000 : ℝ) (497874960909/1000000000000 : ℝ) (497874960917/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 2 (252437707759/500000000000 : ℝ) (20195016621/40000000000 : ℝ) (497874960909/1000000000000 : ℝ) (497874960917/1000000000000 : ℝ) (501375188213/1000000000000 : ℝ) (501375188221/1000000000000 : ℝ) (501362970077/1000000000000 : ℝ) (250681485043/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 3 (501375188213/1000000000000 : ℝ) (501375188221/1000000000000 : ℝ) (501362970077/1000000000000 : ℝ) (250681485043/500000000000 : ℝ) (100273815829/200000000000 : ℝ) (250684539577/500000000000 : ℝ) (501369079107/1000000000000 : ℝ) (501369079117/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 4 (100273815829/200000000000 : ℝ) (250684539577/500000000000 : ℝ) (501369079107/1000000000000 : ℝ) (501369079117/1000000000000 : ℝ) (250684539563/500000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 5 (250684539563/500000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 6 (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66997/524288 : ℝ))) 7 (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66997/524288 : ℝ)) hmem 8 (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66997/524288 : ℝ))) hcmem 8 (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66997/524288 : ℝ)) (496030481883/500000000000 : ℝ) (992060963769/1000000000000 : ℝ) (4010952633/8000000000 : ℝ) (15667783723/31250000000 : ℝ) (793851120667/1000000000000 : ℝ) (793851120687/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0924_exp_lower
  have heNumeric : (1027450806007/500000000000 : ℝ)/4 ≤ Real.exp (-21314124533859/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450806007/500000000000 : ℝ)/4 ≤ Real.exp ((16749/131072 : ℝ)-(793851120687/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16749/131072 : ℝ) (66997/524288 : ℝ) (793851120687/1000000000000 : ℝ) (1027450806007/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0900_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0900_certificate
#check SmaleRate.Proofs.cover8_leaf0901_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0901_certificate
#check SmaleRate.Proofs.cover8_leaf0902_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0902_certificate
#check SmaleRate.Proofs.cover8_leaf0903_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0903_certificate
#check SmaleRate.Proofs.cover8_leaf0904_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0904_certificate
#check SmaleRate.Proofs.cover8_leaf0905_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0905_certificate
#check SmaleRate.Proofs.cover8_leaf0906_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0906_certificate
#check SmaleRate.Proofs.cover8_leaf0907_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0907_certificate
#check SmaleRate.Proofs.cover8_leaf0908_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0908_certificate
#check SmaleRate.Proofs.cover8_leaf0909_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0909_certificate
#check SmaleRate.Proofs.cover8_leaf0910_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0910_certificate
#check SmaleRate.Proofs.cover8_leaf0911_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0911_certificate
#check SmaleRate.Proofs.cover8_leaf0912_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0912_certificate
#check SmaleRate.Proofs.cover8_leaf0913_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0913_certificate
#check SmaleRate.Proofs.cover8_leaf0914_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0914_certificate
#check SmaleRate.Proofs.cover8_leaf0915_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0915_certificate
#check SmaleRate.Proofs.cover8_leaf0916_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0916_certificate
#check SmaleRate.Proofs.cover8_leaf0917_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0917_certificate
#check SmaleRate.Proofs.cover8_leaf0918_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0918_certificate
#check SmaleRate.Proofs.cover8_leaf0919_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0919_certificate
#check SmaleRate.Proofs.cover8_leaf0920_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0920_certificate
#check SmaleRate.Proofs.cover8_leaf0921_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0921_certificate
#check SmaleRate.Proofs.cover8_leaf0922_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0922_certificate
#check SmaleRate.Proofs.cover8_leaf0923_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0923_certificate
#check SmaleRate.Proofs.cover8_leaf0924_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0924_certificate
