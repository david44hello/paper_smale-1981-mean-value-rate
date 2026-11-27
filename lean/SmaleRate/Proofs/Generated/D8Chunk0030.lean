/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0750; no trusted numerical premise.
theorem cover8_leaf0750_exp_radius : (39920420043713727/40000000000000000 : ℝ) ≤ Real.exp ((-66823/4194304 : ℝ)/8) ∧ Real.exp ((-66823/4194304 : ℝ)/8) ≤ (124751312636605397/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66823/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0750_exp_lower : (920113461076055053/1000000000000000000 : ℝ) ≤ Real.exp ((-8525648822953/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525648822953/12800000000000 : ℝ)/8) ≤ (460056730538027527/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525648822953/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0750_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901771043/1000000000000 : ℝ) ≤ 4*Real.exp (33411/262144 : ℝ)*Real.exp (-mu (radius 8 (66823/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901771043/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66823/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0750_exp_radius
  have hrNumeric : (492097197911/500000000000 : ℝ) ≤ Real.exp (-66823/4194304 : ℝ) ∧ Real.exp (-66823/4194304 : ℝ) ≤ (984194395823/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492097197911/500000000000 : ℝ) ≤ (radius 8 (66823/524288 : ℝ)) ∧ (radius 8 (66823/524288 : ℝ)) ≤ (984194395823/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66823/524288 : ℝ)) (492097197911/500000000000 : ℝ) (984194395823/1000000000000 : ℝ) (44272869253/250000000000 : ℝ) (177091477019/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66823/524288 : ℝ)) (492097197911/500000000000 : ℝ) (984194395823/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492097197911/500000000000 : ℝ) (984194395823/1000000000000 : ℝ) (992097197911/1000000000000 : ℝ) (124012149739/125000000000 : ℝ) (992065721523/1000000000000 : ℝ) (39682628861/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 1 (992097197911/1000000000000 : ℝ) (124012149739/125000000000 : ℝ) (992065721523/1000000000000 : ℝ) (39682628861/40000000000 : ℝ) (992081459717/1000000000000 : ℝ) (992081459719/1000000000000 : ℝ) (124010182449/125000000000 : ℝ) (496040729797/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 2 (992081459717/1000000000000 : ℝ) (992081459719/1000000000000 : ℝ) (124010182449/125000000000 : ℝ) (496040729797/500000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 3 (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 4 (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 5 (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 6 (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66823/524288 : ℝ)) 7 (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66823/524288 : ℝ))) (44272869253/250000000000 : ℝ) (177091477019/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44272869253/250000000000 : ℝ) (177091477019/1000000000000 : ℝ) (294272869253/500000000000 : ℝ) (58854573851/100000000000 : ℝ) (84164476357/200000000000 : ℝ) (84164476359/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 1 (294272869253/500000000000 : ℝ) (58854573851/100000000000 : ℝ) (84164476357/200000000000 : ℝ) (84164476359/200000000000 : ℝ) (100936812029/200000000000 : ℝ) (504684060153/1000000000000 : ℝ) (248833890109/500000000000 : ℝ) (497667780227/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 2 (100936812029/200000000000 : ℝ) (504684060153/1000000000000 : ℝ) (248833890109/500000000000 : ℝ) (497667780227/1000000000000 : ℝ) (501175920181/1000000000000 : ℝ) (50117592019/100000000000 : ℝ) (501163641861/1000000000000 : ℝ) (50116364187/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 3 (501175920181/1000000000000 : ℝ) (50117592019/100000000000 : ℝ) (501163641861/1000000000000 : ℝ) (50116364187/100000000000 : ℝ) (501169781021/1000000000000 : ℝ) (50116978103/100000000000 : ℝ) (501169780983/1000000000000 : ℝ) (501169780993/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 4 (501169781021/1000000000000 : ℝ) (50116978103/100000000000 : ℝ) (501169780983/1000000000000 : ℝ) (501169780993/1000000000000 : ℝ) (250584890501/500000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 5 (250584890501/500000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 6 (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66823/524288 : ℝ))) 7 (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66823/524288 : ℝ)) hmem 8 (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66823/524288 : ℝ))) hcmem 8 (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66823/524288 : ℝ)) (496040729827/500000000000 : ℝ) (992081459657/1000000000000 : ℝ) (501169781001/1000000000000 : ℝ) (125292445253/250000000000 : ℝ) (396759582307/500000000000 : ℝ) (158703832927/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0750_exp_lower
  have heNumeric : (2054901771043/1000000000000 : ℝ)/4 ≤ Real.exp (-8525648822953/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901771043/1000000000000 : ℝ)/4 ≤ Real.exp ((33411/262144 : ℝ)-(158703832927/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33411/262144 : ℝ) (66823/524288 : ℝ) (158703832927/200000000000 : ℝ) (2054901771043/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0751; no trusted numerical premise.
theorem cover8_leaf0751_exp_radius : (499005235674906459/500000000000000000 : ℝ) ≤ Real.exp ((-8353/524288 : ℝ)/8) ∧ Real.exp ((-8353/524288 : ℝ)/8) ≤ (998010471349812919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8353/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0751_exp_lower : (920113460832642811/1000000000000000000 : ℝ) ≤ Real.exp ((-3410259540017/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410259540017/5120000000000 : ℝ)/8) ≤ (230028365208160703/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410259540017/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0751_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450883347/500000000000 : ℝ) ≤ 4*Real.exp (66823/524288 : ℝ)*Real.exp (-mu (radius 8 (8353/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450883347/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8353/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0751_exp_radius
  have hrNumeric : (246048540293/250000000000 : ℝ) ≤ Real.exp (-8353/524288 : ℝ) ∧ Real.exp (-8353/524288 : ℝ) ≤ (984194161173/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246048540293/250000000000 : ℝ) ≤ (radius 8 (8353/65536 : ℝ)) ∧ (radius 8 (8353/65536 : ℝ)) ≤ (984194161173/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8353/65536 : ℝ)) (246048540293/250000000000 : ℝ) (984194161173/1000000000000 : ℝ) (88546390543/500000000000 : ℝ) (177092781093/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8353/65536 : ℝ)) (246048540293/250000000000 : ℝ) (984194161173/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246048540293/250000000000 : ℝ) (984194161173/1000000000000 : ℝ) (496048540293/500000000000 : ℝ) (992097080587/1000000000000 : ℝ) (49603280163/50000000000 : ℝ) (992065603261/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 1 (496048540293/500000000000 : ℝ) (992097080587/1000000000000 : ℝ) (49603280163/50000000000 : ℝ) (992065603261/1000000000000 : ℝ) (992081341923/1000000000000 : ℝ) (248020335481/250000000000 : ℝ) (496040670899/500000000000 : ℝ) (4960406709/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 2 (992081341923/1000000000000 : ℝ) (248020335481/250000000000 : ℝ) (496040670899/500000000000 : ℝ) (4960406709/5000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 3 (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 4 (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 5 (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 6 (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8353/65536 : ℝ)) 7 (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8353/65536 : ℝ))) (88546390543/500000000000 : ℝ) (177092781093/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88546390543/500000000000 : ℝ) (177092781093/1000000000000 : ℝ) (588546390543/1000000000000 : ℝ) (588546390547/1000000000000 : ℝ) (210411965609/500000000000 : ℝ) (420823931227/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 1 (588546390543/1000000000000 : ℝ) (588546390547/1000000000000 : ℝ) (210411965609/500000000000 : ℝ) (420823931227/1000000000000 : ℝ) (6308564511/12500000000 : ℝ) (504685160887/1000000000000 : ℝ) (497668972081/1000000000000 : ℝ) (497668972089/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 2 (6308564511/12500000000 : ℝ) (504685160887/1000000000000 : ℝ) (497668972081/1000000000000 : ℝ) (497668972089/1000000000000 : ℝ) (6264713331/12500000000 : ℝ) (62647133311/125000000000 : ℝ) (501164788507/1000000000000 : ℝ) (100232957703/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 3 (6264713331/12500000000 : ℝ) (62647133311/125000000000 : ℝ) (501164788507/1000000000000 : ℝ) (100232957703/200000000000 : ℝ) (501170927493/1000000000000 : ℝ) (250585463751/500000000000 : ℝ) (100234185491/200000000000 : ℝ) (62646365933/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 4 (501170927493/1000000000000 : ℝ) (250585463751/500000000000 : ℝ) (100234185491/200000000000 : ℝ) (62646365933/125000000000 : ℝ) (250585463737/500000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 5 (250585463737/500000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 6 (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8353/65536 : ℝ))) 7 (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8353/65536 : ℝ)) hmem 8 (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8353/65536 : ℝ))) hcmem 8 (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8353/65536 : ℝ)) (49604067093/50000000000 : ℝ) (496040670931/500000000000 : ℝ) (501170927473/1000000000000 : ℝ) (501170927483/1000000000000 : ℝ) (793521074081/1000000000000 : ℝ) (7935210741/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0751_exp_lower
  have heNumeric : (1027450883347/500000000000 : ℝ)/4 ≤ Real.exp (-3410259540017/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450883347/500000000000 : ℝ)/4 ≤ Real.exp ((66823/524288 : ℝ)-(7935210741/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66823/524288 : ℝ) (8353/65536 : ℝ) (7935210741/10000000000 : ℝ) (1027450883347/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0752; no trusted numerical premise.
theorem cover8_leaf0752_exp_radius : (249502610401695887/250000000000000000 : ℝ) ≤ Real.exp ((-66825/4194304 : ℝ)/8) ∧ Real.exp ((-66825/4194304 : ℝ)/8) ≤ (998010441606783549/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66825/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0752_exp_lower : (92011346059118581/100000000000000000 : ℝ) ≤ Real.exp ((-10657061096143/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657061096143/16000000000000 : ℝ)/8) ≤ (920113460591185811/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657061096143/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0752_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745088119/50000000000 : ℝ) ≤ 4*Real.exp (8353/65536 : ℝ)*Real.exp (-mu (radius 8 (66825/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745088119/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66825/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0752_exp_radius
  have hrNumeric : (492096963261/500000000000 : ℝ) ≤ Real.exp (-66825/4194304 : ℝ) ∧ Real.exp (-66825/4194304 : ℝ) ≤ (984193926523/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492096963261/500000000000 : ℝ) ≤ (radius 8 (66825/524288 : ℝ)) ∧ (radius 8 (66825/524288 : ℝ)) ≤ (984193926523/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66825/524288 : ℝ)) (492096963261/500000000000 : ℝ) (984193926523/1000000000000 : ℝ) (3541881703/20000000000 : ℝ) (44273521289/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66825/524288 : ℝ)) (492096963261/500000000000 : ℝ) (984193926523/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492096963261/500000000000 : ℝ) (984193926523/1000000000000 : ℝ) (992096963261/1000000000000 : ℝ) (496048481631/500000000000 : ℝ) (248016371249/250000000000 : ℝ) (496032742499/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 1 (992096963261/1000000000000 : ℝ) (496048481631/500000000000 : ℝ) (248016371249/250000000000 : ℝ) (496032742499/500000000000 : ℝ) (15501269127/15625000000 : ℝ) (99208122413/100000000000 : ℝ) (992081224003/1000000000000 : ℝ) (496040612003/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 2 (15501269127/15625000000 : ℝ) (99208122413/100000000000 : ℝ) (992081224003/1000000000000 : ℝ) (496040612003/500000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 3 (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 4 (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 5 (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 6 (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66825/524288 : ℝ)) 7 (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66825/524288 : ℝ))) (3541881703/20000000000 : ℝ) (44273521289/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3541881703/20000000000 : ℝ) (44273521289/250000000000 : ℝ) (23541881703/40000000000 : ℝ) (294273521289/500000000000 : ℝ) (420825480633/1000000000000 : ℝ) (420825480641/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 1 (23541881703/40000000000 : ℝ) (294273521289/500000000000 : ℝ) (420825480633/1000000000000 : ℝ) (420825480641/1000000000000 : ℝ) (126171565401/250000000000 : ℝ) (50468626161/100000000000 : ℝ) (49767016393/100000000000 : ℝ) (497670163937/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 2 (126171565401/250000000000 : ℝ) (50468626161/100000000000 : ℝ) (49767016393/100000000000 : ℝ) (497670163937/1000000000000 : ℝ) (501178212767/1000000000000 : ℝ) (250589106387/500000000000 : ℝ) (25058296757/50000000000 : ℝ) (125291483787/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 3 (501178212767/1000000000000 : ℝ) (250589106387/500000000000 : ℝ) (25058296757/50000000000 : ℝ) (125291483787/250000000000 : ℝ) (501172073953/1000000000000 : ℝ) (501172073961/1000000000000 : ℝ) (100234414783/200000000000 : ℝ) (125293018481/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 4 (501172073953/1000000000000 : ℝ) (501172073961/1000000000000 : ℝ) (100234414783/200000000000 : ℝ) (125293018481/250000000000 : ℝ) (250586036967/500000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 5 (250586036967/500000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 6 (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66825/524288 : ℝ))) 7 (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66825/524288 : ℝ)) hmem 8 (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66825/524288 : ℝ))) hcmem 8 (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66825/524288 : ℝ)) (198416244813/200000000000 : ℝ) (248020306017/250000000000 : ℝ) (501172073933/1000000000000 : ℝ) (501172073943/1000000000000 : ℝ) (793522983529/1000000000000 : ℝ) (198380745887/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0752_exp_lower
  have heNumeric : (102745088119/50000000000 : ℝ)/4 ≤ Real.exp (-10657061096143/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745088119/50000000000 : ℝ)/4 ≤ Real.exp ((8353/65536 : ℝ)-(198380745887/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8353/65536 : ℝ) (66825/524288 : ℝ) (198380745887/250000000000 : ℝ) (102745088119/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0753; no trusted numerical premise.
theorem cover8_leaf0753_exp_radius : (124751301482969383/125000000000000000 : ℝ) ≤ Real.exp ((-33413/2097152 : ℝ)/8) ∧ Real.exp ((-33413/2097152 : ℝ)/8) ≤ (199602082372751013/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33413/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0753_exp_lower : (920113460352029093/1000000000000000000 : ℝ) ≤ Real.exp ((-85256489035303/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256489035303/128000000000000 : ℝ)/8) ≤ (460056730176014547/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256489035303/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0753_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901758107/1000000000000 : ℝ) ≤ 4*Real.exp (66825/524288 : ℝ)*Real.exp (-mu (radius 8 (33413/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901758107/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33413/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0753_exp_radius
  have hrNumeric : (30756052871/31250000000 : ℝ) ≤ Real.exp (-33413/2097152 : ℝ) ∧ Real.exp (-33413/2097152 : ℝ) ≤ (984193691873/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30756052871/31250000000 : ℝ) ≤ (radius 8 (33413/262144 : ℝ)) ∧ (radius 8 (33413/262144 : ℝ)) ≤ (984193691873/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33413/262144 : ℝ)) (30756052871/31250000000 : ℝ) (984193691873/1000000000000 : ℝ) (44273847301/250000000000 : ℝ) (17709538921/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33413/262144 : ℝ)) (30756052871/31250000000 : ℝ) (984193691873/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30756052871/31250000000 : ℝ) (984193691873/1000000000000 : ℝ) (62006052871/62500000000 : ℝ) (992096845937/1000000000000 : ℝ) (992065366733/1000000000000 : ℝ) (496032683367/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 1 (62006052871/62500000000 : ℝ) (992096845937/1000000000000 : ℝ) (992065366733/1000000000000 : ℝ) (496032683367/500000000000 : ℝ) (496040553167/500000000000 : ℝ) (31002534573/31250000000 : ℝ) (992081106209/1000000000000 : ℝ) (992081106211/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 2 (496040553167/500000000000 : ℝ) (31002534573/31250000000 : ℝ) (992081106209/1000000000000 : ℝ) (992081106211/1000000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 3 (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 4 (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 5 (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 6 (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33413/262144 : ℝ)) 7 (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33413/262144 : ℝ))) (44273847301/250000000000 : ℝ) (17709538921/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44273847301/250000000000 : ℝ) (17709538921/100000000000 : ℝ) (294273847301/500000000000 : ℝ) (117709538921/200000000000 : ℝ) (42082703003/100000000000 : ℝ) (210413515019/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 1 (294273847301/500000000000 : ℝ) (117709538921/200000000000 : ℝ) (42082703003/100000000000 : ℝ) (210413515019/500000000000 : ℝ) (126171840579/250000000000 : ℝ) (252343681161/500000000000 : ℝ) (248835677883/500000000000 : ℝ) (497671355773/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 2 (126171840579/250000000000 : ℝ) (252343681161/500000000000 : ℝ) (248835677883/500000000000 : ℝ) (497671355773/1000000000000 : ℝ) (501179359041/1000000000000 : ℝ) (62647419881/125000000000 : ℝ) (501167081761/1000000000000 : ℝ) (501167081769/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 3 (501179359041/1000000000000 : ℝ) (62647419881/125000000000 : ℝ) (501167081761/1000000000000 : ℝ) (501167081769/1000000000000 : ℝ) (501173220401/1000000000000 : ℝ) (501173220409/1000000000000 : ℝ) (501173220363/1000000000000 : ℝ) (501173220371/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 4 (501173220401/1000000000000 : ℝ) (501173220409/1000000000000 : ℝ) (501173220363/1000000000000 : ℝ) (501173220371/1000000000000 : ℝ) (250586610191/500000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 5 (250586610191/500000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 6 (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33413/262144 : ℝ))) 7 (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33413/262144 : ℝ)) hmem 8 (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33413/262144 : ℝ))) hcmem 8 (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33413/262144 : ℝ)) (992081106271/1000000000000 : ℝ) (496040553137/500000000000 : ℝ) (501173220381/1000000000000 : ℝ) (50117322039/100000000000 : ℝ) (396762446479/500000000000 : ℝ) (49595305811/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0753_exp_lower
  have heNumeric : (2054901758107/1000000000000 : ℝ)/4 ≤ Real.exp (-85256489035303/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901758107/1000000000000 : ℝ)/4 ≤ Real.exp ((66825/524288 : ℝ)-(49595305811/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66825/524288 : ℝ) (33413/262144 : ℝ) (49595305811/62500000000 : ℝ) (2054901758107/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0754; no trusted numerical premise.
theorem cover8_leaf0754_exp_radius : (499005191060363733/500000000000000000 : ℝ) ≤ Real.exp ((-66827/4194304 : ℝ)/8) ∧ Real.exp ((-66827/4194304 : ℝ)/8) ≤ (998010382120727467/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66827/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0754_exp_lower : (184022692023011529/200000000000000000 : ℝ) ≤ Real.exp ((-8525648929903/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525648929903/12800000000000 : ℝ)/8) ≤ (460056730057528823/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525648929903/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0754_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901753873/1000000000000 : ℝ) ≤ 4*Real.exp (33413/262144 : ℝ)*Real.exp (-mu (radius 8 (66827/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901753873/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66827/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0754_exp_radius
  have hrNumeric : (492096728611/500000000000 : ℝ) ≤ Real.exp (-66827/4194304 : ℝ) ∧ Real.exp (-66827/4194304 : ℝ) ≤ (984193457223/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492096728611/500000000000 : ℝ) ≤ (radius 8 (66827/524288 : ℝ)) ∧ (radius 8 (66827/524288 : ℝ)) ≤ (984193457223/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66827/524288 : ℝ)) (492096728611/500000000000 : ℝ) (984193457223/1000000000000 : ℝ) (345891979/1953125000 : ℝ) (88548346627/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66827/524288 : ℝ)) (492096728611/500000000000 : ℝ) (984193457223/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492096728611/500000000000 : ℝ) (984193457223/1000000000000 : ℝ) (992096728611/1000000000000 : ℝ) (248024182153/250000000000 : ℝ) (99206524847/100000000000 : ℝ) (992065248471/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 1 (992096728611/1000000000000 : ℝ) (248024182153/250000000000 : ℝ) (99206524847/100000000000 : ℝ) (992065248471/1000000000000 : ℝ) (49604049427/50000000000 : ℝ) (496040494271/500000000000 : ℝ) (198416197683/200000000000 : ℝ) (992080988417/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 2 (49604049427/50000000000 : ℝ) (496040494271/500000000000 : ℝ) (198416197683/200000000000 : ℝ) (992080988417/1000000000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 3 (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 4 (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 5 (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 6 (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66827/524288 : ℝ)) 7 (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66827/524288 : ℝ))) (345891979/1953125000 : ℝ) (88548346627/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (345891979/1953125000 : ℝ) (88548346627/500000000000 : ℝ) (2299016979/3906250000 : ℝ) (588548346627/1000000000000 : ℝ) (420828579409/1000000000000 : ℝ) (420828579417/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 1 (2299016979/3906250000 : ℝ) (588548346627/1000000000000 : ℝ) (420828579409/1000000000000 : ℝ) (420828579417/1000000000000 : ℝ) (63086057877/125000000000 : ℝ) (252344231511/500000000000 : ℝ) (124418136897/250000000000 : ℝ) (99534509519/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 2 (63086057877/125000000000 : ℝ) (252344231511/500000000000 : ℝ) (124418136897/250000000000 : ℝ) (99534509519/200000000000 : ℝ) (250590252651/500000000000 : ℝ) (501180505309/1000000000000 : ℝ) (501168228369/1000000000000 : ℝ) (501168228377/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 3 (250590252651/500000000000 : ℝ) (501180505309/1000000000000 : ℝ) (501168228369/1000000000000 : ℝ) (501168228377/1000000000000 : ℝ) (100234873367/200000000000 : ℝ) (501174366843/1000000000000 : ℝ) (501174366797/1000000000000 : ℝ) (250587183403/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 4 (100234873367/200000000000 : ℝ) (501174366843/1000000000000 : ℝ) (501174366797/1000000000000 : ℝ) (250587183403/500000000000 : ℝ) (15661698963/31250000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 5 (15661698963/31250000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 6 (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66827/524288 : ℝ))) 7 (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66827/524288 : ℝ)) hmem 8 (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66827/524288 : ℝ))) hcmem 8 (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66827/524288 : ℝ)) (992080988477/1000000000000 : ℝ) (3100253089/3125000000 : ℝ) (100234873363/200000000000 : ℝ) (20046974673/40000000000 : ℝ) (396763401183/500000000000 : ℝ) (158705360477/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0754_exp_lower
  have heNumeric : (2054901753873/1000000000000 : ℝ)/4 ≤ Real.exp (-8525648929903/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901753873/1000000000000 : ℝ)/4 ≤ Real.exp ((33413/262144 : ℝ)-(158705360477/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33413/262144 : ℝ) (66827/524288 : ℝ) (158705360477/200000000000 : ℝ) (2054901753873/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0755; no trusted numerical premise.
theorem cover8_leaf0755_exp_radius : (199602070475540151/200000000000000000 : ℝ) ≤ Real.exp ((-16707/1048576 : ℝ)/8) ∧ Real.exp ((-16707/1048576 : ℝ)/8) ≤ (249502588094425189/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16707/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0755_exp_lower : (920113459880386481/1000000000000000000 : ℝ) ≤ Real.exp ((-85256489560197/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256489560197/128000000000000 : ℝ)/8) ≤ (460056729940193241/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256489560197/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0755_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686271871/12500000000 : ℝ) ≤ 4*Real.exp (66827/524288 : ℝ)*Real.exp (-mu (radius 8 (16707/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (25686271871/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16707/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0755_exp_radius
  have hrNumeric : (246048305643/250000000000 : ℝ) ≤ Real.exp (-16707/1048576 : ℝ) ∧ Real.exp (-16707/1048576 : ℝ) ≤ (984193222573/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246048305643/250000000000 : ℝ) ≤ (radius 8 (16707/131072 : ℝ)) ∧ (radius 8 (16707/131072 : ℝ)) ≤ (984193222573/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16707/131072 : ℝ)) (246048305643/250000000000 : ℝ) (984193222573/1000000000000 : ℝ) (88548998641/500000000000 : ℝ) (22137249661/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16707/131072 : ℝ)) (246048305643/250000000000 : ℝ) (984193222573/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246048305643/250000000000 : ℝ) (984193222573/1000000000000 : ℝ) (496048305643/500000000000 : ℝ) (992096611287/1000000000000 : ℝ) (496032565103/500000000000 : ℝ) (31002035319/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 1 (496048305643/500000000000 : ℝ) (992096611287/1000000000000 : ℝ) (496032565103/500000000000 : ℝ) (31002035319/31250000000 : ℝ) (496040435373/500000000000 : ℝ) (248020217687/250000000000 : ℝ) (992080870621/1000000000000 : ℝ) (992080870623/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 2 (496040435373/500000000000 : ℝ) (248020217687/250000000000 : ℝ) (992080870621/1000000000000 : ℝ) (992080870623/1000000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 3 (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 4 (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 5 (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 6 (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16707/131072 : ℝ)) 7 (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16707/131072 : ℝ))) (88548998641/500000000000 : ℝ) (22137249661/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88548998641/500000000000 : ℝ) (22137249661/125000000000 : ℝ) (588548998641/1000000000000 : ℝ) (147137249661/250000000000 : ℝ) (420830128771/1000000000000 : ℝ) (420830128779/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 1 (588548998641/1000000000000 : ℝ) (147137249661/250000000000 : ℝ) (420830128771/1000000000000 : ℝ) (420830128779/1000000000000 : ℝ) (252344781853/500000000000 : ℝ) (7885774433/15625000000 : ℝ) (497673739397/1000000000000 : ℝ) (124418434851/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 2 (252344781853/500000000000 : ℝ) (7885774433/15625000000 : ℝ) (497673739397/1000000000000 : ℝ) (124418434851/250000000000 : ℝ) (501181651551/1000000000000 : ℝ) (250590825779/500000000000 : ℝ) (250584687483/500000000000 : ℝ) (501169374973/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 3 (501181651551/1000000000000 : ℝ) (250590825779/500000000000 : ℝ) (250584687483/500000000000 : ℝ) (501169374973/1000000000000 : ℝ) (250587756629/500000000000 : ℝ) (250587756633/500000000000 : ℝ) (25058775661/50000000000 : ℝ) (125293878307/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 4 (250587756629/500000000000 : ℝ) (250587756633/500000000000 : ℝ) (25058775661/50000000000 : ℝ) (125293878307/250000000000 : ℝ) (501175513239/1000000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 5 (501175513239/1000000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 6 (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16707/131072 : ℝ))) 7 (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16707/131072 : ℝ)) hmem 8 (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16707/131072 : ℝ))) hcmem 8 (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16707/131072 : ℝ)) (992080870683/1000000000000 : ℝ) (496040435343/500000000000 : ℝ) (250587756619/500000000000 : ℝ) (501175513247/1000000000000 : ℝ) (198382177939/250000000000 : ℝ) (396764355887/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0755_exp_lower
  have heNumeric : (25686271871/12500000000 : ℝ)/4 ≤ Real.exp (-85256489560197/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686271871/12500000000 : ℝ)/4 ≤ Real.exp ((66827/524288 : ℝ)-(396764355887/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66827/524288 : ℝ) (16707/131072 : ℝ) (396764355887/500000000000 : ℝ) (25686271871/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0756; no trusted numerical premise.
theorem cover8_leaf0756_exp_radius : (998010322634674931/1000000000000000000 : ℝ) ≤ Real.exp ((-66829/4194304 : ℝ)/8) ∧ Real.exp ((-66829/4194304 : ℝ)/8) ≤ (249502580658668733/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66829/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0756_exp_lower : (460056729823835279/500000000000000000 : ℝ) ≤ Real.exp ((-21314122454797/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122454797/32000000000000 : ℝ)/8) ≤ (920113459647670559/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122454797/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0756_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450872761/500000000000 : ℝ) ≤ 4*Real.exp (16707/131072 : ℝ)*Real.exp (-mu (radius 8 (66829/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450872761/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66829/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0756_exp_radius
  have hrNumeric : (492096493961/500000000000 : ℝ) ≤ Real.exp (-66829/4194304 : ℝ) ∧ Real.exp (-66829/4194304 : ℝ) ≤ (984192987923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492096493961/500000000000 : ℝ) ≤ (radius 8 (66829/524288 : ℝ)) ∧ (radius 8 (66829/524288 : ℝ)) ≤ (984192987923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66829/524288 : ℝ)) (492096493961/500000000000 : ℝ) (984192987923/1000000000000 : ℝ) (88549650653/500000000000 : ℝ) (2767176583/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66829/524288 : ℝ)) (492096493961/500000000000 : ℝ) (984192987923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492096493961/500000000000 : ℝ) (984192987923/1000000000000 : ℝ) (992096493961/1000000000000 : ℝ) (496048246981/500000000000 : ℝ) (992065011943/1000000000000 : ℝ) (124008126493/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 1 (992096493961/1000000000000 : ℝ) (496048246981/500000000000 : ℝ) (992065011943/1000000000000 : ℝ) (124008126493/125000000000 : ℝ) (124010094119/125000000000 : ℝ) (992080752953/1000000000000 : ℝ) (992080752827/1000000000000 : ℝ) (992080752829/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 2 (124010094119/125000000000 : ℝ) (992080752953/1000000000000 : ℝ) (992080752827/1000000000000 : ℝ) (992080752829/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 3 (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 4 (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 5 (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 6 (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66829/524288 : ℝ)) 7 (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66829/524288 : ℝ))) (88549650653/500000000000 : ℝ) (2767176583/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88549650653/500000000000 : ℝ) (2767176583/15625000000 : ℝ) (588549650653/1000000000000 : ℝ) (18392176583/31250000000 : ℝ) (105207919529/250000000000 : ℝ) (105207919531/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 1 (588549650653/1000000000000 : ℝ) (18392176583/31250000000 : ℝ) (105207919529/250000000000 : ℝ) (105207919531/250000000000 : ℝ) (7885791631/15625000000 : ℝ) (50469066439/100000000000 : ℝ) (497674931193/1000000000000 : ℝ) (19440427/39062500 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 2 (7885791631/15625000000 : ℝ) (50469066439/100000000000 : ℝ) (497674931193/1000000000000 : ℝ) (19440427/39062500 : ℝ) (125295699447/250000000000 : ℝ) (100236559559/200000000000 : ℝ) (10023410431/20000000000 : ℝ) (501170521557/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 3 (125295699447/250000000000 : ℝ) (100236559559/200000000000 : ℝ) (10023410431/20000000000 : ℝ) (501170521557/1000000000000 : ℝ) (501176659669/1000000000000 : ℝ) (125294164919/250000000000 : ℝ) (501176659631/1000000000000 : ℝ) (501176659639/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 4 (501176659669/1000000000000 : ℝ) (125294164919/250000000000 : ℝ) (501176659631/1000000000000 : ℝ) (501176659639/1000000000000 : ℝ) (10023533193/20000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 5 (10023533193/20000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 6 (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66829/524288 : ℝ))) 7 (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66829/524288 : ℝ)) hmem 8 (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66829/524288 : ℝ))) hcmem 8 (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66829/524288 : ℝ)) (992080752889/1000000000000 : ℝ) (992080752891/1000000000000 : ℝ) (501176659649/1000000000000 : ℝ) (250588329829/500000000000 : ℝ) (793530621129/1000000000000 : ℝ) (396765310573/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0756_exp_lower
  have heNumeric : (1027450872761/500000000000 : ℝ)/4 ≤ Real.exp (-21314122454797/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450872761/500000000000 : ℝ)/4 ≤ Real.exp ((16707/131072 : ℝ)-(396765310573/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16707/131072 : ℝ) (66829/524288 : ℝ) (396765310573/500000000000 : ℝ) (1027450872761/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0757; no trusted numerical premise.
theorem cover8_leaf0757_exp_radius : (998010292891649993/1000000000000000000 : ℝ) ≤ Real.exp ((-33415/2097152 : ℝ)/8) ∧ Real.exp ((-33415/2097152 : ℝ)/8) ≤ (499005146445824997/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33415/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0757_exp_lower : (920113459417024891/1000000000000000000 : ℝ) ≤ Real.exp ((-682051920607/1024000000000 : ℝ)/8) ∧ Real.exp ((-682051920607/1024000000000 : ℝ)/8) ≤ (230028364854256223/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682051920607/1024000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0757_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901741401/1000000000000 : ℝ) ≤ 4*Real.exp (66829/524288 : ℝ)*Real.exp (-mu (radius 8 (33415/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901741401/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33415/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0757_exp_radius
  have hrNumeric : (123024094159/125000000000 : ℝ) ≤ Real.exp (-33415/2097152 : ℝ) ∧ Real.exp (-33415/2097152 : ℝ) ≤ (984192753273/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123024094159/125000000000 : ℝ) ≤ (radius 8 (33415/262144 : ℝ)) ∧ (radius 8 (33415/262144 : ℝ)) ≤ (984192753273/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33415/262144 : ℝ)) (123024094159/125000000000 : ℝ) (984192753273/1000000000000 : ℝ) (4427515133/25000000000 : ℝ) (177100605327/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33415/262144 : ℝ)) (123024094159/125000000000 : ℝ) (984192753273/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123024094159/125000000000 : ℝ) (984192753273/1000000000000 : ℝ) (248024094159/250000000000 : ℝ) (992096376637/1000000000000 : ℝ) (992064893679/1000000000000 : ℝ) (992064893681/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 1 (248024094159/250000000000 : ℝ) (992096376637/1000000000000 : ℝ) (992064893679/1000000000000 : ℝ) (992064893681/1000000000000 : ℝ) (992080635157/1000000000000 : ℝ) (992080635159/1000000000000 : ℝ) (124010079379/125000000000 : ℝ) (198416127007/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 2 (992080635157/1000000000000 : ℝ) (992080635159/1000000000000 : ℝ) (124010079379/125000000000 : ℝ) (198416127007/200000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 3 (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 4 (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 5 (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 6 (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33415/262144 : ℝ)) 7 (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33415/262144 : ℝ))) (4427515133/25000000000 : ℝ) (177100605327/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4427515133/25000000000 : ℝ) (177100605327/1000000000000 : ℝ) (29427515133/50000000000 : ℝ) (73568787833/125000000000 : ℝ) (210416613721/500000000000 : ℝ) (105208306863/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 1 (29427515133/50000000000 : ℝ) (73568787833/125000000000 : ℝ) (210416613721/500000000000 : ℝ) (105208306863/250000000000 : ℝ) (504691765051/1000000000000 : ℝ) (252345882529/500000000000 : ℝ) (19907044919/40000000000 : ℝ) (62209515373/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 2 (504691765051/1000000000000 : ℝ) (252345882529/500000000000 : ℝ) (19907044919/40000000000 : ℝ) (62209515373/125000000000 : ℝ) (501183944013/1000000000000 : ℝ) (501183944021/1000000000000 : ℝ) (501171668121/1000000000000 : ℝ) (50117166813/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 3 (501183944013/1000000000000 : ℝ) (501183944021/1000000000000 : ℝ) (501171668121/1000000000000 : ℝ) (50117166813/100000000000 : ℝ) (501177806067/1000000000000 : ℝ) (125294451519/250000000000 : ℝ) (501177806029/1000000000000 : ℝ) (250588903019/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 4 (501177806067/1000000000000 : ℝ) (125294451519/250000000000 : ℝ) (501177806029/1000000000000 : ℝ) (250588903019/500000000000 : ℝ) (15661806439/31250000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 5 (15661806439/31250000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 6 (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33415/262144 : ℝ))) 7 (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33415/262144 : ℝ)) hmem 8 (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33415/262144 : ℝ))) hcmem 8 (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33415/262144 : ℝ)) (496040317547/500000000000 : ℝ) (992080635097/1000000000000 : ℝ) (501177806047/1000000000000 : ℝ) (501177806057/1000000000000 : ℝ) (793532530481/1000000000000 : ℝ) (1587065061/2000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0757_exp_lower
  have heNumeric : (2054901741401/1000000000000 : ℝ)/4 ≤ Real.exp (-682051920607/1024000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901741401/1000000000000 : ℝ)/4 ≤ Real.exp ((66829/524288 : ℝ)-(1587065061/2000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66829/524288 : ℝ) (33415/262144 : ℝ) (1587065061/2000000000 : ℝ) (2054901741401/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0758; no trusted numerical premise.
theorem cover8_leaf0758_exp_radius : (998010263148625941/1000000000000000000 : ℝ) ≤ Real.exp ((-66831/4194304 : ℝ)/8) ∧ Real.exp ((-66831/4194304 : ℝ)/8) ≤ (499005131574312971/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66831/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0758_exp_lower : (230028364797141123/250000000000000000 : ℝ) ≤ Real.exp ((-8525649033013/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525649033013/12800000000000 : ℝ)/8) ≤ (920113459188564493/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525649033013/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0758_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372543433/25000000000 : ℝ) ≤ 4*Real.exp (33415/262144 : ℝ)*Real.exp (-mu (radius 8 (66831/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (51372543433/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66831/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0758_exp_radius
  have hrNumeric : (492096259311/500000000000 : ℝ) ≤ Real.exp (-66831/4194304 : ℝ) ∧ Real.exp (-66831/4194304 : ℝ) ≤ (984192518623/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492096259311/500000000000 : ℝ) ≤ (radius 8 (66831/524288 : ℝ)) ∧ (radius 8 (66831/524288 : ℝ)) ≤ (984192518623/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66831/524288 : ℝ)) (492096259311/500000000000 : ℝ) (984192518623/1000000000000 : ℝ) (44275477331/250000000000 : ℝ) (177101909331/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66831/524288 : ℝ)) (492096259311/500000000000 : ℝ) (984192518623/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492096259311/500000000000 : ℝ) (984192518623/1000000000000 : ℝ) (992096259311/1000000000000 : ℝ) (62006016207/62500000000 : ℝ) (124008096927/125000000000 : ℝ) (992064775417/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 1 (992096259311/1000000000000 : ℝ) (62006016207/62500000000 : ℝ) (124008096927/125000000000 : ℝ) (992064775417/1000000000000 : ℝ) (992080517363/1000000000000 : ℝ) (198416103473/200000000000 : ℝ) (496040258619/500000000000 : ℝ) (24802012931/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 2 (992080517363/1000000000000 : ℝ) (198416103473/200000000000 : ℝ) (496040258619/500000000000 : ℝ) (24802012931/25000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 3 (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 4 (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 5 (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 6 (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66831/524288 : ℝ)) 7 (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66831/524288 : ℝ))) (44275477331/250000000000 : ℝ) (177101909331/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44275477331/250000000000 : ℝ) (177101909331/1000000000000 : ℝ) (294275477331/500000000000 : ℝ) (294275477333/500000000000 : ℝ) (26302173547/62500000000 : ℝ) (420834776761/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 1 (294275477331/500000000000 : ℝ) (294275477333/500000000000 : ℝ) (26302173547/62500000000 : ℝ) (420834776761/1000000000000 : ℝ) (504692865707/1000000000000 : ℝ) (252346432857/500000000000 : ℝ) (99535462949/200000000000 : ℝ) (497677314753/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 2 (504692865707/1000000000000 : ℝ) (252346432857/500000000000 : ℝ) (99535462949/200000000000 : ℝ) (497677314753/1000000000000 : ℝ) (250592545113/500000000000 : ℝ) (250592545117/500000000000 : ℝ) (501172814681/1000000000000 : ℝ) (50117281469/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 3 (250592545113/500000000000 : ℝ) (250592545117/500000000000 : ℝ) (501172814681/1000000000000 : ℝ) (50117281469/100000000000 : ℝ) (501178952453/1000000000000 : ℝ) (250589476231/500000000000 : ℝ) (100235790483/200000000000 : ℝ) (20047158097/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 4 (501178952453/1000000000000 : ℝ) (250589476231/500000000000 : ℝ) (100235790483/200000000000 : ℝ) (20047158097/40000000000 : ℝ) (250589476217/500000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 5 (250589476217/500000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 6 (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66831/524288 : ℝ))) 7 (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66831/524288 : ℝ)) hmem 8 (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66831/524288 : ℝ))) hcmem 8 (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66831/524288 : ℝ)) (9920805173/10000000000 : ℝ) (992080517303/1000000000000 : ℝ) (501178952433/1000000000000 : ℝ) (125294738111/250000000000 : ℝ) (396767219907/500000000000 : ℝ) (158706887967/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0758_exp_lower
  have heNumeric : (51372543433/25000000000 : ℝ)/4 ≤ Real.exp (-8525649033013/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372543433/25000000000 : ℝ)/4 ≤ Real.exp ((33415/262144 : ℝ)-(158706887967/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33415/262144 : ℝ) (66831/524288 : ℝ) (158706887967/200000000000 : ℝ) (51372543433/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0759; no trusted numerical premise.
theorem cover8_leaf0759_exp_radius : (39920409336224111/40000000000000000 : ℝ) ≤ Real.exp ((-4177/262144 : ℝ)/8) ∧ Real.exp ((-4177/262144 : ℝ)/8) ≤ (124751279175700347/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4177/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0759_exp_lower : (920113458962634407/1000000000000000000 : ℝ) ≤ Real.exp ((-85256490581569/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256490581569/128000000000000 : ℝ)/8) ≤ (115014182370329301/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256490581569/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0759_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901733283/1000000000000 : ℝ) ≤ 4*Real.exp (66831/524288 : ℝ)*Real.exp (-mu (radius 8 (4177/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901733283/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4177/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0759_exp_radius
  have hrNumeric : (246048070993/250000000000 : ℝ) ≤ Real.exp (-4177/262144 : ℝ) ∧ Real.exp (-4177/262144 : ℝ) ≤ (984192283973/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246048070993/250000000000 : ℝ) ≤ (radius 8 (4177/32768 : ℝ)) ∧ (radius 8 (4177/32768 : ℝ)) ≤ (984192283973/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4177/32768 : ℝ)) (246048070993/250000000000 : ℝ) (984192283973/1000000000000 : ℝ) (177103213319/1000000000000 : ℝ) (7084128533/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4177/32768 : ℝ)) (246048070993/250000000000 : ℝ) (984192283973/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246048070993/250000000000 : ℝ) (984192283973/1000000000000 : ℝ) (496048070993/500000000000 : ℝ) (992096141987/1000000000000 : ℝ) (3875252567/3906250000 : ℝ) (496032328577/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 1 (496048070993/500000000000 : ℝ) (992096141987/1000000000000 : ℝ) (3875252567/3906250000 : ℝ) (496032328577/500000000000 : ℝ) (992080399569/1000000000000 : ℝ) (992080399571/1000000000000 : ℝ) (248020099861/250000000000 : ℝ) (496040199723/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 2 (992080399569/1000000000000 : ℝ) (992080399571/1000000000000 : ℝ) (248020099861/250000000000 : ℝ) (496040199723/500000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 3 (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 4 (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 5 (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 6 (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4177/32768 : ℝ)) 7 (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4177/32768 : ℝ))) (177103213319/1000000000000 : ℝ) (7084128533/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177103213319/1000000000000 : ℝ) (7084128533/40000000000 : ℝ) (588551606659/1000000000000 : ℝ) (588551606663/1000000000000 : ℝ) (105209081511/250000000000 : ℝ) (420836326053/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 1 (588551606659/1000000000000 : ℝ) (588551606663/1000000000000 : ℝ) (105209081511/250000000000 : ℝ) (420836326053/1000000000000 : ℝ) (504693966351/1000000000000 : ℝ) (252346983179/500000000000 : ℝ) (497678506501/1000000000000 : ℝ) (497678506509/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 2 (504693966351/1000000000000 : ℝ) (252346983179/500000000000 : ℝ) (497678506501/1000000000000 : ℝ) (497678506509/1000000000000 : ℝ) (250593118213/500000000000 : ℝ) (250593118217/500000000000 : ℝ) (125293490307/250000000000 : ℝ) (501173961237/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 3 (250593118213/500000000000 : ℝ) (250593118217/500000000000 : ℝ) (125293490307/250000000000 : ℝ) (501173961237/1000000000000 : ℝ) (501180098827/1000000000000 : ℝ) (125295024709/250000000000 : ℝ) (501180098789/1000000000000 : ℝ) (250590049399/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 4 (501180098827/1000000000000 : ℝ) (125295024709/250000000000 : ℝ) (501180098789/1000000000000 : ℝ) (250590049399/500000000000 : ℝ) (62647512351/125000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 5 (62647512351/125000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 6 (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4177/32768 : ℝ))) 7 (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4177/32768 : ℝ)) hmem 8 (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4177/32768 : ℝ))) hcmem 8 (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4177/32768 : ℝ)) (496040199753/500000000000 : ℝ) (992080399509/1000000000000 : ℝ) (501180098807/1000000000000 : ℝ) (501180098817/1000000000000 : ℝ) (99192043641/125000000000 : ℝ) (198384087287/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0759_exp_lower
  have heNumeric : (2054901733283/1000000000000 : ℝ)/4 ≤ Real.exp (-85256490581569/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901733283/1000000000000 : ℝ)/4 ≤ Real.exp ((66831/524288 : ℝ)-(198384087287/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66831/524288 : ℝ) (4177/32768 : ℝ) (198384087287/250000000000 : ℝ) (2054901733283/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0760; no trusted numerical premise.
theorem cover8_leaf0760_exp_radius : (62375637728911281/62500000000000000 : ℝ) ≤ Real.exp ((-66833/4194304 : ℝ)/8) ∧ Real.exp ((-66833/4194304 : ℝ)/8) ≤ (998010203662580497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66833/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0760_exp_lower : (36804538349583187/40000000000000000 : ℝ) ≤ Real.exp ((-5328530676863/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328530676863/8000000000000 : ℝ)/8) ≤ (230028364684894919/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328530676863/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0760_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450864649/500000000000 : ℝ) ≤ 4*Real.exp (4177/32768 : ℝ)*Real.exp (-mu (radius 8 (66833/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450864649/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66833/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0760_exp_radius
  have hrNumeric : (984192049323/1000000000000 : ℝ) ≤ Real.exp (-66833/4194304 : ℝ) ∧ Real.exp (-66833/4194304 : ℝ) ≤ (246048012331/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984192049323/1000000000000 : ℝ) ≤ (radius 8 (66833/524288 : ℝ)) ∧ (radius 8 (66833/524288 : ℝ)) ≤ (246048012331/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66833/524288 : ℝ)) (984192049323/1000000000000 : ℝ) (246048012331/250000000000 : ℝ) (88552258649/500000000000 : ℝ) (22138064663/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66833/524288 : ℝ)) (984192049323/1000000000000 : ℝ) (246048012331/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984192049323/1000000000000 : ℝ) (246048012331/250000000000 : ℝ) (992096024661/1000000000000 : ℝ) (496048012331/500000000000 : ℝ) (992064538889/1000000000000 : ℝ) (992064538891/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 1 (992096024661/1000000000000 : ℝ) (496048012331/500000000000 : ℝ) (992064538889/1000000000000 : ℝ) (992064538891/1000000000000 : ℝ) (39683211271/40000000000 : ℝ) (992080281777/1000000000000 : ℝ) (19841605633/20000000000 : ℝ) (248020070413/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 2 (39683211271/40000000000 : ℝ) (992080281777/1000000000000 : ℝ) (19841605633/20000000000 : ℝ) (248020070413/250000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 3 (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 4 (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 5 (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 6 (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66833/524288 : ℝ)) 7 (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66833/524288 : ℝ))) (88552258649/500000000000 : ℝ) (22138064663/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88552258649/500000000000 : ℝ) (22138064663/125000000000 : ℝ) (588552258649/1000000000000 : ℝ) (147138064663/250000000000 : ℝ) (420837875313/1000000000000 : ℝ) (420837875321/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 1 (588552258649/1000000000000 : ℝ) (147138064663/250000000000 : ℝ) (420837875313/1000000000000 : ℝ) (420837875321/1000000000000 : ℝ) (504695066981/1000000000000 : ℝ) (504695066987/1000000000000 : ℝ) (1555249057/3125000000 : ℝ) (497679698247/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 2 (504695066981/1000000000000 : ℝ) (504695066987/1000000000000 : ℝ) (1555249057/3125000000 : ℝ) (497679698247/1000000000000 : ℝ) (50118738261/100000000000 : ℝ) (501187382617/1000000000000 : ℝ) (6264688847/12500000000 : ℝ) (501175107767/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 3 (50118738261/100000000000 : ℝ) (501187382617/1000000000000 : ℝ) (6264688847/12500000000 : ℝ) (501175107767/1000000000000 : ℝ) (100236249037/200000000000 : ℝ) (62647655649/125000000000 : ℝ) (501181245147/1000000000000 : ℝ) (100236249031/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 4 (100236249037/200000000000 : ℝ) (62647655649/125000000000 : ℝ) (501181245147/1000000000000 : ℝ) (100236249031/200000000000 : ℝ) (250590622583/500000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 5 (250590622583/500000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 6 (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66833/524288 : ℝ))) 7 (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66833/524288 : ℝ)) hmem 8 (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66833/524288 : ℝ))) hcmem 8 (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66833/524288 : ℝ)) (62005017607/62500000000 : ℝ) (198416056343/200000000000 : ℝ) (100236249033/200000000000 : ℝ) (250590622587/500000000000 : ℝ) (396769129209/500000000000 : ℝ) (198384564609/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0760_exp_lower
  have heNumeric : (1027450864649/500000000000 : ℝ)/4 ≤ Real.exp (-5328530676863/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450864649/500000000000 : ℝ)/4 ≤ Real.exp ((4177/32768 : ℝ)-(198384564609/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4177/32768 : ℝ) (66833/524288 : ℝ) (198384564609/250000000000 : ℝ) (1027450864649/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0761; no trusted numerical premise.
theorem cover8_leaf0761_exp_radius : (15593908967493111/15625000000000000 : ℝ) ≤ Real.exp ((-33417/2097152 : ℝ)/8) ∧ Real.exp ((-33417/2097152 : ℝ)/8) ≤ (199602034783911821/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33417/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0761_exp_lower : (460056729258952557/500000000000000000 : ℝ) ≤ Real.exp ((-85256491076511/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256491076511/128000000000000 : ℝ)/8) ≤ (184022691703581023/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256491076511/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0761_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901725337/1000000000000 : ℝ) ≤ 4*Real.exp (66833/524288 : ℝ)*Real.exp (-mu (radius 8 (33417/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901725337/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33417/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0761_exp_radius
  have hrNumeric : (984191814673/1000000000000 : ℝ) ≤ Real.exp (-33417/2097152 : ℝ) ∧ Real.exp (-33417/2097152 : ℝ) ≤ (492095907337/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984191814673/1000000000000 : ℝ) ≤ (radius 8 (33417/262144 : ℝ)) ∧ (radius 8 (33417/262144 : ℝ)) ≤ (492095907337/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33417/262144 : ℝ)) (984191814673/1000000000000 : ℝ) (492095907337/500000000000 : ℝ) (22138227659/125000000000 : ℝ) (177105821279/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33417/262144 : ℝ)) (984191814673/1000000000000 : ℝ) (492095907337/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984191814673/1000000000000 : ℝ) (492095907337/500000000000 : ℝ) (124011988417/125000000000 : ℝ) (992095907337/1000000000000 : ℝ) (496032210313/500000000000 : ℝ) (248016105157/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 1 (124011988417/125000000000 : ℝ) (992095907337/1000000000000 : ℝ) (496032210313/500000000000 : ℝ) (248016105157/250000000000 : ℝ) (992080163981/1000000000000 : ℝ) (992080163983/1000000000000 : ℝ) (62005010241/62500000000 : ℝ) (496040081929/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 2 (992080163981/1000000000000 : ℝ) (992080163983/1000000000000 : ℝ) (62005010241/62500000000 : ℝ) (496040081929/500000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 3 (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 4 (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 5 (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 6 (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33417/262144 : ℝ)) 7 (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33417/262144 : ℝ))) (22138227659/125000000000 : ℝ) (177105821279/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22138227659/125000000000 : ℝ) (177105821279/1000000000000 : ℝ) (147138227659/250000000000 : ℝ) (7356911383/12500000000 : ℝ) (420839424569/1000000000000 : ℝ) (210419712289/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 1 (147138227659/250000000000 : ℝ) (7356911383/12500000000 : ℝ) (420839424569/1000000000000 : ℝ) (210419712289/500000000000 : ℝ) (252348083801/500000000000 : ℝ) (504696167609/1000000000000 : ℝ) (497680889969/1000000000000 : ℝ) (497680889977/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 2 (252348083801/500000000000 : ℝ) (504696167609/1000000000000 : ℝ) (497680889969/1000000000000 : ℝ) (497680889977/1000000000000 : ℝ) (100237705757/200000000000 : ℝ) (501188528793/1000000000000 : ℝ) (501176254281/1000000000000 : ℝ) (50117625429/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 3 (100237705757/200000000000 : ℝ) (501188528793/1000000000000 : ℝ) (501176254281/1000000000000 : ℝ) (50117625429/100000000000 : ℝ) (501182391533/1000000000000 : ℝ) (250591195771/500000000000 : ℝ) (100236478299/200000000000 : ℝ) (31323899469/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 4 (501182391533/1000000000000 : ℝ) (250591195771/500000000000 : ℝ) (100236478299/200000000000 : ℝ) (31323899469/62500000000 : ℝ) (250591195757/500000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 5 (250591195757/500000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 6 (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33417/262144 : ℝ))) 7 (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33417/262144 : ℝ)) hmem 8 (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33417/262144 : ℝ))) hcmem 8 (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33417/262144 : ℝ)) (496040081959/500000000000 : ℝ) (992080163921/1000000000000 : ℝ) (501182391513/1000000000000 : ℝ) (501182391523/1000000000000 : ℝ) (793540167693/1000000000000 : ℝ) (24798130241/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0761_exp_lower
  have heNumeric : (2054901725337/1000000000000 : ℝ)/4 ≤ Real.exp (-85256491076511/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901725337/1000000000000 : ℝ)/4 ≤ Real.exp ((66833/524288 : ℝ)-(24798130241/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66833/524288 : ℝ) (33417/262144 : ℝ) (24798130241/31250000000 : ℝ) (2054901725337/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0762; no trusted numerical premise.
theorem cover8_leaf0762_exp_radius : (499005072088269299/500000000000000000 : ℝ) ≤ Real.exp ((-66835/4194304 : ℝ)/8) ∧ Real.exp ((-66835/4194304 : ℝ)/8) ≤ (998010144176538599/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66835/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0762_exp_lower : (460056729149207911/500000000000000000 : ℝ) ≤ Real.exp ((-42628245660391/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628245660391/64000000000000 : ℝ)/8) ≤ (920113458298415823/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628245660391/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0762_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862715177/125000000000 : ℝ) ≤ 4*Real.exp (33417/262144 : ℝ)*Real.exp (-mu (radius 8 (66835/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862715177/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66835/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0762_exp_radius
  have hrNumeric : (984191580023/1000000000000 : ℝ) ≤ Real.exp (-66835/4194304 : ℝ) ∧ Real.exp (-66835/4194304 : ℝ) ≤ (123023947503/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984191580023/1000000000000 : ℝ) ≤ (radius 8 (66835/524288 : ℝ)) ∧ (radius 8 (66835/524288 : ℝ)) ≤ (123023947503/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66835/524288 : ℝ)) (984191580023/1000000000000 : ℝ) (123023947503/125000000000 : ℝ) (177107125237/1000000000000 : ℝ) (177107125243/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66835/524288 : ℝ)) (984191580023/1000000000000 : ℝ) (123023947503/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984191580023/1000000000000 : ℝ) (123023947503/125000000000 : ℝ) (992095790011/1000000000000 : ℝ) (248023947503/250000000000 : ℝ) (992064302363/1000000000000 : ℝ) (248016075591/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 1 (992095790011/1000000000000 : ℝ) (248023947503/250000000000 : ℝ) (992064302363/1000000000000 : ℝ) (248016075591/250000000000 : ℝ) (992080046187/1000000000000 : ℝ) (248020011547/250000000000 : ℝ) (496040023031/500000000000 : ℝ) (62005002879/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 2 (992080046187/1000000000000 : ℝ) (248020011547/250000000000 : ℝ) (496040023031/500000000000 : ℝ) (62005002879/62500000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 3 (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 4 (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 5 (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 6 (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66835/524288 : ℝ)) 7 (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66835/524288 : ℝ))) (177107125237/1000000000000 : ℝ) (177107125243/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177107125237/1000000000000 : ℝ) (177107125243/1000000000000 : ℝ) (294276781309/500000000000 : ℝ) (294276781311/500000000000 : ℝ) (420840973809/1000000000000 : ℝ) (420840973817/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 1 (294276781309/500000000000 : ℝ) (294276781311/500000000000 : ℝ) (420840973809/1000000000000 : ℝ) (420840973817/1000000000000 : ℝ) (504697268213/1000000000000 : ℝ) (25234863411/50000000000 : ℝ) (99536416337/200000000000 : ℝ) (497682081693/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 2 (504697268213/1000000000000 : ℝ) (25234863411/50000000000 : ℝ) (99536416337/200000000000 : ℝ) (497682081693/1000000000000 : ℝ) (501189674949/1000000000000 : ℝ) (501189674957/1000000000000 : ℝ) (62647175099/125000000000 : ℝ) (626471751/1250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 3 (501189674949/1000000000000 : ℝ) (501189674957/1000000000000 : ℝ) (62647175099/125000000000 : ℝ) (626471751/1250000000 : ℝ) (50118353787/100000000000 : ℝ) (501183537879/1000000000000 : ℝ) (62647942229/125000000000 : ℝ) (501183537841/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 4 (50118353787/100000000000 : ℝ) (501183537879/1000000000000 : ℝ) (62647942229/125000000000 : ℝ) (501183537841/1000000000000 : ℝ) (501183537851/1000000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 5 (501183537851/1000000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 6 (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66835/524288 : ℝ))) 7 (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66835/524288 : ℝ)) hmem 8 (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66835/524288 : ℝ))) hcmem 8 (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66835/524288 : ℝ)) (248020011531/250000000000 : ℝ) (496040023063/500000000000 : ℝ) (10023670757/20000000000 : ℝ) (25059176893/50000000000 : ℝ) (793542076951/1000000000000 : ℝ) (793542076969/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0762_exp_lower
  have heNumeric : (256862715177/125000000000 : ℝ)/4 ≤ Real.exp (-42628245660391/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862715177/125000000000 : ℝ)/4 ≤ Real.exp ((33417/262144 : ℝ)-(793542076969/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33417/262144 : ℝ) (66835/524288 : ℝ) (793542076969/1000000000000 : ℝ) (256862715177/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0763; no trusted numerical premise.
theorem cover8_leaf0763_exp_radius : (499005057216759489/500000000000000000 : ℝ) ≤ Real.exp ((-16709/1048576 : ℝ)/8) ∧ Real.exp ((-16709/1048576 : ℝ)/8) ≤ (998010114433518979/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16709/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0763_exp_lower : (920113458081686871/1000000000000000000 : ℝ) ≤ Real.exp ((-85256491561981/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256491561981/128000000000000 : ℝ)/8) ≤ (115014182260210859/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256491561981/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0763_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862714693/125000000000 : ℝ) ≤ 4*Real.exp (66835/524288 : ℝ)*Real.exp (-mu (radius 8 (16709/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862714693/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16709/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0763_exp_radius
  have hrNumeric : (492095672687/500000000000 : ℝ) ≤ Real.exp (-16709/1048576 : ℝ) ∧ Real.exp (-16709/1048576 : ℝ) ≤ (7873530763/8000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492095672687/500000000000 : ℝ) ≤ (radius 8 (16709/131072 : ℝ)) ∧ (radius 8 (16709/131072 : ℝ)) ≤ (7873530763/8000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16709/131072 : ℝ)) (492095672687/500000000000 : ℝ) (7873530763/8000000000 : ℝ) (88554214593/500000000000 : ℝ) (177108429193/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16709/131072 : ℝ)) (492095672687/500000000000 : ℝ) (7873530763/8000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492095672687/500000000000 : ℝ) (7873530763/8000000000 : ℝ) (992095672687/1000000000000 : ℝ) (62005979543/62500000000 : ℝ) (9920641841/10000000000 : ℝ) (992064184101/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 1 (992095672687/1000000000000 : ℝ) (62005979543/62500000000 : ℝ) (9920641841/10000000000 : ℝ) (992064184101/1000000000000 : ℝ) (992079928393/1000000000000 : ℝ) (198415985679/200000000000 : ℝ) (248019982067/250000000000 : ℝ) (99207992827/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 2 (992079928393/1000000000000 : ℝ) (198415985679/200000000000 : ℝ) (248019982067/250000000000 : ℝ) (99207992827/100000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 3 (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 4 (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 5 (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 6 (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16709/131072 : ℝ)) 7 (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16709/131072 : ℝ))) (88554214593/500000000000 : ℝ) (177108429193/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88554214593/500000000000 : ℝ) (177108429193/1000000000000 : ℝ) (588554214593/1000000000000 : ℝ) (588554214597/1000000000000 : ℝ) (26302657689/62500000000 : ℝ) (210421261517/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 1 (588554214593/1000000000000 : ℝ) (588554214597/1000000000000 : ℝ) (26302657689/62500000000 : ℝ) (210421261517/500000000000 : ℝ) (63087296101/125000000000 : ℝ) (31543648051/62500000000 : ℝ) (497683273383/1000000000000 : ℝ) (31105204587/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 2 (63087296101/125000000000 : ℝ) (31543648051/62500000000 : ℝ) (497683273383/1000000000000 : ℝ) (31105204587/62500000000 : ℝ) (100238164219/200000000000 : ℝ) (31324426319/62500000000 : ℝ) (100235709457/200000000000 : ℝ) (100235709459/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 3 (100238164219/200000000000 : ℝ) (31324426319/62500000000 : ℝ) (100235709457/200000000000 : ℝ) (100235709459/200000000000 : ℝ) (50118468419/100000000000 : ℝ) (2505923421/5000000000 : ℝ) (62648085519/125000000000 : ℝ) (250592342081/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 4 (50118468419/100000000000 : ℝ) (2505923421/5000000000 : ℝ) (62648085519/125000000000 : ℝ) (250592342081/500000000000 : ℝ) (501184684171/1000000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 5 (501184684171/1000000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 6 (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16709/131072 : ℝ))) 7 (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16709/131072 : ℝ)) hmem 8 (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16709/131072 : ℝ))) hcmem 8 (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16709/131072 : ℝ)) (99207992833/100000000000 : ℝ) (992079928333/1000000000000 : ℝ) (50118468417/100000000000 : ℝ) (501184684181/1000000000000 : ℝ) (793543986181/1000000000000 : ℝ) (396771993101/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0763_exp_lower
  have heNumeric : (256862714693/125000000000 : ℝ)/4 ≤ Real.exp (-85256491561981/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862714693/125000000000 : ℝ)/4 ≤ Real.exp ((66835/524288 : ℝ)-(396771993101/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66835/524288 : ℝ) (16709/131072 : ℝ) (396771993101/500000000000 : ℝ) (256862714693/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0764; no trusted numerical premise.
theorem cover8_leaf0764_exp_radius : (199602016938100049/200000000000000000 : ℝ) ≤ Real.exp ((-66837/4194304 : ℝ)/8) ∧ Real.exp ((-66837/4194304 : ℝ)/8) ≤ (499005042345250123/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66837/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0764_exp_lower : (920113457866798147/1000000000000000000 : ℝ) ≤ Real.exp ((-21314122950283/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122950283/32000000000000 : ℝ)/8) ≤ (230028364466699537/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122950283/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0764_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862714213/125000000000 : ℝ) ≤ 4*Real.exp (16709/131072 : ℝ)*Real.exp (-mu (radius 8 (66837/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862714213/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66837/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0764_exp_radius
  have hrNumeric : (246047777681/250000000000 : ℝ) ≤ Real.exp (-66837/4194304 : ℝ) ∧ Real.exp (-66837/4194304 : ℝ) ≤ (39367644429/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246047777681/250000000000 : ℝ) ≤ (radius 8 (66837/524288 : ℝ)) ∧ (radius 8 (66837/524288 : ℝ)) ≤ (39367644429/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66837/524288 : ℝ)) (246047777681/250000000000 : ℝ) (39367644429/40000000000 : ℝ) (177109733131/1000000000000 : ℝ) (177109733137/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66837/524288 : ℝ)) (246047777681/250000000000 : ℝ) (39367644429/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246047777681/250000000000 : ℝ) (39367644429/40000000000 : ℝ) (496047777681/500000000000 : ℝ) (992095555363/1000000000000 : ℝ) (248016016459/250000000000 : ℝ) (992064065837/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 1 (496047777681/500000000000 : ℝ) (992095555363/1000000000000 : ℝ) (248016016459/250000000000 : ℝ) (992064065837/1000000000000 : ℝ) (992079810599/1000000000000 : ℝ) (4960399053/5000000000 : ℝ) (496039905237/500000000000 : ℝ) (248019952619/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 2 (992079810599/1000000000000 : ℝ) (4960399053/5000000000 : ℝ) (496039905237/500000000000 : ℝ) (248019952619/250000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 3 (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 4 (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 5 (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 6 (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66837/524288 : ℝ)) 7 (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66837/524288 : ℝ))) (177109733131/1000000000000 : ℝ) (177109733137/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177109733131/1000000000000 : ℝ) (177109733137/1000000000000 : ℝ) (117710973313/200000000000 : ℝ) (588554866569/1000000000000 : ℝ) (420844072229/1000000000000 : ℝ) (420844072237/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 1 (117710973313/200000000000 : ℝ) (588554866569/1000000000000 : ℝ) (420844072229/1000000000000 : ℝ) (420844072237/1000000000000 : ℝ) (504699469397/1000000000000 : ℝ) (504699469403/1000000000000 : ℝ) (497684465073/1000000000000 : ℝ) (12442111627/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 2 (504699469397/1000000000000 : ℝ) (504699469403/1000000000000 : ℝ) (497684465073/1000000000000 : ℝ) (12442111627/25000000000 : ℝ) (100238393447/200000000000 : ℝ) (250595983621/500000000000 : ℝ) (125294923443/250000000000 : ℝ) (501179693779/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 3 (100238393447/200000000000 : ℝ) (250595983621/500000000000 : ℝ) (125294923443/250000000000 : ℝ) (501179693779/1000000000000 : ℝ) (501185830503/1000000000000 : ℝ) (501185830511/1000000000000 : ℝ) (100237166093/200000000000 : ℝ) (501185830473/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 4 (501185830503/1000000000000 : ℝ) (501185830511/1000000000000 : ℝ) (100237166093/200000000000 : ℝ) (501185830473/1000000000000 : ℝ) (125296457621/250000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 5 (125296457621/250000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 6 (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66837/524288 : ℝ))) 7 (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66837/524288 : ℝ)) hmem 8 (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66837/524288 : ℝ))) hcmem 8 (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66837/524288 : ℝ)) (124009976317/125000000000 : ℝ) (496039905269/500000000000 : ℝ) (501185830483/1000000000000 : ℝ) (125296457623/250000000000 : ℝ) (396772947701/500000000000 : ℝ) (793545895419/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0764_exp_lower
  have heNumeric : (256862714213/125000000000 : ℝ)/4 ≤ Real.exp (-21314122950283/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862714213/125000000000 : ℝ)/4 ≤ Real.exp ((16709/131072 : ℝ)-(793545895419/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16709/131072 : ℝ) (66837/524288 : ℝ) (793545895419/1000000000000 : ℝ) (256862714213/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0765; no trusted numerical premise.
theorem cover8_leaf0765_exp_radius : (499005027473741199/500000000000000000 : ℝ) ≤ Real.exp ((-33419/2097152 : ℝ)/8) ∧ Real.exp ((-33419/2097152 : ℝ)/8) ≤ (998010054947482399/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33419/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0765_exp_lower : (920113457654324721/1000000000000000000 : ℝ) ≤ Real.exp ((-17051298407519/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051298407519/25600000000000 : ℝ)/8) ≤ (460056728827162361/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051298407519/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0765_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725427477/250000000000 : ℝ) ≤ 4*Real.exp (66837/524288 : ℝ)*Real.exp (-mu (radius 8 (33419/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725427477/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33419/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0765_exp_radius
  have hrNumeric : (39367635043/40000000000 : ℝ) ≤ Real.exp (-33419/2097152 : ℝ) ∧ Real.exp (-33419/2097152 : ℝ) ≤ (246047719019/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39367635043/40000000000 : ℝ) ≤ (radius 8 (33419/262144 : ℝ)) ∧ (radius 8 (33419/262144 : ℝ)) ≤ (246047719019/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33419/262144 : ℝ)) (39367635043/40000000000 : ℝ) (246047719019/250000000000 : ℝ) (8855551853/50000000000 : ℝ) (177111037067/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33419/262144 : ℝ)) (39367635043/40000000000 : ℝ) (246047719019/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39367635043/40000000000 : ℝ) (246047719019/250000000000 : ℝ) (992095438037/1000000000000 : ℝ) (496047719019/500000000000 : ℝ) (992063947573/1000000000000 : ℝ) (496031973787/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 1 (992095438037/1000000000000 : ℝ) (496047719019/500000000000 : ℝ) (992063947573/1000000000000 : ℝ) (496031973787/500000000000 : ℝ) (198415938561/200000000000 : ℝ) (496039846403/500000000000 : ℝ) (24801992317/25000000000 : ℝ) (496039846341/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 2 (198415938561/200000000000 : ℝ) (496039846403/500000000000 : ℝ) (24801992317/25000000000 : ℝ) (496039846341/500000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 3 (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 4 (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 5 (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 6 (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33419/262144 : ℝ)) 7 (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33419/262144 : ℝ))) (8855551853/50000000000 : ℝ) (177111037067/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8855551853/50000000000 : ℝ) (177111037067/1000000000000 : ℝ) (58855551853/100000000000 : ℝ) (294277759267/500000000000 : ℝ) (42084562141/100000000000 : ℝ) (420845621419/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 1 (58855551853/100000000000 : ℝ) (294277759267/500000000000 : ℝ) (42084562141/100000000000 : ℝ) (420845621419/1000000000000 : ℝ) (50470056997/100000000000 : ℝ) (504700569977/1000000000000 : ℝ) (99537131349/200000000000 : ℝ) (497685656753/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 2 (50470056997/100000000000 : ℝ) (504700569977/1000000000000 : ℝ) (99537131349/200000000000 : ℝ) (497685656753/1000000000000 : ℝ) (501193113357/1000000000000 : ℝ) (100238622673/200000000000 : ℝ) (501180840241/1000000000000 : ℝ) (501180840249/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 3 (501193113357/1000000000000 : ℝ) (100238622673/200000000000 : ℝ) (501180840241/1000000000000 : ℝ) (501180840249/1000000000000 : ℝ) (501186976799/1000000000000 : ℝ) (501186976807/1000000000000 : ℝ) (501186976761/1000000000000 : ℝ) (50118697677/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 4 (501186976799/1000000000000 : ℝ) (501186976807/1000000000000 : ℝ) (501186976761/1000000000000 : ℝ) (50118697677/100000000000 : ℝ) (25059348839/50000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 5 (25059348839/50000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 6 (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33419/262144 : ℝ))) 7 (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33419/262144 : ℝ)) hmem 8 (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33419/262144 : ℝ))) hcmem 8 (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33419/262144 : ℝ)) (496039846371/500000000000 : ℝ) (124009961593/125000000000 : ℝ) (501186976779/1000000000000 : ℝ) (501186976789/1000000000000 : ℝ) (198386951149/250000000000 : ℝ) (158709560923/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0765_exp_lower
  have heNumeric : (513725427477/250000000000 : ℝ)/4 ≤ Real.exp (-17051298407519/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725427477/250000000000 : ℝ)/4 ≤ Real.exp ((66837/524288 : ℝ)-(158709560923/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66837/524288 : ℝ) (33419/262144 : ℝ) (158709560923/200000000000 : ℝ) (513725427477/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0766; no trusted numerical premise.
theorem cover8_leaf0766_exp_radius : (998010025204465437/1000000000000000000 : ℝ) ≤ Real.exp ((-66839/4194304 : ℝ)/8) ∧ Real.exp ((-66839/4194304 : ℝ)/8) ≤ (499005012602232719/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66839/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0766_exp_lower : (184022691488922327/200000000000000000 : ℝ) ≤ Real.exp ((-42628246135493/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628246135493/64000000000000 : ℝ)/8) ≤ (230028364361152909/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628246135493/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0766_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901706161/1000000000000 : ℝ) ≤ 4*Real.exp (33419/262144 : ℝ)*Real.exp (-mu (radius 8 (66839/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901706161/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66839/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0766_exp_radius
  have hrNumeric : (492095320713/500000000000 : ℝ) ≤ Real.exp (-66839/4194304 : ℝ) ∧ Real.exp (-66839/4194304 : ℝ) ≤ (984190641427/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492095320713/500000000000 : ℝ) ≤ (radius 8 (66839/524288 : ℝ)) ∧ (radius 8 (66839/524288 : ℝ)) ≤ (984190641427/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66839/524288 : ℝ)) (492095320713/500000000000 : ℝ) (984190641427/1000000000000 : ℝ) (8855617049/50000000000 : ℝ) (88556170493/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66839/524288 : ℝ)) (492095320713/500000000000 : ℝ) (984190641427/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492095320713/500000000000 : ℝ) (984190641427/1000000000000 : ℝ) (992095320713/1000000000000 : ℝ) (496047660357/500000000000 : ℝ) (99206382931/100000000000 : ℝ) (992063829311/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 1 (992095320713/1000000000000 : ℝ) (496047660357/500000000000 : ℝ) (99206382931/100000000000 : ℝ) (992063829311/1000000000000 : ℝ) (992079575011/1000000000000 : ℝ) (992079575013/1000000000000 : ℝ) (496039787443/500000000000 : ℝ) (124009946861/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 2 (992079575011/1000000000000 : ℝ) (992079575013/1000000000000 : ℝ) (496039787443/500000000000 : ℝ) (124009946861/125000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 3 (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 4 (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 5 (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 6 (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66839/524288 : ℝ)) 7 (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66839/524288 : ℝ))) (8855617049/50000000000 : ℝ) (88556170493/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8855617049/50000000000 : ℝ) (88556170493/500000000000 : ℝ) (58855617049/100000000000 : ℝ) (588556170493/1000000000000 : ℝ) (420847170573/1000000000000 : ℝ) (420847170581/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 1 (58855617049/100000000000 : ℝ) (588556170493/1000000000000 : ℝ) (420847170573/1000000000000 : ℝ) (420847170581/1000000000000 : ℝ) (504701670531/1000000000000 : ℝ) (504701670537/1000000000000 : ℝ) (497686848403/1000000000000 : ℝ) (49768684841/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 2 (504701670531/1000000000000 : ℝ) (504701670537/1000000000000 : ℝ) (497686848403/1000000000000 : ℝ) (49768684841/100000000000 : ℝ) (501194259467/1000000000000 : ℝ) (250597129737/500000000000 : ℝ) (501181986697/1000000000000 : ℝ) (100236397341/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 3 (501194259467/1000000000000 : ℝ) (250597129737/500000000000 : ℝ) (501181986697/1000000000000 : ℝ) (100236397341/200000000000 : ℝ) (250594061541/500000000000 : ℝ) (50118812309/100000000000 : ℝ) (125297030761/250000000000 : ℝ) (125297030763/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 4 (250594061541/500000000000 : ℝ) (50118812309/100000000000 : ℝ) (125297030761/250000000000 : ℝ) (125297030763/250000000000 : ℝ) (501188123063/1000000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 5 (501188123063/1000000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 6 (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66839/524288 : ℝ))) 7 (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66839/524288 : ℝ)) hmem 8 (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66839/524288 : ℝ))) hcmem 8 (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66839/524288 : ℝ)) (248019893737/250000000000 : ℝ) (992079574951/1000000000000 : ℝ) (250594061531/500000000000 : ℝ) (501188123071/1000000000000 : ℝ) (793549713769/1000000000000 : ℝ) (793549713787/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0766_exp_lower
  have heNumeric : (2054901706161/1000000000000 : ℝ)/4 ≤ Real.exp (-42628246135493/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901706161/1000000000000 : ℝ)/4 ≤ Real.exp ((33419/262144 : ℝ)-(793549713787/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33419/262144 : ℝ) (66839/524288 : ℝ) (793549713787/1000000000000 : ℝ) (2054901706161/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0767; no trusted numerical premise.
theorem cover8_leaf0767_exp_radius : (998009995461449363/1000000000000000000 : ℝ) ≤ Real.exp ((-8355/524288 : ℝ)/8) ∧ Real.exp ((-8355/524288 : ℝ)/8) ≤ (249502498865362341/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8355/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0767_exp_lower : (460056728617909331/500000000000000000 : ℝ) ≤ Real.exp ((-85256492503353/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256492503353/128000000000000 : ℝ)/8) ≤ (920113457235818663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256492503353/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0767_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901702431/1000000000000 : ℝ) ≤ 4*Real.exp (66839/524288 : ℝ)*Real.exp (-mu (radius 8 (8355/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901702431/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8355/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0767_exp_radius
  have hrNumeric : (123023800847/125000000000 : ℝ) ≤ Real.exp (-8355/524288 : ℝ) ∧ Real.exp (-8355/524288 : ℝ) ≤ (984190406777/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123023800847/125000000000 : ℝ) ≤ (radius 8 (8355/65536 : ℝ)) ∧ (radius 8 (8355/65536 : ℝ)) ≤ (984190406777/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8355/65536 : ℝ)) (123023800847/125000000000 : ℝ) (984190406777/1000000000000 : ℝ) (35422728979/200000000000 : ℝ) (177113644901/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8355/65536 : ℝ)) (123023800847/125000000000 : ℝ) (984190406777/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123023800847/125000000000 : ℝ) (984190406777/1000000000000 : ℝ) (248023800847/250000000000 : ℝ) (992095203389/1000000000000 : ℝ) (496031855523/500000000000 : ℝ) (124007963881/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 1 (248023800847/250000000000 : ℝ) (992095203389/1000000000000 : ℝ) (496031855523/500000000000 : ℝ) (124007963881/125000000000 : ℝ) (992079457217/1000000000000 : ℝ) (992079457219/1000000000000 : ℝ) (248019864273/250000000000 : ℝ) (496039728547/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 2 (992079457217/1000000000000 : ℝ) (992079457219/1000000000000 : ℝ) (248019864273/250000000000 : ℝ) (496039728547/500000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 3 (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 4 (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 5 (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 6 (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8355/65536 : ℝ)) 7 (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8355/65536 : ℝ))) (35422728979/200000000000 : ℝ) (177113644901/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35422728979/200000000000 : ℝ) (177113644901/1000000000000 : ℝ) (588556822447/1000000000000 : ℝ) (588556822451/1000000000000 : ℝ) (16833948789/40000000000 : ℝ) (210424359867/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 1 (588556822447/1000000000000 : ℝ) (588556822451/1000000000000 : ℝ) (16833948789/40000000000 : ℝ) (210424359867/500000000000 : ℝ) (252351385543/500000000000 : ℝ) (504702771093/1000000000000 : ℝ) (497688040053/1000000000000 : ℝ) (497688040061/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 2 (252351385543/500000000000 : ℝ) (504702771093/1000000000000 : ℝ) (497688040053/1000000000000 : ℝ) (497688040061/1000000000000 : ℝ) (501195405569/1000000000000 : ℝ) (501195405577/1000000000000 : ℝ) (501183133147/1000000000000 : ℝ) (100236626631/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 3 (501195405569/1000000000000 : ℝ) (501195405577/1000000000000 : ℝ) (501183133147/1000000000000 : ℝ) (100236626631/200000000000 : ℝ) (250594634679/500000000000 : ℝ) (250594634683/500000000000 : ℝ) (12529731733/25000000000 : ℝ) (501189269329/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 4 (250594634679/500000000000 : ℝ) (250594634683/500000000000 : ℝ) (12529731733/25000000000 : ℝ) (501189269329/1000000000000 : ℝ) (501189269339/1000000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 5 (501189269339/1000000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 6 (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8355/65536 : ℝ))) 7 (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8355/65536 : ℝ)) hmem 8 (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8355/65536 : ℝ))) hcmem 8 (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8355/65536 : ℝ)) (496039728577/500000000000 : ℝ) (992079457157/1000000000000 : ℝ) (250594634669/500000000000 : ℝ) (125297317337/250000000000 : ℝ) (198387905733/250000000000 : ℝ) (793551622951/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0767_exp_lower
  have heNumeric : (2054901702431/1000000000000 : ℝ)/4 ≤ Real.exp (-85256492503353/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901702431/1000000000000 : ℝ)/4 ≤ Real.exp ((66839/524288 : ℝ)-(793551622951/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66839/524288 : ℝ) (8355/65536 : ℝ) (793551622951/1000000000000 : ℝ) (2054901702431/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0768; no trusted numerical premise.
theorem cover8_leaf0768_exp_radius : (39920398628737367/40000000000000000 : ℝ) ≤ Real.exp ((-66841/4194304 : ℝ)/8) ∧ Real.exp ((-66841/4194304 : ℝ)/8) ≤ (7796952857175267/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-66841/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0768_exp_lower : (920113457030131073/1000000000000000000 : ℝ) ≤ Real.exp ((-10657061591533/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657061591533/16000000000000 : ℝ)/8) ≤ (460056728515065537/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657061591533/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0768_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725424689/250000000000 : ℝ) ≤ 4*Real.exp (8355/65536 : ℝ)*Real.exp (-mu (radius 8 (66841/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725424689/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66841/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0768_exp_radius
  have hrNumeric : (984190172127/1000000000000 : ℝ) ≤ Real.exp (-66841/4194304 : ℝ) ∧ Real.exp (-66841/4194304 : ℝ) ≤ (30755942879/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984190172127/1000000000000 : ℝ) ≤ (radius 8 (66841/524288 : ℝ)) ∧ (radius 8 (66841/524288 : ℝ)) ≤ (30755942879/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66841/524288 : ℝ)) (984190172127/1000000000000 : ℝ) (30755942879/31250000000 : ℝ) (35422989759/200000000000 : ℝ) (177114948801/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66841/524288 : ℝ)) (984190172127/1000000000000 : ℝ) (30755942879/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984190172127/1000000000000 : ℝ) (30755942879/31250000000 : ℝ) (992095086063/1000000000000 : ℝ) (62005942879/62500000000 : ℝ) (992063592783/1000000000000 : ℝ) (198412718557/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 1 (992095086063/1000000000000 : ℝ) (62005942879/62500000000 : ℝ) (992063592783/1000000000000 : ℝ) (198412718557/200000000000 : ℝ) (992079339423/1000000000000 : ℝ) (39683173577/40000000000 : ℝ) (496039669649/500000000000 : ℝ) (9920793393/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 2 (992079339423/1000000000000 : ℝ) (39683173577/40000000000 : ℝ) (496039669649/500000000000 : ℝ) (9920793393/10000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 3 (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 4 (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 5 (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 6 (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66841/524288 : ℝ)) 7 (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66841/524288 : ℝ))) (35422989759/200000000000 : ℝ) (177114948801/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35422989759/200000000000 : ℝ) (177114948801/1000000000000 : ℝ) (588557474397/1000000000000 : ℝ) (588557474401/1000000000000 : ℝ) (210425134427/500000000000 : ℝ) (210425134431/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 1 (588557474397/1000000000000 : ℝ) (588557474401/1000000000000 : ℝ) (210425134427/500000000000 : ℝ) (210425134431/500000000000 : ℝ) (4037630973/8000000000 : ℝ) (31543991977/62500000000 : ℝ) (99537846337/200000000000 : ℝ) (497689231693/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 2 (4037630973/8000000000 : ℝ) (31543991977/62500000000 : ℝ) (99537846337/200000000000 : ℝ) (497689231693/1000000000000 : ℝ) (100239310331/200000000000 : ℝ) (501196551663/1000000000000 : ℝ) (501184279579/1000000000000 : ℝ) (501184279587/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 3 (100239310331/200000000000 : ℝ) (501196551663/1000000000000 : ℝ) (501184279579/1000000000000 : ℝ) (501184279587/1000000000000 : ℝ) (501190415617/1000000000000 : ℝ) (160380933/320000000 : ℝ) (501190415579/1000000000000 : ℝ) (125297603897/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 4 (501190415617/1000000000000 : ℝ) (160380933/320000000 : ℝ) (501190415579/1000000000000 : ℝ) (125297603897/250000000000 : ℝ) (250595207799/500000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 5 (250595207799/500000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 6 (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66841/524288 : ℝ))) 7 (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66841/524288 : ℝ)) hmem 8 (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66841/524288 : ℝ))) hcmem 8 (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66841/524288 : ℝ)) (6200495871/6250000000 : ℝ) (992079339363/1000000000000 : ℝ) (501190415597/1000000000000 : ℝ) (501190415607/1000000000000 : ℝ) (793553532069/1000000000000 : ℝ) (99194191511/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0768_exp_lower
  have heNumeric : (513725424689/250000000000 : ℝ)/4 ≤ Real.exp (-10657061591533/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725424689/250000000000 : ℝ)/4 ≤ Real.exp ((8355/65536 : ℝ)-(99194191511/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8355/65536 : ℝ) (66841/524288 : ℝ) (99194191511/125000000000 : ℝ) (513725424689/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0769; no trusted numerical premise.
theorem cover8_leaf0769_exp_radius : (499004967987709937/500000000000000000 : ℝ) ≤ Real.exp ((-33421/2097152 : ℝ)/8) ∧ Real.exp ((-33421/2097152 : ℝ)/8) ≤ (7984079487803359/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33421/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0769_exp_lower : (920113456826628753/1000000000000000000 : ℝ) ≤ Real.exp ((-85256492958743/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256492958743/128000000000000 : ℝ)/8) ≤ (460056728413314377/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256492958743/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0769_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686271189/12500000000 : ℝ) ≤ 4*Real.exp (66841/524288 : ℝ)*Real.exp (-mu (radius 8 (33421/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (25686271189/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33421/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0769_exp_radius
  have hrNumeric : (492094968739/500000000000 : ℝ) ≤ Real.exp (-33421/2097152 : ℝ) ∧ Real.exp (-33421/2097152 : ℝ) ≤ (984189937479/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492094968739/500000000000 : ℝ) ≤ (radius 8 (33421/262144 : ℝ)) ∧ (radius 8 (33421/262144 : ℝ)) ≤ (984189937479/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33421/262144 : ℝ)) (492094968739/500000000000 : ℝ) (984189937479/1000000000000 : ℝ) (44279063171/250000000000 : ℝ) (177116252691/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33421/262144 : ℝ)) (492094968739/500000000000 : ℝ) (984189937479/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492094968739/500000000000 : ℝ) (984189937479/1000000000000 : ℝ) (992094968739/1000000000000 : ℝ) (49604748437/50000000000 : ℝ) (24801586863/25000000000 : ℝ) (496031737261/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 1 (992094968739/1000000000000 : ℝ) (49604748437/50000000000 : ℝ) (24801586863/25000000000 : ℝ) (496031737261/500000000000 : ℝ) (992079221629/1000000000000 : ℝ) (992079221631/1000000000000 : ℝ) (3875309459/3906250000 : ℝ) (992079221507/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 2 (992079221629/1000000000000 : ℝ) (992079221631/1000000000000 : ℝ) (3875309459/3906250000 : ℝ) (992079221507/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 3 (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 4 (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 5 (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 6 (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33421/262144 : ℝ)) 7 (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33421/262144 : ℝ))) (44279063171/250000000000 : ℝ) (177116252691/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44279063171/250000000000 : ℝ) (177116252691/1000000000000 : ℝ) (294279063171/500000000000 : ℝ) (294279063173/500000000000 : ℝ) (105212954491/250000000000 : ℝ) (420851817973/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 1 (294279063171/500000000000 : ℝ) (294279063173/500000000000 : ℝ) (105212954491/250000000000 : ℝ) (420851817973/1000000000000 : ℝ) (504704972153/1000000000000 : ℝ) (788601519/1562500000 : ℝ) (62211302913/125000000000 : ℝ) (31105651457/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 2 (504704972153/1000000000000 : ℝ) (788601519/1562500000 : ℝ) (62211302913/125000000000 : ℝ) (31105651457/62500000000 : ℝ) (7831214027/15625000000 : ℝ) (62649712217/125000000000 : ℝ) (501185425999/1000000000000 : ℝ) (62648178251/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 3 (7831214027/15625000000 : ℝ) (62649712217/125000000000 : ℝ) (501185425999/1000000000000 : ℝ) (62648178251/125000000000 : ℝ) (501191561863/1000000000000 : ℝ) (31324472617/62500000000 : ℝ) (20047662473/40000000000 : ℝ) (100238312367/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 4 (501191561863/1000000000000 : ℝ) (31324472617/62500000000 : ℝ) (20047662473/40000000000 : ℝ) (100238312367/200000000000 : ℝ) (125297890461/250000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 5 (125297890461/250000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 6 (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33421/262144 : ℝ))) 7 (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33421/262144 : ℝ)) hmem 8 (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33421/262144 : ℝ))) hcmem 8 (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33421/262144 : ℝ)) (496039610783/500000000000 : ℝ) (992079221569/1000000000000 : ℝ) (501191561843/1000000000000 : ℝ) (250595780927/500000000000 : ℝ) (158711088237/200000000000 : ℝ) (396777720603/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0769_exp_lower
  have heNumeric : (25686271189/12500000000 : ℝ)/4 ≤ Real.exp (-85256492958743/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686271189/12500000000 : ℝ)/4 ≤ Real.exp ((66841/524288 : ℝ)-(396777720603/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66841/524288 : ℝ) (33421/262144 : ℝ) (396777720603/500000000000 : ℝ) (25686271189/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0770; no trusted numerical premise.
theorem cover8_leaf0770_exp_radius : (998009906232406459/1000000000000000000 : ℝ) ≤ Real.exp ((-66843/4194304 : ℝ)/8) ∧ Real.exp ((-66843/4194304 : ℝ)/8) ≤ (49900495311620323/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66843/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0770_exp_lower : (920113456625426717/1000000000000000000 : ℝ) ≤ Real.exp ((-42628246591331/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628246591331/64000000000000 : ℝ)/8) ≤ (460056728312713359/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628246591331/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0770_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196067661/40000000000 : ℝ) ≤ 4*Real.exp (33421/262144 : ℝ)*Real.exp (-mu (radius 8 (66843/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (82196067661/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66843/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0770_exp_radius
  have hrNumeric : (984189702829/1000000000000 : ℝ) ≤ Real.exp (-66843/4194304 : ℝ) ∧ Real.exp (-66843/4194304 : ℝ) ≤ (98418970283/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984189702829/1000000000000 : ℝ) ≤ (radius 8 (66843/524288 : ℝ)) ∧ (radius 8 (66843/524288 : ℝ)) ≤ (98418970283/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66843/524288 : ℝ)) (984189702829/1000000000000 : ℝ) (98418970283/100000000000 : ℝ) (44279389141/250000000000 : ℝ) (177117556571/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66843/524288 : ℝ)) (984189702829/1000000000000 : ℝ) (98418970283/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984189702829/1000000000000 : ℝ) (98418970283/100000000000 : ℝ) (496047425707/500000000000 : ℝ) (198418970283/200000000000 : ℝ) (992063356257/1000000000000 : ℝ) (992063356259/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 1 (496047425707/500000000000 : ℝ) (198418970283/200000000000 : ℝ) (992063356257/1000000000000 : ℝ) (992063356259/1000000000000 : ℝ) (198415820767/200000000000 : ℝ) (992079103837/1000000000000 : ℝ) (99207910371/100000000000 : ℝ) (992079103713/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 2 (198415820767/200000000000 : ℝ) (992079103837/1000000000000 : ℝ) (99207910371/100000000000 : ℝ) (992079103713/1000000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 3 (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 4 (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 5 (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 6 (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66843/524288 : ℝ)) 7 (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66843/524288 : ℝ))) (44279389141/250000000000 : ℝ) (177117556571/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44279389141/250000000000 : ℝ) (177117556571/1000000000000 : ℝ) (294279389141/500000000000 : ℝ) (294279389143/500000000000 : ℝ) (420853367057/1000000000000 : ℝ) (420853367067/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 1 (294279389141/500000000000 : ℝ) (294279389143/500000000000 : ℝ) (420853367057/1000000000000 : ℝ) (420853367067/1000000000000 : ℝ) (504706072669/1000000000000 : ℝ) (504706072677/1000000000000 : ℝ) (497691614909/1000000000000 : ℝ) (497691614917/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 2 (504706072669/1000000000000 : ℝ) (504706072677/1000000000000 : ℝ) (497691614909/1000000000000 : ℝ) (497691614917/1000000000000 : ℝ) (501198843789/1000000000000 : ℝ) (501198843797/1000000000000 : ℝ) (250593286203/500000000000 : ℝ) (100237314483/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 3 (501198843789/1000000000000 : ℝ) (501198843797/1000000000000 : ℝ) (250593286203/500000000000 : ℝ) (100237314483/200000000000 : ℝ) (501192708097/1000000000000 : ℝ) (250596354053/500000000000 : ℝ) (501192708059/1000000000000 : ℝ) (501192708069/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 4 (501192708097/1000000000000 : ℝ) (250596354053/500000000000 : ℝ) (501192708059/1000000000000 : ℝ) (501192708069/1000000000000 : ℝ) (250596354039/500000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 5 (250596354039/500000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 6 (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66843/524288 : ℝ))) 7 (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66843/524288 : ℝ)) hmem 8 (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66843/524288 : ℝ))) hcmem 8 (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66843/524288 : ℝ)) (248019775943/250000000000 : ℝ) (39683164151/40000000000 : ℝ) (501192708077/1000000000000 : ℝ) (62649088511/125000000000 : ℝ) (793557350283/1000000000000 : ℝ) (24798667197/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0770_exp_lower
  have heNumeric : (82196067661/40000000000 : ℝ)/4 ≤ Real.exp (-42628246591331/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196067661/40000000000 : ℝ)/4 ≤ Real.exp ((33421/262144 : ℝ)-(24798667197/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33421/262144 : ℝ) (66843/524288 : ℝ) (24798667197/31250000000 : ℝ) (82196067661/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0771; no trusted numerical premise.
theorem cover8_leaf0771_exp_radius : (998009876489393931/1000000000000000000 : ℝ) ≤ Real.exp ((-16711/1048576 : ℝ)/8) ∧ Real.exp ((-16711/1048576 : ℝ)/8) ≤ (249502469122348483/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16711/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0771_exp_lower : (18402269128528199/20000000000000000 : ℝ) ≤ Real.exp ((-85256493404149/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256493404149/128000000000000 : ℝ)/8) ≤ (920113456426409951/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256493404149/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0771_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490168797/100000000000 : ℝ) ≤ 4*Real.exp (66843/524288 : ℝ)*Real.exp (-mu (radius 8 (16711/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490168797/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16711/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0771_exp_radius
  have hrNumeric : (49209473409/50000000000 : ℝ) ≤ Real.exp (-16711/1048576 : ℝ) ∧ Real.exp (-16711/1048576 : ℝ) ≤ (984189468181/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49209473409/50000000000 : ℝ) ≤ (radius 8 (16711/131072 : ℝ)) ∧ (radius 8 (16711/131072 : ℝ)) ≤ (984189468181/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16711/131072 : ℝ)) (49209473409/50000000000 : ℝ) (984189468181/1000000000000 : ℝ) (88559430217/500000000000 : ℝ) (177118860441/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16711/131072 : ℝ)) (49209473409/50000000000 : ℝ) (984189468181/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49209473409/50000000000 : ℝ) (984189468181/1000000000000 : ℝ) (99209473409/100000000000 : ℝ) (992094734091/1000000000000 : ℝ) (496031618997/500000000000 : ℝ) (198412647599/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 1 (99209473409/100000000000 : ℝ) (992094734091/1000000000000 : ℝ) (496031618997/500000000000 : ℝ) (198412647599/200000000000 : ℝ) (496039493021/500000000000 : ℝ) (992078986043/1000000000000 : ℝ) (992078985917/1000000000000 : ℝ) (992078985919/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 2 (496039493021/500000000000 : ℝ) (992078986043/1000000000000 : ℝ) (992078985917/1000000000000 : ℝ) (992078985919/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 3 (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 4 (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 5 (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 6 (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16711/131072 : ℝ)) 7 (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16711/131072 : ℝ))) (88559430217/500000000000 : ℝ) (177118860441/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88559430217/500000000000 : ℝ) (177118860441/1000000000000 : ℝ) (588559430217/1000000000000 : ℝ) (588559430221/1000000000000 : ℝ) (420854916133/1000000000000 : ℝ) (420854916143/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 1 (588559430217/1000000000000 : ℝ) (588559430221/1000000000000 : ℝ) (420854916133/1000000000000 : ℝ) (420854916143/1000000000000 : ℝ) (20188286927/40000000000 : ℝ) (252353586591/500000000000 : ℝ) (497692806501/1000000000000 : ℝ) (49769280651/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 2 (20188286927/40000000000 : ℝ) (252353586591/500000000000 : ℝ) (497692806501/1000000000000 : ℝ) (49769280651/100000000000 : ℝ) (250599994919/500000000000 : ℝ) (250599994923/500000000000 : ℝ) (250593859401/500000000000 : ℝ) (501187718811/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 3 (250599994919/500000000000 : ℝ) (250599994923/500000000000 : ℝ) (250593859401/500000000000 : ℝ) (501187718811/1000000000000 : ℝ) (6264923179/12500000000 : ℝ) (501193854329/1000000000000 : ℝ) (250596927141/500000000000 : ℝ) (501193854291/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 4 (6264923179/12500000000 : ℝ) (501193854329/1000000000000 : ℝ) (250596927141/500000000000 : ℝ) (501193854291/1000000000000 : ℝ) (501193854301/1000000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 5 (501193854301/1000000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 6 (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16711/131072 : ℝ))) 7 (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16711/131072 : ℝ)) hmem 8 (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16711/131072 : ℝ))) hcmem 8 (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16711/131072 : ℝ)) (992078985979/1000000000000 : ℝ) (992078985981/1000000000000 : ℝ) (5011938543/10000000000 : ℝ) (50119385431/100000000000 : ℝ) (198389814841/250000000000 : ℝ) (793559259383/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0771_exp_lower
  have heNumeric : (205490168797/100000000000 : ℝ)/4 ≤ Real.exp (-85256493404149/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490168797/100000000000 : ℝ)/4 ≤ Real.exp ((66843/524288 : ℝ)-(793559259383/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66843/524288 : ℝ) (16711/131072 : ℝ) (793559259383/1000000000000 : ℝ) (205490168797/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0772; no trusted numerical premise.
theorem cover8_leaf0772_exp_radius : (998009846746382289/1000000000000000000 : ℝ) ≤ Real.exp ((-66845/4194304 : ℝ)/8) ∧ Real.exp ((-66845/4194304 : ℝ)/8) ≤ (99800984674638229/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66845/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0772_exp_lower : (920113456229463439/1000000000000000000 : ℝ) ≤ Real.exp ((-21314123405833/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314123405833/32000000000000 : ℝ)/8) ≤ (11501418202868293/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314123405833/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0772_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901684451/1000000000000 : ℝ) ≤ 4*Real.exp (16711/131072 : ℝ)*Real.exp (-mu (radius 8 (66845/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901684451/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66845/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0772_exp_radius
  have hrNumeric : (984189233531/1000000000000 : ℝ) ≤ Real.exp (-66845/4194304 : ℝ) ∧ Real.exp (-66845/4194304 : ℝ) ≤ (246047308383/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984189233531/1000000000000 : ℝ) ≤ (radius 8 (66845/524288 : ℝ)) ∧ (radius 8 (66845/524288 : ℝ)) ≤ (246047308383/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66845/524288 : ℝ)) (984189233531/1000000000000 : ℝ) (246047308383/250000000000 : ℝ) (88560082147/500000000000 : ℝ) (177120164301/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66845/524288 : ℝ)) (984189233531/1000000000000 : ℝ) (246047308383/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984189233531/1000000000000 : ℝ) (246047308383/250000000000 : ℝ) (198418923353/200000000000 : ℝ) (496047308383/500000000000 : ℝ) (992063119731/1000000000000 : ℝ) (248015779933/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 1 (198418923353/200000000000 : ℝ) (496047308383/500000000000 : ℝ) (992063119731/1000000000000 : ℝ) (248015779933/250000000000 : ℝ) (124009858531/125000000000 : ℝ) (992078868249/1000000000000 : ℝ) (992078868123/1000000000000 : ℝ) (1587326189/1600000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 2 (124009858531/125000000000 : ℝ) (992078868249/1000000000000 : ℝ) (992078868123/1000000000000 : ℝ) (1587326189/1600000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 3 (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 4 (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 5 (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 6 (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66845/524288 : ℝ)) 7 (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66845/524288 : ℝ))) (88560082147/500000000000 : ℝ) (177120164301/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88560082147/500000000000 : ℝ) (177120164301/1000000000000 : ℝ) (588560082147/1000000000000 : ℝ) (588560082151/1000000000000 : ℝ) (52607058149/125000000000 : ℝ) (420856465201/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 1 (588560082147/1000000000000 : ℝ) (588560082151/1000000000000 : ℝ) (52607058149/125000000000 : ℝ) (420856465201/1000000000000 : ℝ) (504708273669/1000000000000 : ℝ) (126177068419/250000000000 : ℝ) (97205859/195312500 : ℝ) (62211749761/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 2 (504708273669/1000000000000 : ℝ) (126177068419/250000000000 : ℝ) (97205859/195312500 : ℝ) (62211749761/125000000000 : ℝ) (250600567937/500000000000 : ℝ) (250600567941/500000000000 : ℝ) (100237773037/200000000000 : ℝ) (250594432597/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 3 (250600567937/500000000000 : ℝ) (250600567941/500000000000 : ℝ) (100237773037/200000000000 : ℝ) (250594432597/500000000000 : ℝ) (501195000529/1000000000000 : ℝ) (250597500269/500000000000 : ℝ) (501195000491/1000000000000 : ℝ) (501195000501/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 4 (501195000529/1000000000000 : ℝ) (250597500269/500000000000 : ℝ) (501195000491/1000000000000 : ℝ) (501195000501/1000000000000 : ℝ) (50119500051/100000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 5 (50119500051/100000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 6 (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66845/524288 : ℝ))) 7 (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66845/524288 : ℝ)) hmem 8 (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66845/524288 : ℝ))) hcmem 8 (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66845/524288 : ℝ)) (198415773637/200000000000 : ℝ) (992078868187/1000000000000 : ℝ) (501195000509/1000000000000 : ℝ) (12529875013/25000000000 : ℝ) (99195146053/125000000000 : ℝ) (198390292111/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0772_exp_lower
  have heNumeric : (2054901684451/1000000000000 : ℝ)/4 ≤ Real.exp (-21314123405833/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901684451/1000000000000 : ℝ)/4 ≤ Real.exp ((16711/131072 : ℝ)-(198390292111/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16711/131072 : ℝ) (66845/524288 : ℝ) (198390292111/250000000000 : ℝ) (2054901684451/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0773; no trusted numerical premise.
theorem cover8_leaf0773_exp_radius : (998009817003371533/1000000000000000000 : ℝ) ≤ Real.exp ((-33423/2097152 : ℝ)/8) ∧ Real.exp ((-33423/2097152 : ℝ)/8) ≤ (499004908501685767/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33423/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0773_exp_lower : (920113456034702197/1000000000000000000 : ℝ) ≤ Real.exp ((-85256493840083/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256493840083/128000000000000 : ℝ)/8) ≤ (460056728017351099/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256493840083/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0773_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901680971/1000000000000 : ℝ) ≤ 4*Real.exp (66845/524288 : ℝ)*Real.exp (-mu (radius 8 (33423/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901680971/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33423/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0773_exp_radius
  have hrNumeric : (492094499441/500000000000 : ℝ) ≤ Real.exp (-33423/2097152 : ℝ) ∧ Real.exp (-33423/2097152 : ℝ) ≤ (984188998883/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492094499441/500000000000 : ℝ) ≤ (radius 8 (33423/262144 : ℝ)) ∧ (radius 8 (33423/262144 : ℝ)) ≤ (984188998883/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33423/262144 : ℝ)) (492094499441/500000000000 : ℝ) (984188998883/1000000000000 : ℝ) (11070091759/62500000000 : ℝ) (177121468151/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33423/262144 : ℝ)) (492094499441/500000000000 : ℝ) (984188998883/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492094499441/500000000000 : ℝ) (984188998883/1000000000000 : ℝ) (992094499441/1000000000000 : ℝ) (496047249721/500000000000 : ℝ) (248015750367/250000000000 : ℝ) (992063001469/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 1 (992094499441/1000000000000 : ℝ) (496047249721/500000000000 : ℝ) (248015750367/250000000000 : ℝ) (992063001469/1000000000000 : ℝ) (496039375227/500000000000 : ℝ) (124009843807/125000000000 : ℝ) (992078750329/1000000000000 : ℝ) (992078750331/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 2 (496039375227/500000000000 : ℝ) (124009843807/125000000000 : ℝ) (992078750329/1000000000000 : ℝ) (992078750331/1000000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 3 (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 4 (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 5 (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 6 (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33423/262144 : ℝ)) 7 (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33423/262144 : ℝ))) (11070091759/62500000000 : ℝ) (177121468151/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11070091759/62500000000 : ℝ) (177121468151/1000000000000 : ℝ) (73570091759/125000000000 : ℝ) (147140183519/250000000000 : ℝ) (52607251779/125000000000 : ℝ) (210429007121/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 1 (73570091759/125000000000 : ℝ) (147140183519/250000000000 : ℝ) (52607251779/125000000000 : ℝ) (210429007121/500000000000 : ℝ) (63088671769/125000000000 : ℝ) (504709374159/1000000000000 : ℝ) (99539037929/200000000000 : ℝ) (248847594827/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 2 (63088671769/125000000000 : ℝ) (504709374159/1000000000000 : ℝ) (99539037929/200000000000 : ℝ) (248847594827/500000000000 : ℝ) (250601140949/500000000000 : ℝ) (501202281907/1000000000000 : ℝ) (125297502889/250000000000 : ℝ) (100238002313/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 3 (250601140949/500000000000 : ℝ) (501202281907/1000000000000 : ℝ) (125297502889/250000000000 : ℝ) (100238002313/200000000000 : ℝ) (501196146727/1000000000000 : ℝ) (31324759171/62500000000 : ℝ) (501196146689/1000000000000 : ℝ) (501196146699/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 4 (501196146727/1000000000000 : ℝ) (31324759171/62500000000 : ℝ) (501196146689/1000000000000 : ℝ) (501196146699/1000000000000 : ℝ) (125299036677/250000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 5 (125299036677/250000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 6 (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33423/262144 : ℝ))) 7 (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33423/262144 : ℝ)) hmem 8 (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33423/262144 : ℝ))) hcmem 8 (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33423/262144 : ℝ)) (992078750391/1000000000000 : ℝ) (496039375197/500000000000 : ℝ) (501196146707/1000000000000 : ℝ) (250598073359/500000000000 : ℝ) (158712615493/200000000000 : ℝ) (396781538743/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0773_exp_lower
  have heNumeric : (2054901680971/1000000000000 : ℝ)/4 ≤ Real.exp (-85256493840083/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901680971/1000000000000 : ℝ)/4 ≤ Real.exp ((66845/524288 : ℝ)-(396781538743/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66845/524288 : ℝ) (33423/262144 : ℝ) (396781538743/500000000000 : ℝ) (2054901680971/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0774; no trusted numerical premise.
theorem cover8_leaf0774_exp_radius : (15593902925943151/15625000000000000 : ℝ) ≤ Real.exp ((-66847/4194304 : ℝ)/8) ∧ Real.exp ((-66847/4194304 : ℝ)/8) ≤ (199601957452072333/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66847/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0774_exp_lower : (57507090990132889/62500000000000000 : ℝ) ≤ Real.exp ((-42628247027201/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628247027201/64000000000000 : ℝ)/8) ≤ (36804538233685049/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628247027201/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0774_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901677531/1000000000000 : ℝ) ≤ 4*Real.exp (33423/262144 : ℝ)*Real.exp (-mu (radius 8 (66847/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901677531/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66847/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0774_exp_radius
  have hrNumeric : (984188764233/1000000000000 : ℝ) ≤ Real.exp (-66847/4194304 : ℝ) ∧ Real.exp (-66847/4194304 : ℝ) ≤ (492094382117/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984188764233/1000000000000 : ℝ) ≤ (radius 8 (66847/524288 : ℝ)) ∧ (radius 8 (66847/524288 : ℝ)) ≤ (492094382117/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66847/524288 : ℝ)) (984188764233/1000000000000 : ℝ) (492094382117/500000000000 : ℝ) (11070173249/62500000000 : ℝ) (177122771991/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66847/524288 : ℝ)) (984188764233/1000000000000 : ℝ) (492094382117/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984188764233/1000000000000 : ℝ) (492094382117/500000000000 : ℝ) (248023595529/250000000000 : ℝ) (992094382117/1000000000000 : ℝ) (248015720801/250000000000 : ℝ) (496031441603/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 1 (248023595529/250000000000 : ℝ) (992094382117/1000000000000 : ℝ) (248015720801/250000000000 : ℝ) (496031441603/500000000000 : ℝ) (49603931633/50000000000 : ℝ) (496039316331/500000000000 : ℝ) (496039316267/500000000000 : ℝ) (992078632537/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 2 (49603931633/50000000000 : ℝ) (496039316331/500000000000 : ℝ) (496039316267/500000000000 : ℝ) (992078632537/1000000000000 : ℝ) (992078632597/1000000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 3 (992078632597/1000000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 4 (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 5 (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 6 (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66847/524288 : ℝ)) 7 (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66847/524288 : ℝ))) (11070173249/62500000000 : ℝ) (177122771991/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11070173249/62500000000 : ℝ) (177122771991/1000000000000 : ℝ) (73570173249/125000000000 : ℝ) (147140346499/250000000000 : ℝ) (84171912651/200000000000 : ℝ) (84171912653/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 1 (73570173249/125000000000 : ℝ) (147140346499/250000000000 : ℝ) (84171912651/200000000000 : ℝ) (84171912653/200000000000 : ℝ) (504710474623/1000000000000 : ℝ) (504710474631/1000000000000 : ℝ) (497696381197/1000000000000 : ℝ) (248848190603/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 2 (504710474623/1000000000000 : ℝ) (504710474631/1000000000000 : ℝ) (497696381197/1000000000000 : ℝ) (248848190603/500000000000 : ℝ) (50120342791/100000000000 : ℝ) (501203427919/1000000000000 : ℝ) (250595578957/500000000000 : ℝ) (125297789481/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 3 (50120342791/100000000000 : ℝ) (501203427919/1000000000000 : ℝ) (250595578957/500000000000 : ℝ) (125297789481/250000000000 : ℝ) (31324830807/62500000000 : ℝ) (250598646461/500000000000 : ℝ) (250598646437/500000000000 : ℝ) (125299323221/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 4 (31324830807/62500000000 : ℝ) (250598646461/500000000000 : ℝ) (250598646437/500000000000 : ℝ) (125299323221/250000000000 : ℝ) (501197292893/1000000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 5 (501197292893/1000000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 6 (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66847/524288 : ℝ))) 7 (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66847/524288 : ℝ)) hmem 8 (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66847/524288 : ℝ))) hcmem 8 (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66847/524288 : ℝ)) (248019658149/250000000000 : ℝ) (4960393163/5000000000 : ℝ) (125299323223/250000000000 : ℝ) (501197292903/1000000000000 : ℝ) (99195623311/125000000000 : ℝ) (793564986509/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0774_exp_lower
  have heNumeric : (2054901677531/1000000000000 : ℝ)/4 ≤ Real.exp (-42628247027201/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901677531/1000000000000 : ℝ)/4 ≤ Real.exp ((33423/262144 : ℝ)-(793564986509/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33423/262144 : ℝ) (66847/524288 : ℝ) (793564986509/1000000000000 : ℝ) (2054901677531/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0750_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0750_certificate
#check SmaleRate.Proofs.cover8_leaf0751_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0751_certificate
#check SmaleRate.Proofs.cover8_leaf0752_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0752_certificate
#check SmaleRate.Proofs.cover8_leaf0753_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0753_certificate
#check SmaleRate.Proofs.cover8_leaf0754_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0754_certificate
#check SmaleRate.Proofs.cover8_leaf0755_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0755_certificate
#check SmaleRate.Proofs.cover8_leaf0756_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0756_certificate
#check SmaleRate.Proofs.cover8_leaf0757_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0757_certificate
#check SmaleRate.Proofs.cover8_leaf0758_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0758_certificate
#check SmaleRate.Proofs.cover8_leaf0759_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0759_certificate
#check SmaleRate.Proofs.cover8_leaf0760_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0760_certificate
#check SmaleRate.Proofs.cover8_leaf0761_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0761_certificate
#check SmaleRate.Proofs.cover8_leaf0762_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0762_certificate
#check SmaleRate.Proofs.cover8_leaf0763_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0763_certificate
#check SmaleRate.Proofs.cover8_leaf0764_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0764_certificate
#check SmaleRate.Proofs.cover8_leaf0765_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0765_certificate
#check SmaleRate.Proofs.cover8_leaf0766_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0766_certificate
#check SmaleRate.Proofs.cover8_leaf0767_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0767_certificate
#check SmaleRate.Proofs.cover8_leaf0768_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0768_certificate
#check SmaleRate.Proofs.cover8_leaf0769_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0769_certificate
#check SmaleRate.Proofs.cover8_leaf0770_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0770_certificate
#check SmaleRate.Proofs.cover8_leaf0771_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0771_certificate
#check SmaleRate.Proofs.cover8_leaf0772_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0772_certificate
#check SmaleRate.Proofs.cover8_leaf0773_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0773_certificate
#check SmaleRate.Proofs.cover8_leaf0774_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0774_certificate
