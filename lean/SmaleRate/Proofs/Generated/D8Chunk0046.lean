/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1150; no trusted numerical premise.
theorem cover8_leaf1150_exp_radius : (498999301975737927/500000000000000000 : ℝ) ≤ Real.exp ((-67223/4194304 : ℝ)/8) ∧ Real.exp ((-67223/4194304 : ℝ)/8) ≤ (199599720790295171/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67223/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1150_exp_lower : (920113540891430087/1000000000000000000 : ℝ) ≤ Real.exp ((-42628199701253/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628199701253/64000000000000 : ℝ)/8) ≤ (115014192611428761/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628199701253/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1150_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980639413/200000000000 : ℝ) ≤ 4*Real.exp (33611/262144 : ℝ)*Real.exp (-mu (radius 8 (67223/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980639413/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67223/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1150_exp_radius
  have hrNumeric : (492050270103/500000000000 : ℝ) ≤ Real.exp (-67223/4194304 : ℝ) ∧ Real.exp (-67223/4194304 : ℝ) ≤ (984100540207/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492050270103/500000000000 : ℝ) ≤ (radius 8 (67223/524288 : ℝ)) ∧ (radius 8 (67223/524288 : ℝ)) ≤ (984100540207/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67223/524288 : ℝ)) (492050270103/500000000000 : ℝ) (984100540207/1000000000000 : ℝ) (11100768337/62500000000 : ℝ) (177612293399/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67223/524288 : ℝ)) (492050270103/500000000000 : ℝ) (984100540207/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492050270103/500000000000 : ℝ) (984100540207/1000000000000 : ℝ) (992050270103/1000000000000 : ℝ) (124006283763/125000000000 : ℝ) (992018417271/1000000000000 : ℝ) (992018417273/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 1 (992050270103/1000000000000 : ℝ) (124006283763/125000000000 : ℝ) (992018417271/1000000000000 : ℝ) (992018417273/1000000000000 : ℝ) (992034343687/1000000000000 : ℝ) (992034343689/1000000000000 : ℝ) (992034343559/1000000000000 : ℝ) (992034343561/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 2 (992034343687/1000000000000 : ℝ) (992034343689/1000000000000 : ℝ) (992034343559/1000000000000 : ℝ) (992034343561/1000000000000 : ℝ) (992034343623/1000000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 3 (992034343623/1000000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 4 (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 5 (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 6 (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67223/524288 : ℝ)) 7 (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67223/524288 : ℝ))) (11100768337/62500000000 : ℝ) (177612293399/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11100768337/62500000000 : ℝ) (177612293399/1000000000000 : ℝ) (73600768337/125000000000 : ℝ) (5888061467/10000000000 : ℝ) (16857629413/40000000000 : ℝ) (84288147067/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 1 (73600768337/125000000000 : ℝ) (5888061467/10000000000 : ℝ) (16857629413/40000000000 : ℝ) (84288147067/200000000000 : ℝ) (50512344101/100000000000 : ℝ) (252561720509/500000000000 : ℝ) (124535862161/250000000000 : ℝ) (498143448653/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 2 (50512344101/100000000000 : ℝ) (252561720509/500000000000 : ℝ) (124535862161/250000000000 : ℝ) (498143448653/1000000000000 : ℝ) (501633444827/1000000000000 : ℝ) (125408361209/250000000000 : ℝ) (125405326067/250000000000 : ℝ) (501621304277/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 3 (501633444827/1000000000000 : ℝ) (125408361209/250000000000 : ℝ) (125405326067/250000000000 : ℝ) (501621304277/1000000000000 : ℝ) (501627374547/1000000000000 : ℝ) (501627374557/1000000000000 : ℝ) (50162737451/100000000000 : ℝ) (12540684363/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 4 (501627374547/1000000000000 : ℝ) (501627374557/1000000000000 : ℝ) (50162737451/100000000000 : ℝ) (12540684363/25000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 5 (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 6 (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67223/524288 : ℝ))) 7 (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67223/524288 : ℝ)) hmem 8 (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67223/524288 : ℝ))) hcmem 8 (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67223/524288 : ℝ)) (496017171811/500000000000 : ℝ) (7936274749/8000000000 : ℝ) (7837927727/15625000000 : ℝ) (501627374539/1000000000000 : ℝ) (397140705053/500000000000 : ℝ) (794281410127/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1150_exp_lower
  have heNumeric : (410980639413/200000000000 : ℝ)/4 ≤ Real.exp (-42628199701253/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980639413/200000000000 : ℝ)/4 ≤ Real.exp ((33611/262144 : ℝ)-(794281410127/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33611/262144 : ℝ) (67223/524288 : ℝ) (794281410127/1000000000000 : ℝ) (410980639413/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1151; no trusted numerical premise.
theorem cover8_leaf1151_exp_radius : (6237491088805001/6250000000000000 : ℝ) ≤ Real.exp ((-8403/524288 : ℝ)/8) ∧ Real.exp ((-8403/524288 : ℝ)/8) ≤ (997998574208800161/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8403/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1151_exp_lower : (920113541534892263/1000000000000000000 : ℝ) ≤ Real.exp ((-85256398686393/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256398686393/128000000000000 : ℝ)/8) ≤ (115014192691861533/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256398686393/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1151_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903208561/1000000000000 : ℝ) ≤ 4*Real.exp (67223/524288 : ℝ)*Real.exp (-mu (radius 8 (8403/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903208561/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8403/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1151_exp_radius
  have hrNumeric : (492050152789/500000000000 : ℝ) ≤ Real.exp (-8403/524288 : ℝ) ∧ Real.exp (-8403/524288 : ℝ) ≤ (984100305579/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492050152789/500000000000 : ℝ) ≤ (radius 8 (8403/65536 : ℝ)) ∧ (radius 8 (8403/65536 : ℝ)) ≤ (984100305579/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8403/65536 : ℝ)) (492050152789/500000000000 : ℝ) (984100305579/1000000000000 : ℝ) (44403398349/250000000000 : ℝ) (177613593403/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8403/65536 : ℝ)) (492050152789/500000000000 : ℝ) (984100305579/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492050152789/500000000000 : ℝ) (984100305579/1000000000000 : ℝ) (992050152789/1000000000000 : ℝ) (99205015279/100000000000 : ℝ) (992018299013/1000000000000 : ℝ) (198403659803/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 1 (992050152789/1000000000000 : ℝ) (99205015279/100000000000 : ℝ) (992018299013/1000000000000 : ℝ) (198403659803/200000000000 : ℝ) (992034225901/1000000000000 : ℝ) (992034225903/1000000000000 : ℝ) (992034225773/1000000000000 : ℝ) (39681369031/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 2 (992034225901/1000000000000 : ℝ) (992034225903/1000000000000 : ℝ) (992034225773/1000000000000 : ℝ) (39681369031/40000000000 : ℝ) (992034225837/1000000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 3 (992034225837/1000000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 4 (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 5 (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 6 (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8403/65536 : ℝ)) 7 (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8403/65536 : ℝ))) (44403398349/250000000000 : ℝ) (177613593403/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44403398349/250000000000 : ℝ) (177613593403/1000000000000 : ℝ) (294403398349/500000000000 : ℝ) (294403398351/500000000000 : ℝ) (52680284707/125000000000 : ℝ) (84288455533/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 1 (294403398349/500000000000 : ℝ) (294403398351/500000000000 : ℝ) (52680284707/125000000000 : ℝ) (84288455533/200000000000 : ℝ) (505124537177/1000000000000 : ℝ) (15785141787/31250000000 : ℝ) (6226807939/12500000000 : ℝ) (62268079391/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 2 (505124537177/1000000000000 : ℝ) (15785141787/31250000000 : ℝ) (6226807939/12500000000 : ℝ) (62268079391/125000000000 : ℝ) (125408646537/250000000000 : ℝ) (125408646539/250000000000 : ℝ) (501622445931/1000000000000 : ℝ) (501622445939/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 3 (125408646537/250000000000 : ℝ) (125408646539/250000000000 : ℝ) (501622445931/1000000000000 : ℝ) (501622445939/1000000000000 : ℝ) (501628516039/1000000000000 : ℝ) (31351782253/62500000000 : ℝ) (250814258001/500000000000 : ℝ) (501628516011/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 4 (501628516039/1000000000000 : ℝ) (31351782253/62500000000 : ℝ) (250814258001/500000000000 : ℝ) (501628516011/1000000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 5 (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 6 (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8403/65536 : ℝ))) 7 (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8403/65536 : ℝ)) hmem 8 (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8403/65536 : ℝ))) hcmem 8 (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8403/65536 : ℝ)) (248008556459/250000000000 : ℝ) (992034225839/1000000000000 : ℝ) (25081425801/50000000000 : ℝ) (50162851603/100000000000 : ℝ) (794283311861/1000000000000 : ℝ) (794283311881/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1151_exp_lower
  have heNumeric : (2054903208561/1000000000000 : ℝ)/4 ≤ Real.exp (-85256398686393/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903208561/1000000000000 : ℝ)/4 ≤ Real.exp ((67223/524288 : ℝ)-(794283311881/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67223/524288 : ℝ) (8403/65536 : ℝ) (794283311881/1000000000000 : ℝ) (2054903208561/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1152; no trusted numerical premise.
theorem cover8_leaf1152_exp_radius : (124749818058265669/125000000000000000 : ℝ) ≤ Real.exp ((-67225/4194304 : ℝ)/8) ∧ Real.exp ((-67225/4194304 : ℝ)/8) ≤ (997998544466125353/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67225/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1152_exp_lower : (920113542180309681/1000000000000000000 : ℝ) ≤ Real.exp ((-10657049746013/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657049746013/16000000000000 : ℝ)/8) ≤ (460056771090154841/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657049746013/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1152_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903220093/1000000000000 : ℝ) ≤ 4*Real.exp (8403/65536 : ℝ)*Real.exp (-mu (radius 8 (67225/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903220093/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67225/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1152_exp_radius
  have hrNumeric : (19682001419/20000000000 : ℝ) ≤ Real.exp (-67225/4194304 : ℝ) ∧ Real.exp (-67225/4194304 : ℝ) ≤ (984100070951/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19682001419/20000000000 : ℝ) ≤ (radius 8 (67225/524288 : ℝ)) ∧ (radius 8 (67225/524288 : ℝ)) ≤ (984100070951/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67225/524288 : ℝ)) (19682001419/20000000000 : ℝ) (984100070951/1000000000000 : ℝ) (17761489339/100000000000 : ℝ) (177614893397/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67225/524288 : ℝ)) (19682001419/20000000000 : ℝ) (984100070951/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19682001419/20000000000 : ℝ) (984100070951/1000000000000 : ℝ) (39682001419/40000000000 : ℝ) (248012508869/250000000000 : ℝ) (198403636151/200000000000 : ℝ) (992018180757/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 1 (39682001419/40000000000 : ℝ) (248012508869/250000000000 : ℝ) (198403636151/200000000000 : ℝ) (992018180757/1000000000000 : ℝ) (198406821623/200000000000 : ℝ) (992034108117/1000000000000 : ℝ) (992034107987/1000000000000 : ℝ) (992034107989/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 2 (198406821623/200000000000 : ℝ) (992034108117/1000000000000 : ℝ) (992034107987/1000000000000 : ℝ) (992034107989/1000000000000 : ℝ) (992034108051/1000000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 3 (992034108051/1000000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 4 (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 5 (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 6 (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67225/524288 : ℝ)) 7 (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67225/524288 : ℝ))) (17761489339/100000000000 : ℝ) (177614893397/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17761489339/100000000000 : ℝ) (177614893397/1000000000000 : ℝ) (117761489339/200000000000 : ℝ) (588807446699/1000000000000 : ℝ) (6585059687/15625000000 : ℝ) (210721909989/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 1 (117761489339/200000000000 : ℝ) (588807446699/1000000000000 : ℝ) (6585059687/15625000000 : ℝ) (210721909989/500000000000 : ℝ) (505125633331/1000000000000 : ℝ) (505125633339/1000000000000 : ℝ) (498145821583/1000000000000 : ℝ) (498145821591/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 2 (505125633331/1000000000000 : ℝ) (505125633339/1000000000000 : ℝ) (498145821583/1000000000000 : ℝ) (498145821591/1000000000000 : ℝ) (501635727457/1000000000000 : ℝ) (100327145493/200000000000 : ℝ) (501623587581/1000000000000 : ℝ) (50162358759/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 3 (501635727457/1000000000000 : ℝ) (100327145493/200000000000 : ℝ) (501623587581/1000000000000 : ℝ) (50162358759/100000000000 : ℝ) (501629657519/1000000000000 : ℝ) (62703707191/125000000000 : ℝ) (250814828741/500000000000 : ℝ) (501629657491/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 4 (501629657519/1000000000000 : ℝ) (62703707191/125000000000 : ℝ) (250814828741/500000000000 : ℝ) (501629657491/1000000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 5 (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 6 (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67225/524288 : ℝ))) 7 (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67225/524288 : ℝ)) hmem 8 (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67225/524288 : ℝ))) hcmem 8 (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67225/524288 : ℝ)) (19840682161/20000000000 : ℝ) (992034108053/1000000000000 : ℝ) (200651863/400000000 : ℝ) (50162965751/100000000000 : ℝ) (794285213599/1000000000000 : ℝ) (397142606809/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1152_exp_lower
  have heNumeric : (2054903220093/1000000000000 : ℝ)/4 ≤ Real.exp (-10657049746013/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903220093/1000000000000 : ℝ)/4 ≤ Real.exp ((8403/65536 : ℝ)-(397142606809/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8403/65536 : ℝ) (67225/524288 : ℝ) (397142606809/500000000000 : ℝ) (2054903220093/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1153; no trusted numerical premise.
theorem cover8_leaf1153_exp_radius : (997998514723451431/1000000000000000000 : ℝ) ≤ Real.exp ((-33613/2097152 : ℝ)/8) ∧ Real.exp ((-33613/2097152 : ℝ)/8) ≤ (124749814340431429/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33613/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1153_exp_lower : (920113542828832483/1000000000000000000 : ℝ) ≤ Real.exp ((-85256397246359/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256397246359/128000000000000 : ℝ)/8) ≤ (230028385707208121/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256397246359/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1153_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (6421572599/3125000000 : ℝ) ≤ 4*Real.exp (67225/524288 : ℝ)*Real.exp (-mu (radius 8 (33613/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (6421572599/3125000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33613/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1153_exp_radius
  have hrNumeric : (984099836323/1000000000000 : ℝ) ≤ Real.exp (-33613/2097152 : ℝ) ∧ Real.exp (-33613/2097152 : ℝ) ≤ (246024959081/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984099836323/1000000000000 : ℝ) ≤ (radius 8 (33613/262144 : ℝ)) ∧ (radius 8 (33613/262144 : ℝ)) ≤ (246024959081/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33613/262144 : ℝ)) (984099836323/1000000000000 : ℝ) (246024959081/250000000000 : ℝ) (177616193369/1000000000000 : ℝ) (5550506043/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33613/262144 : ℝ)) (984099836323/1000000000000 : ℝ) (246024959081/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984099836323/1000000000000 : ℝ) (246024959081/250000000000 : ℝ) (992049918161/1000000000000 : ℝ) (496024959081/500000000000 : ℝ) (496009031249/500000000000 : ℝ) (992018062499/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 1 (992049918161/1000000000000 : ℝ) (496024959081/500000000000 : ℝ) (496009031249/500000000000 : ℝ) (992018062499/1000000000000 : ℝ) (992033990329/1000000000000 : ℝ) (992033990331/1000000000000 : ℝ) (992033990201/1000000000000 : ℝ) (992033990203/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 2 (992033990329/1000000000000 : ℝ) (992033990331/1000000000000 : ℝ) (992033990201/1000000000000 : ℝ) (992033990203/1000000000000 : ℝ) (198406798053/200000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 3 (198406798053/200000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 4 (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 5 (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 6 (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33613/262144 : ℝ)) 7 (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33613/262144 : ℝ))) (177616193369/1000000000000 : ℝ) (5550506043/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177616193369/1000000000000 : ℝ) (5550506043/31250000000 : ℝ) (147202024171/250000000000 : ℝ) (36800506043/62500000000 : ℝ) (210722681129/500000000000 : ℝ) (421445362267/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 1 (147202024171/250000000000 : ℝ) (36800506043/62500000000 : ℝ) (210722681129/500000000000 : ℝ) (421445362267/1000000000000 : ℝ) (505126729471/1000000000000 : ℝ) (252563364739/500000000000 : ℝ) (124536752007/250000000000 : ℝ) (124536752009/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 2 (505126729471/1000000000000 : ℝ) (252563364739/500000000000 : ℝ) (124536752007/250000000000 : ℝ) (124536752009/250000000000 : ℝ) (501636868749/1000000000000 : ℝ) (501636868757/1000000000000 : ℝ) (100324945843/200000000000 : ℝ) (62703091153/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 3 (501636868749/1000000000000 : ℝ) (501636868757/1000000000000 : ℝ) (100324945843/200000000000 : ℝ) (62703091153/125000000000 : ℝ) (250815399491/500000000000 : ℝ) (501630798991/1000000000000 : ℝ) (100326159789/200000000000 : ℝ) (250815399477/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 4 (250815399491/500000000000 : ℝ) (501630798991/1000000000000 : ℝ) (100326159789/200000000000 : ℝ) (250815399477/500000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 5 (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 6 (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33613/262144 : ℝ))) 7 (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33613/262144 : ℝ)) hmem 8 (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33613/262144 : ℝ))) hcmem 8 (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33613/262144 : ℝ)) (124004248783/125000000000 : ℝ) (992033990267/1000000000000 : ℝ) (501630798963/1000000000000 : ℝ) (501630798973/1000000000000 : ℝ) (794287115309/1000000000000 : ℝ) (12410736177/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1153_exp_lower
  have heNumeric : (6421572599/3125000000 : ℝ)/4 ≤ Real.exp (-85256397246359/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (6421572599/3125000000 : ℝ)/4 ≤ Real.exp ((67225/524288 : ℝ)-(12410736177/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67225/524288 : ℝ) (33613/262144 : ℝ) (12410736177/15625000000 : ℝ) (6421572599/3125000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1154; no trusted numerical premise.
theorem cover8_leaf1154_exp_radius : (249499621245194599/250000000000000000 : ℝ) ≤ Real.exp ((-67227/4194304 : ℝ)/8) ∧ Real.exp ((-67227/4194304 : ℝ)/8) ≤ (997998484980778397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67227/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1154_exp_lower : (920113543478620441/1000000000000000000 : ℝ) ≤ Real.exp ((-42628198261603/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628198261603/64000000000000 : ℝ)/8) ≤ (460056771739310221/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628198261603/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1154_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903243289/1000000000000 : ℝ) ≤ 4*Real.exp (33613/262144 : ℝ)*Real.exp (-mu (radius 8 (67227/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903243289/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67227/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1154_exp_radius
  have hrNumeric : (196819920339/200000000000 : ℝ) ≤ Real.exp (-67227/4194304 : ℝ) ∧ Real.exp (-67227/4194304 : ℝ) ≤ (30753112553/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196819920339/200000000000 : ℝ) ≤ (radius 8 (67227/524288 : ℝ)) ∧ (radius 8 (67227/524288 : ℝ)) ≤ (30753112553/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67227/524288 : ℝ)) (196819920339/200000000000 : ℝ) (30753112553/31250000000 : ℝ) (177617493343/1000000000000 : ℝ) (3552349867/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67227/524288 : ℝ)) (196819920339/200000000000 : ℝ) (30753112553/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196819920339/200000000000 : ℝ) (30753112553/31250000000 : ℝ) (992049800847/1000000000000 : ℝ) (62003112553/62500000000 : ℝ) (12400224303/12500000000 : ℝ) (992017944241/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 1 (992049800847/1000000000000 : ℝ) (62003112553/62500000000 : ℝ) (12400224303/12500000000 : ℝ) (992017944241/1000000000000 : ℝ) (992033872543/1000000000000 : ℝ) (198406774509/200000000000 : ℝ) (198406774483/200000000000 : ℝ) (992033872417/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 2 (992033872543/1000000000000 : ℝ) (198406774509/200000000000 : ℝ) (198406774483/200000000000 : ℝ) (992033872417/1000000000000 : ℝ) (992033872479/1000000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 3 (992033872479/1000000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 4 (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 5 (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 6 (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67227/524288 : ℝ)) 7 (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67227/524288 : ℝ))) (177617493343/1000000000000 : ℝ) (3552349867/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177617493343/1000000000000 : ℝ) (3552349867/20000000000 : ℝ) (588808746671/1000000000000 : ℝ) (23552349867/40000000000 : ℝ) (52680863067/125000000000 : ℝ) (84289380909/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 1 (588808746671/1000000000000 : ℝ) (23552349867/40000000000 : ℝ) (52680863067/125000000000 : ℝ) (84289380909/200000000000 : ℝ) (505127825603/1000000000000 : ℝ) (50512782561/100000000000 : ℝ) (15567131077/31250000000 : ℝ) (62268524309/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 2 (505127825603/1000000000000 : ℝ) (50512782561/100000000000 : ℝ) (15567131077/31250000000 : ℝ) (62268524309/125000000000 : ℝ) (501638010033/1000000000000 : ℝ) (501638010041/1000000000000 : ℝ) (501625870841/1000000000000 : ℝ) (10032517417/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 3 (501638010033/1000000000000 : ℝ) (501638010041/1000000000000 : ℝ) (501625870841/1000000000000 : ℝ) (10032517417/20000000000 : ℝ) (501631940437/1000000000000 : ℝ) (250815970223/500000000000 : ℝ) (1254079851/2500000000 : ℝ) (501631940409/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 4 (501631940437/1000000000000 : ℝ) (250815970223/500000000000 : ℝ) (1254079851/2500000000 : ℝ) (501631940409/1000000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 5 (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 6 (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67227/524288 : ℝ))) 7 (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67227/524288 : ℝ)) hmem 8 (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67227/524288 : ℝ))) hcmem 8 (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67227/524288 : ℝ)) (496016936239/500000000000 : ℝ) (992033872481/1000000000000 : ℝ) (250815970209/500000000000 : ℝ) (125407985107/250000000000 : ℝ) (49643063563/62500000000 : ℝ) (794289017027/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1154_exp_lower
  have heNumeric : (2054903243289/1000000000000 : ℝ)/4 ≤ Real.exp (-42628198261603/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903243289/1000000000000 : ℝ)/4 ≤ Real.exp ((33613/262144 : ℝ)-(794289017027/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33613/262144 : ℝ) (67227/524288 : ℝ) (794289017027/1000000000000 : ℝ) (2054903243289/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1155; no trusted numerical premise.
theorem cover8_leaf1155_exp_radius : (997998455238106247/1000000000000000000 : ℝ) ≤ Real.exp ((-16807/1048576 : ℝ)/8) ∧ Real.exp ((-16807/1048576 : ℝ)/8) ≤ (124749806904763281/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16807/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1155_exp_lower : (920113544130593669/1000000000000000000 : ℝ) ≤ Real.exp ((-85256395797621/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256395797621/128000000000000 : ℝ)/8) ≤ (92011354413059367/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256395797621/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1155_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451627469/500000000000 : ℝ) ≤ 4*Real.exp (67227/524288 : ℝ)*Real.exp (-mu (radius 8 (16807/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451627469/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16807/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1155_exp_radius
  have hrNumeric : (984099367067/1000000000000 : ℝ) ≤ Real.exp (-16807/1048576 : ℝ) ∧ Real.exp (-16807/1048576 : ℝ) ≤ (246024841767/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984099367067/1000000000000 : ℝ) ≤ (radius 8 (16807/131072 : ℝ)) ∧ (radius 8 (16807/131072 : ℝ)) ≤ (246024841767/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16807/131072 : ℝ)) (984099367067/1000000000000 : ℝ) (246024841767/250000000000 : ℝ) (44404698327/250000000000 : ℝ) (35523758663/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16807/131072 : ℝ)) (984099367067/1000000000000 : ℝ) (246024841767/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984099367067/1000000000000 : ℝ) (246024841767/250000000000 : ℝ) (992049683533/1000000000000 : ℝ) (496024841767/500000000000 : ℝ) (496008912991/500000000000 : ℝ) (992017825983/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 1 (992049683533/1000000000000 : ℝ) (496024841767/500000000000 : ℝ) (496008912991/500000000000 : ℝ) (992017825983/1000000000000 : ℝ) (992033754757/1000000000000 : ℝ) (992033754759/1000000000000 : ℝ) (992033754629/1000000000000 : ℝ) (992033754631/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 2 (992033754757/1000000000000 : ℝ) (992033754759/1000000000000 : ℝ) (992033754629/1000000000000 : ℝ) (992033754631/1000000000000 : ℝ) (992033754693/1000000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 3 (992033754693/1000000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 4 (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 5 (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 6 (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16807/131072 : ℝ)) 7 (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16807/131072 : ℝ))) (44404698327/250000000000 : ℝ) (35523758663/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44404698327/250000000000 : ℝ) (35523758663/200000000000 : ℝ) (294404698327/500000000000 : ℝ) (294404698329/500000000000 : ℝ) (421448446797/1000000000000 : ℝ) (210724223403/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 1 (294404698327/500000000000 : ℝ) (294404698329/500000000000 : ℝ) (421448446797/1000000000000 : ℝ) (210724223403/500000000000 : ℝ) (20205156869/40000000000 : ℝ) (126282230433/250000000000 : ℝ) (62268672611/125000000000 : ℝ) (15567168153/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 2 (20205156869/40000000000 : ℝ) (126282230433/250000000000 : ℝ) (62268672611/125000000000 : ℝ) (15567168153/31250000000 : ℝ) (250819575653/500000000000 : ℝ) (250819575657/500000000000 : ℝ) (62703376557/125000000000 : ℝ) (31351688279/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 3 (250819575653/500000000000 : ℝ) (250819575657/500000000000 : ℝ) (62703376557/125000000000 : ℝ) (31351688279/62500000000 : ℝ) (501633081881/1000000000000 : ℝ) (501633081889/1000000000000 : ℝ) (125408270461/250000000000 : ℝ) (501633081853/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 4 (501633081881/1000000000000 : ℝ) (501633081889/1000000000000 : ℝ) (125408270461/250000000000 : ℝ) (501633081853/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 5 (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 6 (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16807/131072 : ℝ))) 7 (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16807/131072 : ℝ)) hmem 8 (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16807/131072 : ℝ))) hcmem 8 (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16807/131072 : ℝ)) (248008438673/250000000000 : ℝ) (198406750939/200000000000 : ℝ) (250816540931/500000000000 : ℝ) (501633081871/1000000000000 : ℝ) (794290918689/1000000000000 : ℝ) (794290918707/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1155_exp_lower
  have heNumeric : (1027451627469/500000000000 : ℝ)/4 ≤ Real.exp (-85256395797621/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451627469/500000000000 : ℝ)/4 ≤ Real.exp ((67227/524288 : ℝ)-(794290918707/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67227/524288 : ℝ) (16807/131072 : ℝ) (794290918707/1000000000000 : ℝ) (1027451627469/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1156; no trusted numerical premise.
theorem cover8_leaf1156_exp_radius : (199599685099086997/200000000000000000 : ℝ) ≤ Real.exp ((-67229/4194304 : ℝ)/8) ∧ Real.exp ((-67229/4194304 : ℝ)/8) ≤ (498999212747717493/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67229/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1156_exp_lower : (920113544785557267/1000000000000000000 : ℝ) ≤ Real.exp ((-21314098767177/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314098767177/32000000000000 : ℝ)/8) ≤ (230028386196389317/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314098767177/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1156_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903266639/1000000000000 : ℝ) ≤ 4*Real.exp (16807/131072 : ℝ)*Real.exp (-mu (radius 8 (67229/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903266639/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67229/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1156_exp_radius
  have hrNumeric : (24602478311/25000000000 : ℝ) ≤ Real.exp (-67229/4194304 : ℝ) ∧ Real.exp (-67229/4194304 : ℝ) ≤ (984099132441/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24602478311/25000000000 : ℝ) ≤ (radius 8 (67229/524288 : ℝ)) ∧ (radius 8 (67229/524288 : ℝ)) ≤ (984099132441/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67229/524288 : ℝ)) (24602478311/25000000000 : ℝ) (984099132441/1000000000000 : ℝ) (177620093257/1000000000000 : ℝ) (11101255829/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67229/524288 : ℝ)) (24602478311/25000000000 : ℝ) (984099132441/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24602478311/25000000000 : ℝ) (984099132441/1000000000000 : ℝ) (49602478311/50000000000 : ℝ) (992049566221/1000000000000 : ℝ) (39680708309/40000000000 : ℝ) (496008853863/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 1 (49602478311/50000000000 : ℝ) (992049566221/1000000000000 : ℝ) (39680708309/40000000000 : ℝ) (496008853863/500000000000 : ℝ) (248008409243/250000000000 : ℝ) (496016818487/500000000000 : ℝ) (248008409211/250000000000 : ℝ) (496016818423/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 2 (248008409243/250000000000 : ℝ) (496016818487/500000000000 : ℝ) (248008409211/250000000000 : ℝ) (496016818423/500000000000 : ℝ) (248008409227/250000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 3 (248008409227/250000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 4 (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 5 (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 6 (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67229/524288 : ℝ)) 7 (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67229/524288 : ℝ))) (177620093257/1000000000000 : ℝ) (11101255829/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177620093257/1000000000000 : ℝ) (11101255829/62500000000 : ℝ) (147202511657/250000000000 : ℝ) (73601255829/125000000000 : ℝ) (210724994517/500000000000 : ℝ) (421449989043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 1 (147202511657/250000000000 : ℝ) (73601255829/125000000000 : ℝ) (210724994517/500000000000 : ℝ) (421449989043/1000000000000 : ℝ) (505130017831/1000000000000 : ℝ) (252565008919/500000000000 : ℝ) (498150567293/1000000000000 : ℝ) (498150567301/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 2 (505130017831/1000000000000 : ℝ) (252565008919/500000000000 : ℝ) (498150567293/1000000000000 : ℝ) (498150567301/1000000000000 : ℝ) (250820146281/500000000000 : ℝ) (50164029257/100000000000 : ℝ) (501628154053/1000000000000 : ℝ) (250814077031/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 3 (250820146281/500000000000 : ℝ) (50164029257/100000000000 : ℝ) (501628154053/1000000000000 : ℝ) (250814077031/500000000000 : ℝ) (501634223307/1000000000000 : ℝ) (125408555829/250000000000 : ℝ) (50163422327/100000000000 : ℝ) (6270427791/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 4 (501634223307/1000000000000 : ℝ) (125408555829/250000000000 : ℝ) (50163422327/100000000000 : ℝ) (6270427791/12500000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 5 (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 6 (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67229/524288 : ℝ))) 7 (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67229/524288 : ℝ)) hmem 8 (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67229/524288 : ℝ))) hcmem 8 (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67229/524288 : ℝ)) (992033636907/1000000000000 : ℝ) (99203363691/100000000000 : ℝ) (62704277911/125000000000 : ℝ) (250817111649/500000000000 : ℝ) (397146410171/500000000000 : ℝ) (794292820361/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1156_exp_lower
  have heNumeric : (2054903266639/1000000000000 : ℝ)/4 ≤ Real.exp (-21314098767177/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903266639/1000000000000 : ℝ)/4 ≤ Real.exp ((16807/131072 : ℝ)-(794292820361/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16807/131072 : ℝ) (67229/524288 : ℝ) (794292820361/1000000000000 : ℝ) (2054903266639/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1157; no trusted numerical premise.
theorem cover8_leaf1157_exp_radius : (997998395752764609/1000000000000000000 : ℝ) ≤ Real.exp ((-33615/2097152 : ℝ)/8) ∧ Real.exp ((-33615/2097152 : ℝ)/8) ≤ (99799839575276461/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33615/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1157_exp_lower : (920113545441786021/1000000000000000000 : ℝ) ≤ Real.exp ((-85256394338387/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256394338387/128000000000000 : ℝ)/8) ≤ (460056772720893011/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256394338387/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1157_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725819591/250000000000 : ℝ) ≤ 4*Real.exp (67229/524288 : ℝ)*Real.exp (-mu (radius 8 (33615/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725819591/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33615/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1157_exp_radius
  have hrNumeric : (246024724453/250000000000 : ℝ) ≤ Real.exp (-33615/2097152 : ℝ) ∧ Real.exp (-33615/2097152 : ℝ) ≤ (984098897813/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246024724453/250000000000 : ℝ) ≤ (radius 8 (33615/262144 : ℝ)) ∧ (radius 8 (33615/262144 : ℝ)) ≤ (984098897813/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33615/262144 : ℝ)) (246024724453/250000000000 : ℝ) (984098897813/1000000000000 : ℝ) (88810696601/500000000000 : ℝ) (177621393209/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33615/262144 : ℝ)) (246024724453/250000000000 : ℝ) (984098897813/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246024724453/250000000000 : ℝ) (984098897813/1000000000000 : ℝ) (496024724453/500000000000 : ℝ) (992049448907/1000000000000 : ℝ) (992017589467/1000000000000 : ℝ) (248004397367/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 1 (496024724453/500000000000 : ℝ) (992049448907/1000000000000 : ℝ) (992017589467/1000000000000 : ℝ) (248004397367/250000000000 : ℝ) (496016759593/500000000000 : ℝ) (248008379797/250000000000 : ℝ) (496016759529/500000000000 : ℝ) (49601675953/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 2 (496016759593/500000000000 : ℝ) (248008379797/250000000000 : ℝ) (496016759529/500000000000 : ℝ) (49601675953/50000000000 : ℝ) (496016759561/500000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 3 (496016759561/500000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 4 (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 5 (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 6 (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33615/262144 : ℝ)) 7 (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33615/262144 : ℝ))) (88810696601/500000000000 : ℝ) (177621393209/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88810696601/500000000000 : ℝ) (177621393209/1000000000000 : ℝ) (588810696601/1000000000000 : ℝ) (117762139321/200000000000 : ℝ) (21072576563/50000000000 : ℝ) (42145153127/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 1 (588810696601/1000000000000 : ℝ) (117762139321/200000000000 : ℝ) (21072576563/50000000000 : ℝ) (42145153127/100000000000 : ℝ) (50513111393/100000000000 : ℝ) (252565556969/500000000000 : ℝ) (49815175369/100000000000 : ℝ) (249075876849/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 2 (50513111393/100000000000 : ℝ) (252565556969/500000000000 : ℝ) (49815175369/100000000000 : ℝ) (249075876849/500000000000 : ℝ) (50164143381/100000000000 : ℝ) (250820716909/500000000000 : ℝ) (501629295643/1000000000000 : ℝ) (125407323913/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 3 (50164143381/100000000000 : ℝ) (250820716909/500000000000 : ℝ) (501629295643/1000000000000 : ℝ) (125407323913/250000000000 : ℝ) (250817682363/500000000000 : ℝ) (100327072947/200000000000 : ℝ) (501635364689/1000000000000 : ℝ) (501635364699/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 4 (250817682363/500000000000 : ℝ) (100327072947/200000000000 : ℝ) (501635364689/1000000000000 : ℝ) (501635364699/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 5 (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 6 (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33615/262144 : ℝ))) 7 (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33615/262144 : ℝ)) hmem 8 (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33615/262144 : ℝ))) hcmem 8 (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33615/262144 : ℝ)) (992033519121/1000000000000 : ℝ) (248008379781/250000000000 : ℝ) (501635364707/1000000000000 : ℝ) (501635364717/1000000000000 : ℝ) (12410855031/15625000000 : ℝ) (198573680501/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1157_exp_lower
  have heNumeric : (513725819591/250000000000 : ℝ)/4 ≤ Real.exp (-85256394338387/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725819591/250000000000 : ℝ)/4 ≤ Real.exp ((67229/524288 : ℝ)-(198573680501/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67229/524288 : ℝ) (33615/262144 : ℝ) (198573680501/250000000000 : ℝ) (513725819591/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1158; no trusted numerical premise.
theorem cover8_leaf1158_exp_radius : (12474979575126189/12500000000000000 : ℝ) ≤ Real.exp ((-67231/4194304 : ℝ)/8) ∧ Real.exp ((-67231/4194304 : ℝ)/8) ≤ (997998366010095121/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67231/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1158_exp_lower : (920113546101350187/1000000000000000000 : ℝ) ≤ Real.exp ((-42628196802177/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628196802177/64000000000000 : ℝ)/8) ≤ (230028386525337547/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628196802177/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1158_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725822537/250000000000 : ℝ) ≤ 4*Real.exp (33615/262144 : ℝ)*Real.exp (-mu (radius 8 (67231/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725822537/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67231/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1158_exp_radius
  have hrNumeric : (196819732637/200000000000 : ℝ) ≤ Real.exp (-67231/4194304 : ℝ) ∧ Real.exp (-67231/4194304 : ℝ) ≤ (492049331593/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196819732637/200000000000 : ℝ) ≤ (radius 8 (67231/524288 : ℝ)) ∧ (radius 8 (67231/524288 : ℝ)) ≤ (492049331593/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67231/524288 : ℝ)) (196819732637/200000000000 : ℝ) (492049331593/500000000000 : ℝ) (44405673283/250000000000 : ℝ) (88811346569/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67231/524288 : ℝ)) (196819732637/200000000000 : ℝ) (492049331593/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196819732637/200000000000 : ℝ) (492049331593/500000000000 : ℝ) (124006166449/125000000000 : ℝ) (992049331593/1000000000000 : ℝ) (992017471209/1000000000000 : ℝ) (992017471211/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 1 (124006166449/125000000000 : ℝ) (992049331593/1000000000000 : ℝ) (992017471209/1000000000000 : ℝ) (992017471211/1000000000000 : ℝ) (4960167007/5000000000 : ℝ) (496016700701/500000000000 : ℝ) (124004175159/125000000000 : ℝ) (39681336051/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 2 (4960167007/5000000000 : ℝ) (496016700701/500000000000 : ℝ) (124004175159/125000000000 : ℝ) (39681336051/40000000000 : ℝ) (124004175167/125000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 3 (124004175167/125000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 4 (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 5 (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 6 (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67231/524288 : ℝ)) 7 (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67231/524288 : ℝ))) (44405673283/250000000000 : ℝ) (88811346569/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44405673283/250000000000 : ℝ) (88811346569/500000000000 : ℝ) (294405673283/500000000000 : ℝ) (588811346569/1000000000000 : ℝ) (421453073463/1000000000000 : ℝ) (421453073471/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 1 (294405673283/500000000000 : ℝ) (588811346569/1000000000000 : ℝ) (421453073463/1000000000000 : ℝ) (421453073471/1000000000000 : ℝ) (252566105007/500000000000 : ℝ) (25256610501/50000000000 : ℝ) (498152940069/1000000000000 : ℝ) (124538235019/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 2 (252566105007/500000000000 : ℝ) (25256610501/50000000000 : ℝ) (498152940069/1000000000000 : ℝ) (124538235019/250000000000 : ℝ) (501642575041/1000000000000 : ℝ) (62705321881/125000000000 : ℝ) (15675951163/31250000000 : ℝ) (62703804653/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 3 (501642575041/1000000000000 : ℝ) (62705321881/125000000000 : ℝ) (15675951163/31250000000 : ℝ) (62703804653/125000000000 : ℝ) (31352281633/62500000000 : ℝ) (62704563267/125000000000 : ℝ) (501636506091/1000000000000 : ℝ) (5016365061/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 4 (31352281633/62500000000 : ℝ) (62704563267/125000000000 : ℝ) (501636506091/1000000000000 : ℝ) (5016365061/10000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 5 (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 6 (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67231/524288 : ℝ))) 7 (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67231/524288 : ℝ)) hmem 8 (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67231/524288 : ℝ))) hcmem 8 (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67231/524288 : ℝ)) (198406680267/200000000000 : ℝ) (992033401339/1000000000000 : ℝ) (501636506109/1000000000000 : ℝ) (250818253059/500000000000 : ℝ) (1985741559/2500000000 : ℝ) (397148311809/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1158_exp_lower
  have heNumeric : (513725822537/250000000000 : ℝ)/4 ≤ Real.exp (-42628196802177/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725822537/250000000000 : ℝ)/4 ≤ Real.exp ((33615/262144 : ℝ)-(397148311809/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33615/262144 : ℝ) (67231/524288 : ℝ) (397148311809/500000000000 : ℝ) (513725822537/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1159; no trusted numerical premise.
theorem cover8_leaf1159_exp_radius : (997998336267426517/1000000000000000000 : ℝ) ≤ Real.exp ((-2101/131072 : ℝ)/8) ∧ Real.exp ((-2101/131072 : ℝ)/8) ≤ (498999168133713259/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2101/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1159_exp_lower : (920113546761719453/1000000000000000000 : ℝ) ≤ Real.exp ((-3410255714777/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410255714777/5120000000000 : ℝ)/8) ≤ (460056773380859727/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410255714777/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1159_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903301947/1000000000000 : ℝ) ≤ 4*Real.exp (67231/524288 : ℝ)*Real.exp (-mu (radius 8 (2101/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903301947/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2101/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1159_exp_radius
  have hrNumeric : (984098428557/1000000000000 : ℝ) ≤ Real.exp (-2101/131072 : ℝ) ∧ Real.exp (-2101/131072 : ℝ) ≤ (492049214279/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984098428557/1000000000000 : ℝ) ≤ (radius 8 (2101/16384 : ℝ)) ∧ (radius 8 (2101/16384 : ℝ)) ≤ (492049214279/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2101/16384 : ℝ)) (984098428557/1000000000000 : ℝ) (492049214279/500000000000 : ℝ) (177623993057/1000000000000 : ℝ) (177623993063/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2101/16384 : ℝ)) (984098428557/1000000000000 : ℝ) (492049214279/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984098428557/1000000000000 : ℝ) (492049214279/500000000000 : ℝ) (496024607139/500000000000 : ℝ) (992049214279/1000000000000 : ℝ) (992017352951/1000000000000 : ℝ) (992017352953/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 1 (496024607139/500000000000 : ℝ) (992049214279/1000000000000 : ℝ) (992017352951/1000000000000 : ℝ) (992017352953/1000000000000 : ℝ) (496016641807/500000000000 : ℝ) (31001040113/31250000000 : ℝ) (496016641743/500000000000 : ℝ) (992033283489/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 2 (496016641807/500000000000 : ℝ) (31001040113/31250000000 : ℝ) (496016641743/500000000000 : ℝ) (992033283489/1000000000000 : ℝ) (19840665671/20000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 3 (19840665671/20000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 4 (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 5 (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 6 (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2101/16384 : ℝ)) 7 (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2101/16384 : ℝ))) (177623993057/1000000000000 : ℝ) (177623993063/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177623993057/1000000000000 : ℝ) (177623993063/1000000000000 : ℝ) (36800749783/62500000000 : ℝ) (147202999133/250000000000 : ℝ) (84290923131/200000000000 : ℝ) (421454615663/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 1 (36800749783/62500000000 : ℝ) (147202999133/250000000000 : ℝ) (84290923131/200000000000 : ℝ) (421454615663/1000000000000 : ℝ) (505133306091/1000000000000 : ℝ) (252566653049/500000000000 : ℝ) (12453853161/25000000000 : ℝ) (498154126447/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 2 (505133306091/1000000000000 : ℝ) (252566653049/500000000000 : ℝ) (12453853161/25000000000 : ℝ) (498154126447/1000000000000 : ℝ) (100328743253/200000000000 : ℝ) (501643716273/1000000000000 : ℝ) (250815789391/500000000000 : ℝ) (50163157879/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 3 (100328743253/200000000000 : ℝ) (501643716273/1000000000000 : ℝ) (250815789391/500000000000 : ℝ) (50163157879/100000000000 : ℝ) (501637647523/1000000000000 : ℝ) (125409411883/250000000000 : ℝ) (250818823743/500000000000 : ℝ) (100327529499/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 4 (501637647523/1000000000000 : ℝ) (125409411883/250000000000 : ℝ) (250818823743/500000000000 : ℝ) (100327529499/200000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 5 (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 6 (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2101/16384 : ℝ))) 7 (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2101/16384 : ℝ)) hmem 8 (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2101/16384 : ℝ))) hcmem 8 (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2101/16384 : ℝ)) (992033283549/1000000000000 : ℝ) (992033283553/1000000000000 : ℝ) (31352352969/62500000000 : ℝ) (250818823757/500000000000 : ℝ) (158859705041/200000000000 : ℝ) (31771941009/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1159_exp_lower
  have heNumeric : (2054903301947/1000000000000 : ℝ)/4 ≤ Real.exp (-3410255714777/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903301947/1000000000000 : ℝ)/4 ≤ Real.exp ((67231/524288 : ℝ)-(31771941009/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67231/524288 : ℝ) (2101/16384 : ℝ) (31771941009/40000000000 : ℝ) (2054903301947/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1160; no trusted numerical premise.
theorem cover8_leaf1160_exp_radius : (2494995766311897/2500000000000000 : ℝ) ≤ Real.exp ((-67233/4194304 : ℝ)/8) ∧ Real.exp ((-67233/4194304 : ℝ)/8) ≤ (997998306524758801/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67233/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1160_exp_lower : (460056773712769573/500000000000000000 : ℝ) ≤ Real.exp ((-2664262254083/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664262254083/4000000000000 : ℝ)/8) ≤ (920113547425539147/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664262254083/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1160_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903313807/1000000000000 : ℝ) ≤ 4*Real.exp (2101/16384 : ℝ)*Real.exp (-mu (radius 8 (67233/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903313807/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67233/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1160_exp_radius
  have hrNumeric : (98409819393/100000000000 : ℝ) ≤ Real.exp (-67233/4194304 : ℝ) ∧ Real.exp (-67233/4194304 : ℝ) ≤ (984098193931/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98409819393/100000000000 : ℝ) ≤ (radius 8 (67233/524288 : ℝ)) ∧ (radius 8 (67233/524288 : ℝ)) ≤ (984098193931/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67233/524288 : ℝ)) (98409819393/100000000000 : ℝ) (984098193931/1000000000000 : ℝ) (177625292967/1000000000000 : ℝ) (177625292973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67233/524288 : ℝ)) (98409819393/100000000000 : ℝ) (984098193931/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98409819393/100000000000 : ℝ) (984098193931/1000000000000 : ℝ) (198409819393/200000000000 : ℝ) (496024548483/500000000000 : ℝ) (496008617347/500000000000 : ℝ) (198403446939/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 1 (198409819393/200000000000 : ℝ) (496024548483/500000000000 : ℝ) (496008617347/500000000000 : ℝ) (198403446939/200000000000 : ℝ) (992033165829/1000000000000 : ℝ) (992033165831/1000000000000 : ℝ) (992033165701/1000000000000 : ℝ) (992033165703/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 2 (992033165829/1000000000000 : ℝ) (992033165831/1000000000000 : ℝ) (992033165701/1000000000000 : ℝ) (992033165703/1000000000000 : ℝ) (198406633153/200000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 3 (198406633153/200000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 4 (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 5 (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 6 (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67233/524288 : ℝ)) 7 (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67233/524288 : ℝ))) (177625292967/1000000000000 : ℝ) (177625292973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177625292967/1000000000000 : ℝ) (177625292973/1000000000000 : ℝ) (588812646483/1000000000000 : ℝ) (588812646487/1000000000000 : ℝ) (421456157823/1000000000000 : ℝ) (421456157831/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 1 (588812646483/1000000000000 : ℝ) (588812646487/1000000000000 : ℝ) (421456157823/1000000000000 : ℝ) (421456157831/1000000000000 : ℝ) (505134402153/1000000000000 : ℝ) (505134402159/1000000000000 : ℝ) (498155312793/1000000000000 : ℝ) (622694141/1250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 2 (505134402153/1000000000000 : ℝ) (505134402159/1000000000000 : ℝ) (498155312793/1000000000000 : ℝ) (622694141/1250000000 : ℝ) (501644857473/1000000000000 : ℝ) (12541121437/25000000000 : ℝ) (501632720331/1000000000000 : ℝ) (250816360169/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 3 (501644857473/1000000000000 : ℝ) (12541121437/25000000000 : ℝ) (501632720331/1000000000000 : ℝ) (250816360169/500000000000 : ℝ) (250819394451/500000000000 : ℝ) (501638788909/1000000000000 : ℝ) (100327757773/200000000000 : ℝ) (501638788873/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 4 (250819394451/500000000000 : ℝ) (501638788909/1000000000000 : ℝ) (100327757773/200000000000 : ℝ) (501638788873/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 5 (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 6 (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67233/524288 : ℝ))) 7 (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67233/524288 : ℝ)) hmem 8 (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67233/524288 : ℝ))) hcmem 8 (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67233/524288 : ℝ)) (248008291441/250000000000 : ℝ) (992033165767/1000000000000 : ℝ) (501638788883/1000000000000 : ℝ) (501638788891/1000000000000 : ℝ) (397150213393/500000000000 : ℝ) (397150213401/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1160_exp_lower
  have heNumeric : (2054903313807/1000000000000 : ℝ)/4 ≤ Real.exp (-2664262254083/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903313807/1000000000000 : ℝ)/4 ≤ Real.exp ((2101/16384 : ℝ)-(397150213401/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2101/16384 : ℝ) (67233/524288 : ℝ) (397150213401/500000000000 : ℝ) (2054903313807/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1161; no trusted numerical premise.
theorem cover8_leaf1161_exp_radius : (99799827678209197/100000000000000000 : ℝ) ≤ Real.exp ((-33617/2097152 : ℝ)/8) ∧ Real.exp ((-33617/2097152 : ℝ)/8) ≤ (997998276782091971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33617/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1161_exp_lower : (230028387022771013/250000000000000000 : ℝ) ≤ Real.exp ((-85256391389967/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256391389967/128000000000000 : ℝ)/8) ≤ (920113548091084053/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256391389967/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1161_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451662849/500000000000 : ℝ) ≤ 4*Real.exp (67233/524288 : ℝ)*Real.exp (-mu (radius 8 (33617/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451662849/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33617/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1161_exp_radius
  have hrNumeric : (984097959303/1000000000000 : ℝ) ≤ Real.exp (-33617/2097152 : ℝ) ∧ Real.exp (-33617/2097152 : ℝ) ≤ (123012244913/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984097959303/1000000000000 : ℝ) ≤ (radius 8 (33617/262144 : ℝ)) ∧ (radius 8 (33617/262144 : ℝ)) ≤ (123012244913/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33617/262144 : ℝ)) (984097959303/1000000000000 : ℝ) (123012244913/125000000000 : ℝ) (177626592867/1000000000000 : ℝ) (88813296437/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33617/262144 : ℝ)) (984097959303/1000000000000 : ℝ) (123012244913/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984097959303/1000000000000 : ℝ) (123012244913/125000000000 : ℝ) (992048979651/1000000000000 : ℝ) (248012244913/250000000000 : ℝ) (248004279109/250000000000 : ℝ) (496008558219/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 1 (992048979651/1000000000000 : ℝ) (248012244913/250000000000 : ℝ) (248004279109/250000000000 : ℝ) (496008558219/500000000000 : ℝ) (992033048043/1000000000000 : ℝ) (198406609609/200000000000 : ℝ) (198406609583/200000000000 : ℝ) (496016523959/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 2 (992033048043/1000000000000 : ℝ) (198406609609/200000000000 : ℝ) (198406609583/200000000000 : ℝ) (496016523959/500000000000 : ℝ) (992033047979/1000000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 3 (992033047979/1000000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 4 (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 5 (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 6 (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33617/262144 : ℝ)) 7 (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33617/262144 : ℝ))) (177626592867/1000000000000 : ℝ) (88813296437/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177626592867/1000000000000 : ℝ) (88813296437/500000000000 : ℝ) (588813296433/1000000000000 : ℝ) (588813296437/1000000000000 : ℝ) (421457699973/1000000000000 : ℝ) (210728849991/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 1 (588813296433/1000000000000 : ℝ) (588813296437/1000000000000 : ℝ) (421457699973/1000000000000 : ℝ) (210728849991/500000000000 : ℝ) (505135498203/1000000000000 : ℝ) (50513549821/100000000000 : ℝ) (124539124783/250000000000 : ℝ) (24907824957/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 2 (505135498203/1000000000000 : ℝ) (50513549821/100000000000 : ℝ) (124539124783/250000000000 : ℝ) (24907824957/50000000000 : ℝ) (501645998667/1000000000000 : ℝ) (20065839947/40000000000 : ℝ) (501633861867/1000000000000 : ℝ) (125408465469/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 3 (501645998667/1000000000000 : ℝ) (20065839947/40000000000 : ℝ) (501633861867/1000000000000 : ℝ) (125408465469/250000000000 : ℝ) (501639930267/1000000000000 : ℝ) (125409982569/250000000000 : ℝ) (50163993023/100000000000 : ℝ) (501639930239/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 4 (501639930267/1000000000000 : ℝ) (125409982569/250000000000 : ℝ) (50163993023/100000000000 : ℝ) (501639930239/1000000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 5 (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 6 (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33617/262144 : ℝ))) 7 (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33617/262144 : ℝ)) hmem 8 (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33617/262144 : ℝ))) hcmem 8 (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33617/262144 : ℝ)) (496016523989/500000000000 : ℝ) (496016523991/500000000000 : ℝ) (62704991281/125000000000 : ℝ) (250819965129/500000000000 : ℝ) (99287791043/125000000000 : ℝ) (198575582091/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1161_exp_lower
  have heNumeric : (1027451662849/500000000000 : ℝ)/4 ≤ Real.exp (-85256391389967/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451662849/500000000000 : ℝ)/4 ≤ Real.exp ((67233/524288 : ℝ)-(198575582091/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67233/524288 : ℝ) (33617/262144 : ℝ) (198575582091/250000000000 : ℝ) (1027451662849/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1162; no trusted numerical premise.
theorem cover8_leaf1162_exp_radius : (498999123519713013/500000000000000000 : ℝ) ≤ Real.exp ((-67235/4194304 : ℝ)/8) ∧ Real.exp ((-67235/4194304 : ℝ)/8) ≤ (997998247039426027/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67235/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1162_exp_lower : (92011354875915927/100000000000000000 : ℝ) ≤ Real.exp ((-42628195323231/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628195323231/64000000000000 : ℝ)/8) ≤ (920113548759159271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628195323231/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1162_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451668817/500000000000 : ℝ) ≤ 4*Real.exp (33617/262144 : ℝ)*Real.exp (-mu (radius 8 (67235/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451668817/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67235/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1162_exp_radius
  have hrNumeric : (246024431169/250000000000 : ℝ) ≤ Real.exp (-67235/4194304 : ℝ) ∧ Real.exp (-67235/4194304 : ℝ) ≤ (984097724677/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246024431169/250000000000 : ℝ) ≤ (radius 8 (67235/524288 : ℝ)) ∧ (radius 8 (67235/524288 : ℝ)) ≤ (984097724677/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67235/524288 : ℝ)) (246024431169/250000000000 : ℝ) (984097724677/1000000000000 : ℝ) (177627892757/1000000000000 : ℝ) (44406973191/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67235/524288 : ℝ)) (246024431169/250000000000 : ℝ) (984097724677/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246024431169/250000000000 : ℝ) (984097724677/1000000000000 : ℝ) (496024431169/500000000000 : ℝ) (992048862339/1000000000000 : ℝ) (496008499089/500000000000 : ℝ) (49600849909/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 1 (496024431169/500000000000 : ℝ) (992048862339/1000000000000 : ℝ) (496008499089/500000000000 : ℝ) (49600849909/50000000000 : ℝ) (496016465129/500000000000 : ℝ) (49601646513/50000000000 : ℝ) (99203293013/100000000000 : ℝ) (248008232533/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 2 (496016465129/500000000000 : ℝ) (49601646513/50000000000 : ℝ) (99203293013/100000000000 : ℝ) (248008232533/250000000000 : ℝ) (496016465097/500000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 3 (496016465097/500000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 4 (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 5 (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 6 (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67235/524288 : ℝ)) 7 (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67235/524288 : ℝ))) (177627892757/1000000000000 : ℝ) (44406973191/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177627892757/1000000000000 : ℝ) (44406973191/250000000000 : ℝ) (294406973189/500000000000 : ℝ) (294406973191/500000000000 : ℝ) (210729621053/500000000000 : ℝ) (84291848423/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 1 (294406973189/500000000000 : ℝ) (294406973191/500000000000 : ℝ) (210729621053/500000000000 : ℝ) (84291848423/200000000000 : ℝ) (252568297121/500000000000 : ℝ) (505136594249/1000000000000 : ℝ) (498157685459/1000000000000 : ℝ) (498157685467/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 2 (252568297121/500000000000 : ℝ) (505136594249/1000000000000 : ℝ) (498157685459/1000000000000 : ℝ) (498157685467/1000000000000 : ℝ) (10032942797/20000000000 : ℝ) (250823569929/500000000000 : ℝ) (489877933/976562500 : ℝ) (2508175017/5000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 3 (10032942797/20000000000 : ℝ) (250823569929/500000000000 : ℝ) (489877933/976562500 : ℝ) (2508175017/5000000000 : ℝ) (501641071621/1000000000000 : ℝ) (501641071629/1000000000000 : ℝ) (15676283487/31250000000 : ℝ) (501641071593/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 4 (501641071621/1000000000000 : ℝ) (501641071629/1000000000000 : ℝ) (15676283487/31250000000 : ℝ) (501641071593/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 5 (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 6 (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67235/524288 : ℝ))) 7 (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67235/524288 : ℝ)) hmem 8 (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67235/524288 : ℝ))) hcmem 8 (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67235/524288 : ℝ)) (992032930193/1000000000000 : ℝ) (248008232549/250000000000 : ℝ) (250820535801/500000000000 : ℝ) (501641071611/1000000000000 : ℝ) (397152114943/500000000000 : ℝ) (49644014369/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1162_exp_lower
  have heNumeric : (1027451668817/500000000000 : ℝ)/4 ≤ Real.exp (-42628195323231/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451668817/500000000000 : ℝ)/4 ≤ Real.exp ((33617/262144 : ℝ)-(49644014369/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33617/262144 : ℝ) (67235/524288 : ℝ) (49644014369/62500000000 : ℝ) (1027451668817/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1163; no trusted numerical premise.
theorem cover8_leaf1163_exp_radius : (997998217296760969/1000000000000000000 : ℝ) ≤ Real.exp ((-16809/1048576 : ℝ)/8) ∧ Real.exp ((-16809/1048576 : ℝ)/8) ≤ (99799821729676097/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16809/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1163_exp_lower : (920113549428154603/1000000000000000000 : ℝ) ≤ Real.exp ((-85256389901933/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256389901933/128000000000000 : ℝ)/8) ≤ (230028387357038651/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256389901933/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1163_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903349587/1000000000000 : ℝ) ≤ 4*Real.exp (67235/524288 : ℝ)*Real.exp (-mu (radius 8 (16809/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903349587/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16809/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1163_exp_radius
  have hrNumeric : (7688261641/7812500000 : ℝ) ≤ Real.exp (-16809/1048576 : ℝ) ∧ Real.exp (-16809/1048576 : ℝ) ≤ (984097490049/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7688261641/7812500000 : ℝ) ≤ (radius 8 (16809/131072 : ℝ)) ∧ (radius 8 (16809/131072 : ℝ)) ≤ (984097490049/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16809/131072 : ℝ)) (7688261641/7812500000 : ℝ) (984097490049/1000000000000 : ℝ) (177629192643/1000000000000 : ℝ) (3552583853/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16809/131072 : ℝ)) (7688261641/7812500000 : ℝ) (984097490049/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7688261641/7812500000 : ℝ) (984097490049/1000000000000 : ℝ) (15500761641/15625000000 : ℝ) (39681949801/40000000000 : ℝ) (12400210999/12500000000 : ℝ) (496008439961/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 1 (15500761641/15625000000 : ℝ) (39681949801/40000000000 : ℝ) (12400210999/12500000000 : ℝ) (496008439961/500000000000 : ℝ) (124004101559/125000000000 : ℝ) (496016406237/500000000000 : ℝ) (124004101543/125000000000 : ℝ) (496016406173/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 2 (124004101559/125000000000 : ℝ) (496016406237/500000000000 : ℝ) (124004101543/125000000000 : ℝ) (496016406173/500000000000 : ℝ) (124004101551/125000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 3 (124004101551/125000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 4 (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 5 (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 6 (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16809/131072 : ℝ)) 7 (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16809/131072 : ℝ))) (177629192643/1000000000000 : ℝ) (3552583853/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177629192643/1000000000000 : ℝ) (3552583853/20000000000 : ℝ) (588814596321/1000000000000 : ℝ) (23552583853/40000000000 : ℝ) (421460784229/1000000000000 : ℝ) (210730392119/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 1 (588814596321/1000000000000 : ℝ) (23552583853/40000000000 : ℝ) (421460784229/1000000000000 : ℝ) (210730392119/500000000000 : ℝ) (20205507611/40000000000 : ℝ) (252568845141/500000000000 : ℝ) (498158871777/1000000000000 : ℝ) (99631774357/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 2 (20205507611/40000000000 : ℝ) (252568845141/500000000000 : ℝ) (498158871777/1000000000000 : ℝ) (99631774357/200000000000 : ℝ) (250824140513/500000000000 : ℝ) (250824140517/500000000000 : ℝ) (501636144909/1000000000000 : ℝ) (501636144917/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 3 (250824140513/500000000000 : ℝ) (250824140517/500000000000 : ℝ) (501636144909/1000000000000 : ℝ) (501636144917/1000000000000 : ℝ) (501642212967/1000000000000 : ℝ) (31352638311/62500000000 : ℝ) (50164221293/100000000000 : ℝ) (501642212939/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 4 (501642212967/1000000000000 : ℝ) (31352638311/62500000000 : ℝ) (50164221293/100000000000 : ℝ) (501642212939/1000000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 5 (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 6 (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16809/131072 : ℝ))) 7 (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16809/131072 : ℝ)) hmem 8 (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16809/131072 : ℝ))) hcmem 8 (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16809/131072 : ℝ)) (992032812407/1000000000000 : ℝ) (99203281241/100000000000 : ℝ) (125410553237/250000000000 : ℝ) (250821106479/500000000000 : ℝ) (99288266427/125000000000 : ℝ) (198576532859/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1163_exp_lower
  have heNumeric : (2054903349587/1000000000000 : ℝ)/4 ≤ Real.exp (-85256389901933/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903349587/1000000000000 : ℝ)/4 ≤ Real.exp ((67235/524288 : ℝ)-(198576532859/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67235/524288 : ℝ) (16809/131072 : ℝ) (198576532859/250000000000 : ℝ) (2054903349587/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1164; no trusted numerical premise.
theorem cover8_leaf1164_exp_radius : (498999093777048399/500000000000000000 : ℝ) ≤ Real.exp ((-67237/4194304 : ℝ)/8) ∧ Real.exp ((-67237/4194304 : ℝ)/8) ≤ (997998187554096799/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67237/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1164_exp_lower : (230028387525121337/250000000000000000 : ℝ) ≤ Real.exp ((-21314097288423/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314097288423/32000000000000 : ℝ)/8) ≤ (920113550100485349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314097288423/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1164_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903361599/1000000000000 : ℝ) ≤ 4*Real.exp (16809/131072 : ℝ)*Real.exp (-mu (radius 8 (67237/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903361599/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67237/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1164_exp_radius
  have hrNumeric : (984097255421/1000000000000 : ℝ) ≤ Real.exp (-67237/4194304 : ℝ) ∧ Real.exp (-67237/4194304 : ℝ) ≤ (492048627711/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984097255421/1000000000000 : ℝ) ≤ (radius 8 (67237/524288 : ℝ)) ∧ (radius 8 (67237/524288 : ℝ)) ≤ (492048627711/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67237/524288 : ℝ)) (984097255421/1000000000000 : ℝ) (492048627711/500000000000 : ℝ) (88815246257/500000000000 : ℝ) (4440762313/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67237/524288 : ℝ)) (984097255421/1000000000000 : ℝ) (492048627711/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984097255421/1000000000000 : ℝ) (492048627711/500000000000 : ℝ) (99204862771/100000000000 : ℝ) (992048627711/1000000000000 : ℝ) (992016761663/1000000000000 : ℝ) (15500261901/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 1 (99204862771/100000000000 : ℝ) (992048627711/1000000000000 : ℝ) (992016761663/1000000000000 : ℝ) (15500261901/15625000000 : ℝ) (496016347343/500000000000 : ℝ) (31001021709/31250000000 : ℝ) (496016347279/500000000000 : ℝ) (6200204341/6250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 2 (496016347343/500000000000 : ℝ) (31001021709/31250000000 : ℝ) (496016347279/500000000000 : ℝ) (6200204341/6250000000 : ℝ) (496016347311/500000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 3 (496016347311/500000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 4 (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 5 (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 6 (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67237/524288 : ℝ)) 7 (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67237/524288 : ℝ))) (88815246257/500000000000 : ℝ) (4440762313/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88815246257/500000000000 : ℝ) (4440762313/25000000000 : ℝ) (588815246257/1000000000000 : ℝ) (29440762313/50000000000 : ℝ) (52682790791/125000000000 : ℝ) (6585348849/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 1 (588815246257/1000000000000 : ℝ) (29440762313/50000000000 : ℝ) (52682790791/125000000000 : ℝ) (6585348849/15625000000 : ℝ) (126284696573/250000000000 : ℝ) (252569393149/500000000000 : ℝ) (249080029039/500000000000 : ℝ) (99632011617/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 2 (126284696573/250000000000 : ℝ) (252569393149/500000000000 : ℝ) (249080029039/500000000000 : ℝ) (99632011617/200000000000 : ℝ) (100329884437/200000000000 : ℝ) (31353088887/62500000000 : ℝ) (501637286409/1000000000000 : ℝ) (501637286417/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 3 (100329884437/200000000000 : ℝ) (31353088887/62500000000 : ℝ) (501637286409/1000000000000 : ℝ) (501637286417/1000000000000 : ℝ) (501643354297/1000000000000 : ℝ) (100328670861/200000000000 : ℝ) (25082167713/50000000000 : ℝ) (125410838567/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 4 (501643354297/1000000000000 : ℝ) (100328670861/200000000000 : ℝ) (25082167713/50000000000 : ℝ) (125410838567/250000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 5 (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 6 (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67237/524288 : ℝ))) 7 (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67237/524288 : ℝ)) hmem 8 (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67237/524288 : ℝ))) hcmem 8 (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67237/524288 : ℝ)) (992032694621/1000000000000 : ℝ) (31001021707/31250000000 : ℝ) (250821677139/500000000000 : ℝ) (501643354287/1000000000000 : ℝ) (794308032921/1000000000000 : ℝ) (794308032939/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1164_exp_lower
  have heNumeric : (2054903361599/1000000000000 : ℝ)/4 ≤ Real.exp (-21314097288423/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903361599/1000000000000 : ℝ)/4 ≤ Real.exp ((16809/131072 : ℝ)-(794308032939/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16809/131072 : ℝ) (67237/524288 : ℝ) (794308032939/1000000000000 : ℝ) (2054903361599/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1165; no trusted numerical premise.
theorem cover8_leaf1165_exp_radius : (997998157811433513/1000000000000000000 : ℝ) ≤ Real.exp ((-33619/2097152 : ℝ)/8) ∧ Real.exp ((-33619/2097152 : ℝ)/8) ≤ (498999078905716757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33619/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1165_exp_lower : (460056775387500681/500000000000000000 : ℝ) ≤ Real.exp ((-85256388403019/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256388403019/128000000000000 : ℝ)/8) ≤ (920113550775001363/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256388403019/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1165_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098067473/20000000000 : ℝ) ≤ 4*Real.exp (67237/524288 : ℝ)*Real.exp (-mu (radius 8 (33619/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (41098067473/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33619/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1165_exp_radius
  have hrNumeric : (492048510397/500000000000 : ℝ) ≤ Real.exp (-33619/2097152 : ℝ) ∧ Real.exp (-33619/2097152 : ℝ) ≤ (196819404159/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492048510397/500000000000 : ℝ) ≤ (radius 8 (33619/262144 : ℝ)) ∧ (radius 8 (33619/262144 : ℝ)) ≤ (196819404159/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33619/262144 : ℝ)) (492048510397/500000000000 : ℝ) (196819404159/200000000000 : ℝ) (1421054339/8000000000 : ℝ) (177631792381/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33619/262144 : ℝ)) (492048510397/500000000000 : ℝ) (196819404159/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492048510397/500000000000 : ℝ) (196819404159/200000000000 : ℝ) (992048510397/1000000000000 : ℝ) (496024255199/500000000000 : ℝ) (198403328681/200000000000 : ℝ) (992016643407/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 1 (992048510397/1000000000000 : ℝ) (496024255199/500000000000 : ℝ) (198403328681/200000000000 : ℝ) (992016643407/1000000000000 : ℝ) (992032576901/1000000000000 : ℝ) (992032576903/1000000000000 : ℝ) (992032576773/1000000000000 : ℝ) (39681303071/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 2 (992032576901/1000000000000 : ℝ) (992032576903/1000000000000 : ℝ) (992032576773/1000000000000 : ℝ) (39681303071/40000000000 : ℝ) (992032576837/1000000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 3 (992032576837/1000000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 4 (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 5 (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 6 (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33619/262144 : ℝ)) 7 (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33619/262144 : ℝ))) (1421054339/8000000000 : ℝ) (177631792381/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1421054339/8000000000 : ℝ) (177631792381/1000000000000 : ℝ) (588815896187/1000000000000 : ℝ) (588815896191/1000000000000 : ℝ) (421463868409/1000000000000 : ℝ) (421463868417/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 1 (588815896187/1000000000000 : ℝ) (588815896191/1000000000000 : ℝ) (421463868409/1000000000000 : ℝ) (421463868417/1000000000000 : ℝ) (252569941149/500000000000 : ℝ) (7892810661/15625000000 : ℝ) (99632248873/200000000000 : ℝ) (124540311093/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 2 (252569941149/500000000000 : ℝ) (7892810661/15625000000 : ℝ) (99632248873/200000000000 : ℝ) (124540311093/250000000000 : ℝ) (501650563331/1000000000000 : ℝ) (250825281669/500000000000 : ℝ) (501638427897/1000000000000 : ℝ) (100327685581/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 3 (501650563331/1000000000000 : ℝ) (250825281669/500000000000 : ℝ) (501638427897/1000000000000 : ℝ) (100327685581/200000000000 : ℝ) (250822247807/500000000000 : ℝ) (250822247811/500000000000 : ℝ) (501644495577/1000000000000 : ℝ) (100328899117/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 4 (250822247807/500000000000 : ℝ) (250822247811/500000000000 : ℝ) (501644495577/1000000000000 : ℝ) (100328899117/200000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 5 (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 6 (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33619/262144 : ℝ))) 7 (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33619/262144 : ℝ)) hmem 8 (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33619/262144 : ℝ))) hcmem 8 (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33619/262144 : ℝ)) (248008144209/250000000000 : ℝ) (992032576839/1000000000000 : ℝ) (100328899119/200000000000 : ℝ) (125411123901/250000000000 : ℝ) (158861986881/200000000000 : ℝ) (794309934423/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1165_exp_lower
  have heNumeric : (41098067473/20000000000 : ℝ)/4 ≤ Real.exp (-85256388403019/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098067473/20000000000 : ℝ)/4 ≤ Real.exp ((67237/524288 : ℝ)-(794309934423/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67237/524288 : ℝ) (33619/262144 : ℝ) (794309934423/1000000000000 : ℝ) (41098067473/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1166; no trusted numerical premise.
theorem cover8_leaf1166_exp_radius : (199599625613754223/200000000000000000 : ℝ) ≤ Real.exp ((-67239/4194304 : ℝ)/8) ∧ Real.exp ((-67239/4194304 : ℝ)/8) ≤ (249499532017192779/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67239/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1166_exp_lower : (184022710290271521/200000000000000000 : ℝ) ≤ Real.exp ((-42628193825149/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628193825149/64000000000000 : ℝ)/8) ≤ (460056775725678803/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628193825149/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1166_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451692867/500000000000 : ℝ) ≤ 4*Real.exp (33619/262144 : ℝ)*Real.exp (-mu (radius 8 (67239/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451692867/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67239/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1166_exp_radius
  have hrNumeric : (984096786167/1000000000000 : ℝ) ≤ Real.exp (-67239/4194304 : ℝ) ∧ Real.exp (-67239/4194304 : ℝ) ≤ (123012098271/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984096786167/1000000000000 : ℝ) ≤ (radius 8 (67239/524288 : ℝ)) ∧ (radius 8 (67239/524288 : ℝ)) ≤ (123012098271/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67239/524288 : ℝ)) (984096786167/1000000000000 : ℝ) (123012098271/125000000000 : ℝ) (88816546113/500000000000 : ℝ) (22204136529/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67239/524288 : ℝ)) (984096786167/1000000000000 : ℝ) (123012098271/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984096786167/1000000000000 : ℝ) (123012098271/125000000000 : ℝ) (992048393083/1000000000000 : ℝ) (248012098271/250000000000 : ℝ) (248004131287/250000000000 : ℝ) (992016525149/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 1 (992048393083/1000000000000 : ℝ) (248012098271/250000000000 : ℝ) (248004131287/250000000000 : ℝ) (992016525149/1000000000000 : ℝ) (198406491823/200000000000 : ℝ) (992032459117/1000000000000 : ℝ) (992032458987/1000000000000 : ℝ) (992032458989/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 2 (198406491823/200000000000 : ℝ) (992032459117/1000000000000 : ℝ) (992032458987/1000000000000 : ℝ) (992032458989/1000000000000 : ℝ) (992032459051/1000000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 3 (992032459051/1000000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 4 (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 5 (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 6 (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67239/524288 : ℝ)) 7 (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67239/524288 : ℝ))) (88816546113/500000000000 : ℝ) (22204136529/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88816546113/500000000000 : ℝ) (22204136529/125000000000 : ℝ) (588816546113/1000000000000 : ℝ) (147204136529/250000000000 : ℝ) (421465410473/1000000000000 : ℝ) (210732705241/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 1 (588816546113/1000000000000 : ℝ) (147204136529/250000000000 : ℝ) (421465410473/1000000000000 : ℝ) (210732705241/500000000000 : ℝ) (505140978293/1000000000000 : ℝ) (505140978299/1000000000000 : ℝ) (498162430639/1000000000000 : ℝ) (498162430647/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 2 (505140978293/1000000000000 : ℝ) (505140978299/1000000000000 : ℝ) (498162430639/1000000000000 : ℝ) (498162430647/1000000000000 : ℝ) (250825852233/500000000000 : ℝ) (501651704473/1000000000000 : ℝ) (250819784687/500000000000 : ℝ) (250819784691/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 3 (250825852233/500000000000 : ℝ) (501651704473/1000000000000 : ℝ) (250819784687/500000000000 : ℝ) (250819784691/500000000000 : ℝ) (12541140923/25000000000 : ℝ) (7838213077/15625000000 : ℝ) (501645636883/1000000000000 : ℝ) (501645636891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 4 (12541140923/25000000000 : ℝ) (7838213077/15625000000 : ℝ) (501645636883/1000000000000 : ℝ) (501645636891/1000000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 5 (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 6 (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67239/524288 : ℝ))) 7 (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67239/524288 : ℝ)) hmem 8 (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67239/524288 : ℝ))) hcmem 8 (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67239/524288 : ℝ)) (19840649181/20000000000 : ℝ) (992032459053/1000000000000 : ℝ) (501645636901/1000000000000 : ℝ) (50164563691/100000000000 : ℝ) (794311835873/1000000000000 : ℝ) (794311835891/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1166_exp_lower
  have heNumeric : (1027451692867/500000000000 : ℝ)/4 ≤ Real.exp (-42628193825149/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451692867/500000000000 : ℝ)/4 ≤ Real.exp ((33619/262144 : ℝ)-(794311835891/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33619/262144 : ℝ) (67239/524288 : ℝ) (794311835891/1000000000000 : ℝ) (1027451692867/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1167; no trusted numerical premise.
theorem cover8_leaf1167_exp_radius : (997998098326109603/1000000000000000000 : ℝ) ≤ Real.exp ((-8405/524288 : ℝ)/8) ∧ Real.exp ((-8405/524288 : ℝ)/8) ≤ (249499524581527401/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8405/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1167_exp_lower : (460056776065179587/500000000000000000 : ℝ) ≤ Real.exp ((-85256386894633/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256386894633/128000000000000 : ℝ)/8) ≤ (36804542085214367/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256386894633/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1167_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451698933/500000000000 : ℝ) ≤ 4*Real.exp (67239/524288 : ℝ)*Real.exp (-mu (radius 8 (8405/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451698933/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8405/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1167_exp_radius
  have hrNumeric : (49204827577/50000000000 : ℝ) ≤ Real.exp (-8405/524288 : ℝ) ∧ Real.exp (-8405/524288 : ℝ) ≤ (984096551541/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49204827577/50000000000 : ℝ) ≤ (radius 8 (8405/65536 : ℝ)) ∧ (radius 8 (8405/65536 : ℝ)) ≤ (984096551541/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8405/65536 : ℝ)) (49204827577/50000000000 : ℝ) (984096551541/1000000000000 : ℝ) (177634392067/1000000000000 : ℝ) (177634392073/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8405/65536 : ℝ)) (49204827577/50000000000 : ℝ) (984096551541/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49204827577/50000000000 : ℝ) (984096551541/1000000000000 : ℝ) (99204827577/100000000000 : ℝ) (992048275771/1000000000000 : ℝ) (99201640689/100000000000 : ℝ) (248004101723/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 1 (99204827577/100000000000 : ℝ) (992048275771/1000000000000 : ℝ) (99201640689/100000000000 : ℝ) (248004101723/250000000000 : ℝ) (99203234133/100000000000 : ℝ) (248008085333/250000000000 : ℝ) (496016170601/500000000000 : ℝ) (248008085301/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 2 (99203234133/100000000000 : ℝ) (248008085333/250000000000 : ℝ) (496016170601/500000000000 : ℝ) (248008085301/250000000000 : ℝ) (496016170633/500000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 3 (496016170633/500000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 4 (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 5 (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 6 (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8405/65536 : ℝ)) 7 (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8405/65536 : ℝ))) (177634392067/1000000000000 : ℝ) (177634392073/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177634392067/1000000000000 : ℝ) (177634392073/1000000000000 : ℝ) (588817196033/1000000000000 : ℝ) (588817196037/1000000000000 : ℝ) (10536673813/25000000000 : ℝ) (26341684533/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 1 (588817196033/1000000000000 : ℝ) (588817196037/1000000000000 : ℝ) (10536673813/25000000000 : ℝ) (26341684533/62500000000 : ℝ) (126285518569/250000000000 : ℝ) (505142074283/1000000000000 : ℝ) (4981636169/10000000000 : ℝ) (498163616907/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 2 (126285518569/250000000000 : ℝ) (505142074283/1000000000000 : ℝ) (4981636169/10000000000 : ℝ) (498163616907/1000000000000 : ℝ) (125413211397/250000000000 : ℝ) (100330569119/200000000000 : ℝ) (501640710837/1000000000000 : ℝ) (100328142169/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 3 (125413211397/250000000000 : ℝ) (100330569119/200000000000 : ℝ) (501640710837/1000000000000 : ℝ) (100328142169/200000000000 : ℝ) (125411694553/250000000000 : ℝ) (25082338911/50000000000 : ℝ) (20065871127/40000000000 : ℝ) (62705847273/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 4 (125411694553/250000000000 : ℝ) (25082338911/50000000000 : ℝ) (20065871127/40000000000 : ℝ) (62705847273/125000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 5 (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 6 (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8405/65536 : ℝ))) 7 (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8405/65536 : ℝ)) hmem 8 (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8405/65536 : ℝ))) hcmem 8 (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8405/65536 : ℝ)) (198406468253/200000000000 : ℝ) (248008085317/250000000000 : ℝ) (501646778193/1000000000000 : ℝ) (250823389101/500000000000 : ℝ) (794313737319/1000000000000 : ℝ) (99289217167/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1167_exp_lower
  have heNumeric : (1027451698933/500000000000 : ℝ)/4 ≤ Real.exp (-85256386894633/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451698933/500000000000 : ℝ)/4 ≤ Real.exp ((67239/524288 : ℝ)-(99289217167/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67239/524288 : ℝ) (8405/65536 : ℝ) (99289217167/125000000000 : ℝ) (1027451698933/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1168; no trusted numerical premise.
theorem cover8_leaf1168_exp_radius : (997998068583448977/1000000000000000000 : ℝ) ≤ Real.exp ((-67241/4194304 : ℝ)/8) ∧ Real.exp ((-67241/4194304 : ℝ)/8) ≤ (498999034291724489/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67241/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1168_exp_lower : (920113552812006071/1000000000000000000 : ℝ) ≤ Real.exp ((-10657048267003/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657048267003/16000000000000 : ℝ)/8) ≤ (115014194101500759/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657048267003/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1168_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725852511/250000000000 : ℝ) ≤ 4*Real.exp (8405/65536 : ℝ)*Real.exp (-mu (radius 8 (67241/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725852511/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67241/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1168_exp_radius
  have hrNumeric : (492048158457/500000000000 : ℝ) ≤ Real.exp (-67241/4194304 : ℝ) ∧ Real.exp (-67241/4194304 : ℝ) ≤ (196819263383/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492048158457/500000000000 : ℝ) ≤ (radius 8 (67241/524288 : ℝ)) ∧ (radius 8 (67241/524288 : ℝ)) ≤ (196819263383/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67241/524288 : ℝ)) (492048158457/500000000000 : ℝ) (196819263383/200000000000 : ℝ) (177635691893/1000000000000 : ℝ) (177635691899/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67241/524288 : ℝ)) (492048158457/500000000000 : ℝ) (196819263383/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492048158457/500000000000 : ℝ) (196819263383/200000000000 : ℝ) (992048158457/1000000000000 : ℝ) (496024079229/500000000000 : ℝ) (992016288633/1000000000000 : ℝ) (496008144317/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 1 (992048158457/1000000000000 : ℝ) (496024079229/500000000000 : ℝ) (992016288633/1000000000000 : ℝ) (496008144317/500000000000 : ℝ) (198406444709/200000000000 : ℝ) (496016111773/500000000000 : ℝ) (992032223417/1000000000000 : ℝ) (992032223419/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 2 (198406444709/200000000000 : ℝ) (496016111773/500000000000 : ℝ) (992032223417/1000000000000 : ℝ) (992032223419/1000000000000 : ℝ) (992032223481/1000000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 3 (992032223481/1000000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 4 (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 5 (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 6 (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67241/524288 : ℝ)) 7 (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67241/524288 : ℝ))) (177635691893/1000000000000 : ℝ) (177635691899/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177635691893/1000000000000 : ℝ) (177635691899/1000000000000 : ℝ) (294408922973/500000000000 : ℝ) (11776356919/20000000000 : ℝ) (421468494543/1000000000000 : ℝ) (421468494551/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 1 (294408922973/500000000000 : ℝ) (11776356919/20000000000 : ℝ) (421468494543/1000000000000 : ℝ) (421468494551/1000000000000 : ℝ) (126285792561/250000000000 : ℝ) (505143170251/1000000000000 : ℝ) (498164803143/1000000000000 : ℝ) (9963296063/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 2 (126285792561/250000000000 : ℝ) (505143170251/1000000000000 : ℝ) (498164803143/1000000000000 : ℝ) (9963296063/20000000000 : ℝ) (501653986693/1000000000000 : ℝ) (501653986701/1000000000000 : ℝ) (125410463071/250000000000 : ℝ) (125410463073/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 3 (501653986693/1000000000000 : ℝ) (501653986701/1000000000000 : ℝ) (125410463071/250000000000 : ℝ) (125410463073/250000000000 : ℝ) (3919124371/7812500000 : ℝ) (501647919497/1000000000000 : ℝ) (501647919451/1000000000000 : ℝ) (25082395973/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 4 (3919124371/7812500000 : ℝ) (501647919497/1000000000000 : ℝ) (501647919451/1000000000000 : ℝ) (25082395973/50000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 5 (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 6 (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67241/524288 : ℝ))) 7 (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67241/524288 : ℝ)) hmem 8 (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67241/524288 : ℝ))) hcmem 8 (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67241/524288 : ℝ)) (24800805587/25000000000 : ℝ) (992032223483/1000000000000 : ℝ) (501647919469/1000000000000 : ℝ) (501647919479/1000000000000 : ℝ) (794315638739/1000000000000 : ℝ) (397157819379/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1168_exp_lower
  have heNumeric : (513725852511/250000000000 : ℝ)/4 ≤ Real.exp (-10657048267003/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725852511/250000000000 : ℝ)/4 ≤ Real.exp ((8405/65536 : ℝ)-(397157819379/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8405/65536 : ℝ) (67241/524288 : ℝ) (397157819379/500000000000 : ℝ) (513725852511/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1169; no trusted numerical premise.
theorem cover8_leaf1169_exp_radius : (498999019420394619/500000000000000000 : ℝ) ≤ Real.exp ((-33621/2097152 : ℝ)/8) ∧ Real.exp ((-33621/2097152 : ℝ)/8) ≤ (997998038840789239/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33621/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1169_exp_lower : (28753548546709003/31250000000000000 : ℝ) ≤ Real.exp ((-85256385376263/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256385376263/128000000000000 : ℝ)/8) ≤ (920113553494688097/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256385376263/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1169_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903422241/1000000000000 : ℝ) ≤ 4*Real.exp (67241/524288 : ℝ)*Real.exp (-mu (radius 8 (33621/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903422241/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33621/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1169_exp_radius
  have hrNumeric : (984096082287/1000000000000 : ℝ) ≤ Real.exp (-33621/2097152 : ℝ) ∧ Real.exp (-33621/2097152 : ℝ) ≤ (61506005143/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984096082287/1000000000000 : ℝ) ≤ (radius 8 (33621/262144 : ℝ)) ∧ (radius 8 (33621/262144 : ℝ)) ≤ (61506005143/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33621/262144 : ℝ)) (984096082287/1000000000000 : ℝ) (61506005143/62500000000 : ℝ) (88818495857/500000000000 : ℝ) (177636991721/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33621/262144 : ℝ)) (984096082287/1000000000000 : ℝ) (61506005143/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984096082287/1000000000000 : ℝ) (61506005143/62500000000 : ℝ) (992048041143/1000000000000 : ℝ) (124006005143/125000000000 : ℝ) (7936129363/8000000000 : ℝ) (992016170377/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 1 (992048041143/1000000000000 : ℝ) (124006005143/125000000000 : ℝ) (7936129363/8000000000 : ℝ) (992016170377/1000000000000 : ℝ) (992032105759/1000000000000 : ℝ) (992032105761/1000000000000 : ℝ) (992032105631/1000000000000 : ℝ) (992032105633/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 2 (992032105759/1000000000000 : ℝ) (992032105761/1000000000000 : ℝ) (992032105631/1000000000000 : ℝ) (992032105633/1000000000000 : ℝ) (198406421139/200000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 3 (198406421139/200000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 4 (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 5 (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 6 (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33621/262144 : ℝ)) 7 (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33621/262144 : ℝ))) (88818495857/500000000000 : ℝ) (177636991721/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88818495857/500000000000 : ℝ) (177636991721/1000000000000 : ℝ) (588818495857/1000000000000 : ℝ) (588818495861/1000000000000 : ℝ) (84294007311/200000000000 : ℝ) (105367509141/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 1 (588818495857/1000000000000 : ℝ) (588818495861/1000000000000 : ℝ) (84294007311/200000000000 : ℝ) (105367509141/250000000000 : ℝ) (252572133103/500000000000 : ℝ) (505144266213/1000000000000 : ℝ) (249082994689/500000000000 : ℝ) (249082994693/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 2 (252572133103/500000000000 : ℝ) (505144266213/1000000000000 : ℝ) (249082994689/500000000000 : ℝ) (249082994693/500000000000 : ℝ) (31353445487/62500000000 : ℝ) (2508275639/5000000000 : ℝ) (125410748431/250000000000 : ℝ) (501642993733/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 3 (31353445487/62500000000 : ℝ) (2508275639/5000000000 : ℝ) (125410748431/250000000000 : ℝ) (501642993733/1000000000000 : ℝ) (250824530379/500000000000 : ℝ) (501649060767/1000000000000 : ℝ) (501649060721/1000000000000 : ℝ) (50164906073/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 4 (250824530379/500000000000 : ℝ) (501649060767/1000000000000 : ℝ) (501649060721/1000000000000 : ℝ) (50164906073/100000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 5 (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 6 (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33621/262144 : ℝ))) 7 (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33621/262144 : ℝ)) hmem 8 (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33621/262144 : ℝ))) hcmem 8 (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33621/262144 : ℝ)) (496016052847/500000000000 : ℝ) (992032105697/1000000000000 : ℝ) (501649060739/1000000000000 : ℝ) (501649060749/1000000000000 : ℝ) (794317540151/1000000000000 : ℝ) (794317540171/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1169_exp_lower
  have heNumeric : (2054903422241/1000000000000 : ℝ)/4 ≤ Real.exp (-85256385376263/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903422241/1000000000000 : ℝ)/4 ≤ Real.exp ((67241/524288 : ℝ)-(794317540171/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67241/524288 : ℝ) (33621/262144 : ℝ) (794317540171/1000000000000 : ℝ) (2054903422241/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1170; no trusted numerical premise.
theorem cover8_leaf1170_exp_radius : (498999004549065193/500000000000000000 : ℝ) ≤ Real.exp ((-67243/4194304 : ℝ)/8) ∧ Real.exp ((-67243/4194304 : ℝ)/8) ≤ (997998009098130387/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67243/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1170_exp_lower : (230028388545061369/250000000000000000 : ℝ) ≤ Real.exp ((-42628192306651/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628192306651/64000000000000 : ℝ)/8) ≤ (920113554180245477/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628192306651/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1170_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490343449/100000000000 : ℝ) ≤ 4*Real.exp (33621/262144 : ℝ)*Real.exp (-mu (radius 8 (67243/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490343449/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67243/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1170_exp_radius
  have hrNumeric : (49204792383/50000000000 : ℝ) ≤ Real.exp (-67243/4194304 : ℝ) ∧ Real.exp (-67243/4194304 : ℝ) ≤ (984095847661/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49204792383/50000000000 : ℝ) ≤ (radius 8 (67243/524288 : ℝ)) ∧ (radius 8 (67243/524288 : ℝ)) ≤ (984095847661/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67243/524288 : ℝ)) (49204792383/50000000000 : ℝ) (984095847661/1000000000000 : ℝ) (88819145763/500000000000 : ℝ) (44409572883/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67243/524288 : ℝ)) (49204792383/50000000000 : ℝ) (984095847661/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49204792383/50000000000 : ℝ) (984095847661/1000000000000 : ℝ) (99204792383/100000000000 : ℝ) (992047923831/1000000000000 : ℝ) (496008026059/500000000000 : ℝ) (992016052119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 1 (99204792383/100000000000 : ℝ) (992047923831/1000000000000 : ℝ) (496008026059/500000000000 : ℝ) (992016052119/1000000000000 : ℝ) (496015993987/500000000000 : ℝ) (39681279519/40000000000 : ℝ) (496015993923/500000000000 : ℝ) (124003998481/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 2 (496015993987/500000000000 : ℝ) (39681279519/40000000000 : ℝ) (496015993923/500000000000 : ℝ) (124003998481/125000000000 : ℝ) (99203198791/100000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 3 (99203198791/100000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 4 (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 5 (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 6 (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67243/524288 : ℝ)) 7 (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67243/524288 : ℝ))) (88819145763/500000000000 : ℝ) (44409572883/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88819145763/500000000000 : ℝ) (44409572883/250000000000 : ℝ) (588819145763/1000000000000 : ℝ) (294409572883/500000000000 : ℝ) (8429431571/20000000000 : ℝ) (210735789279/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 1 (588819145763/1000000000000 : ℝ) (294409572883/500000000000 : ℝ) (8429431571/20000000000 : ℝ) (210735789279/500000000000 : ℝ) (126286340539/250000000000 : ℝ) (252572681081/500000000000 : ℝ) (498167175599/1000000000000 : ℝ) (249083587803/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 2 (126286340539/250000000000 : ℝ) (252572681081/500000000000 : ℝ) (498167175599/1000000000000 : ℝ) (249083587803/500000000000 : ℝ) (501656268877/1000000000000 : ℝ) (125414067221/250000000000 : ℝ) (501644135151/1000000000000 : ℝ) (501644135159/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 3 (501656268877/1000000000000 : ℝ) (125414067221/250000000000 : ℝ) (501644135151/1000000000000 : ℝ) (501644135159/1000000000000 : ℝ) (250825101007/500000000000 : ℝ) (250825101011/500000000000 : ℝ) (501650201977/1000000000000 : ℝ) (100330040397/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 4 (250825101007/500000000000 : ℝ) (250825101011/500000000000 : ℝ) (501650201977/1000000000000 : ℝ) (100330040397/200000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 5 (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 6 (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67243/524288 : ℝ))) 7 (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67243/524288 : ℝ)) hmem 8 (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67243/524288 : ℝ))) hcmem 8 (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67243/524288 : ℝ)) (992031987909/1000000000000 : ℝ) (124003998489/125000000000 : ℝ) (100330040399/200000000000 : ℝ) (125412550501/250000000000 : ℝ) (794319441541/1000000000000 : ℝ) (794319441559/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1170_exp_lower
  have heNumeric : (205490343449/100000000000 : ℝ)/4 ≤ Real.exp (-42628192306651/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490343449/100000000000 : ℝ)/4 ≤ Real.exp ((33621/262144 : ℝ)-(794319441559/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33621/262144 : ℝ) (67243/524288 : ℝ) (794319441559/1000000000000 : ℝ) (205490343449/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1171; no trusted numerical premise.
theorem cover8_leaf1171_exp_radius : (49899898967773621/50000000000000000 : ℝ) ≤ Real.exp ((-16811/1048576 : ℝ)/8) ∧ Real.exp ((-16811/1048576 : ℝ)/8) ≤ (997997979355472421/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16811/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1171_exp_lower : (920113554867528069/1000000000000000000 : ℝ) ≤ Real.exp ((-85256383848421/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256383848421/128000000000000 : ℝ)/8) ≤ (92011355486752807/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256383848421/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1171_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903446769/1000000000000 : ℝ) ≤ 4*Real.exp (67243/524288 : ℝ)*Real.exp (-mu (radius 8 (16811/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903446769/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16811/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1171_exp_radius
  have hrNumeric : (984095613033/1000000000000 : ℝ) ≤ Real.exp (-16811/1048576 : ℝ) ∧ Real.exp (-16811/1048576 : ℝ) ≤ (492047806517/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984095613033/1000000000000 : ℝ) ≤ (radius 8 (16811/131072 : ℝ)) ∧ (radius 8 (16811/131072 : ℝ)) ≤ (492047806517/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16811/131072 : ℝ)) (984095613033/1000000000000 : ℝ) (492047806517/500000000000 : ℝ) (5551237229/31250000000 : ℝ) (88819795667/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16811/131072 : ℝ)) (984095613033/1000000000000 : ℝ) (492047806517/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984095613033/1000000000000 : ℝ) (492047806517/500000000000 : ℝ) (248011951629/250000000000 : ℝ) (992047806517/1000000000000 : ℝ) (49600796693/50000000000 : ℝ) (992015933861/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 1 (248011951629/250000000000 : ℝ) (992047806517/1000000000000 : ℝ) (49600796693/50000000000 : ℝ) (992015933861/1000000000000 : ℝ) (248007967547/250000000000 : ℝ) (992031870189/1000000000000 : ℝ) (992031870059/1000000000000 : ℝ) (992031870061/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 2 (248007967547/250000000000 : ℝ) (992031870189/1000000000000 : ℝ) (992031870059/1000000000000 : ℝ) (992031870061/1000000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 3 (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 4 (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 5 (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 6 (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16811/131072 : ℝ)) 7 (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16811/131072 : ℝ))) (5551237229/31250000000 : ℝ) (88819795667/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5551237229/31250000000 : ℝ) (88819795667/500000000000 : ℝ) (36801237229/62500000000 : ℝ) (588819795667/1000000000000 : ℝ) (26342070033/62500000000 : ℝ) (52684140067/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 1 (36801237229/62500000000 : ℝ) (588819795667/1000000000000 : ℝ) (26342070033/62500000000 : ℝ) (52684140067/125000000000 : ℝ) (31571653631/62500000000 : ℝ) (252573229051/500000000000 : ℝ) (31135522613/62500000000 : ℝ) (99633672363/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 2 (31571653631/62500000000 : ℝ) (252573229051/500000000000 : ℝ) (31135522613/62500000000 : ℝ) (99633672363/200000000000 : ℝ) (15676794061/31250000000 : ℝ) (501657409959/1000000000000 : ℝ) (501645276567/1000000000000 : ℝ) (20065811063/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 3 (15676794061/31250000000 : ℝ) (501657409959/1000000000000 : ℝ) (501645276567/1000000000000 : ℝ) (20065811063/40000000000 : ℝ) (501651343259/1000000000000 : ℝ) (501651343267/1000000000000 : ℝ) (250825671611/500000000000 : ℝ) (501651343231/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 4 (501651343259/1000000000000 : ℝ) (501651343267/1000000000000 : ℝ) (250825671611/500000000000 : ℝ) (501651343231/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 5 (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 6 (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16811/131072 : ℝ))) 7 (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16811/131072 : ℝ)) hmem 8 (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16811/131072 : ℝ))) hcmem 8 (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16811/131072 : ℝ)) (992031870123/1000000000000 : ℝ) (7936254961/8000000000 : ℝ) (12541283581/25000000000 : ℝ) (501651343249/1000000000000 : ℝ) (158864268583/200000000000 : ℝ) (198580335733/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1171_exp_lower
  have heNumeric : (2054903446769/1000000000000 : ℝ)/4 ≤ Real.exp (-85256383848421/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903446769/1000000000000 : ℝ)/4 ≤ Real.exp ((67243/524288 : ℝ)-(198580335733/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67243/524288 : ℝ) (16811/131072 : ℝ) (198580335733/250000000000 : ℝ) (2054903446769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1172; no trusted numerical premise.
theorem cover8_leaf1172_exp_radius : (49899897480640767/50000000000000000 : ℝ) ≤ Real.exp ((-67245/4194304 : ℝ)/8) ∧ Real.exp ((-67245/4194304 : ℝ)/8) ≤ (997997949612815341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67245/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1172_exp_lower : (115014194444725129/125000000000000000 : ℝ) ≤ Real.exp ((-21314095770053/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314095770053/32000000000000 : ℝ)/8) ≤ (920113555557801033/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314095770053/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1172_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451729551/500000000000 : ℝ) ≤ 4*Real.exp (16811/131072 : ℝ)*Real.exp (-mu (radius 8 (67245/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451729551/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67245/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1172_exp_radius
  have hrNumeric : (984095378407/1000000000000 : ℝ) ≤ Real.exp (-67245/4194304 : ℝ) ∧ Real.exp (-67245/4194304 : ℝ) ≤ (123011922301/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984095378407/1000000000000 : ℝ) ≤ (radius 8 (67245/524288 : ℝ)) ∧ (radius 8 (67245/524288 : ℝ)) ≤ (123011922301/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67245/524288 : ℝ)) (984095378407/1000000000000 : ℝ) (123011922301/125000000000 : ℝ) (88820445557/500000000000 : ℝ) (177640891121/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67245/524288 : ℝ)) (984095378407/1000000000000 : ℝ) (123011922301/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984095378407/1000000000000 : ℝ) (123011922301/125000000000 : ℝ) (992047689203/1000000000000 : ℝ) (248011922301/250000000000 : ℝ) (992015815603/1000000000000 : ℝ) (248003953901/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 1 (992047689203/1000000000000 : ℝ) (248011922301/250000000000 : ℝ) (992015815603/1000000000000 : ℝ) (248003953901/250000000000 : ℝ) (992031752403/1000000000000 : ℝ) (248007938101/250000000000 : ℝ) (496015876137/500000000000 : ℝ) (248007938069/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 2 (992031752403/1000000000000 : ℝ) (248007938101/250000000000 : ℝ) (496015876137/500000000000 : ℝ) (248007938069/250000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 3 (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 4 (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 5 (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 6 (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67245/524288 : ℝ)) 7 (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67245/524288 : ℝ))) (88820445557/500000000000 : ℝ) (177640891121/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88820445557/500000000000 : ℝ) (177640891121/1000000000000 : ℝ) (588820445557/1000000000000 : ℝ) (588820445561/1000000000000 : ℝ) (421474662481/1000000000000 : ℝ) (42147466249/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 1 (588820445557/1000000000000 : ℝ) (588820445561/1000000000000 : ℝ) (421474662481/1000000000000 : ℝ) (42147466249/100000000000 : ℝ) (505147554019/1000000000000 : ℝ) (252573777013/500000000000 : ℝ) (249084773999/500000000000 : ℝ) (249084774003/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 2 (505147554019/1000000000000 : ℝ) (252573777013/500000000000 : ℝ) (249084773999/500000000000 : ℝ) (249084774003/500000000000 : ℝ) (15676829719/31250000000 : ℝ) (62707318877/125000000000 : ℝ) (100329283593/200000000000 : ℝ) (250823208987/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 3 (15676829719/31250000000 : ℝ) (62707318877/125000000000 : ℝ) (100329283593/200000000000 : ℝ) (250823208987/500000000000 : ℝ) (250826242243/500000000000 : ℝ) (100330496899/200000000000 : ℝ) (501652484449/1000000000000 : ℝ) (501652484459/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 4 (250826242243/500000000000 : ℝ) (100330496899/200000000000 : ℝ) (501652484449/1000000000000 : ℝ) (501652484459/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 5 (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 6 (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67245/524288 : ℝ))) 7 (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67245/524288 : ℝ)) hmem 8 (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67245/524288 : ℝ))) hcmem 8 (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67245/524288 : ℝ)) (496015876169/500000000000 : ℝ) (49601587617/50000000000 : ℝ) (501652484467/1000000000000 : ℝ) (501652484477/1000000000000 : ℝ) (39716162213/50000000000 : ℝ) (794323244279/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1172_exp_lower
  have heNumeric : (1027451729551/500000000000 : ℝ)/4 ≤ Real.exp (-21314095770053/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451729551/500000000000 : ℝ)/4 ≤ Real.exp ((16811/131072 : ℝ)-(794323244279/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16811/131072 : ℝ) (67245/524288 : ℝ) (794323244279/1000000000000 : ℝ) (1027451729551/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1173; no trusted numerical premise.
theorem cover8_leaf1173_exp_radius : (498998959935079573/500000000000000000 : ℝ) ≤ Real.exp ((-33623/2097152 : ℝ)/8) ∧ Real.exp ((-33623/2097152 : ℝ)/8) ≤ (997997919870159147/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33623/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1173_exp_lower : (57507097265583697/62500000000000000 : ℝ) ≤ Real.exp ((-17051276462119/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051276462119/25600000000000 : ℝ)/8) ≤ (920113556249339153/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051276462119/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1173_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903471457/1000000000000 : ℝ) ≤ 4*Real.exp (67245/524288 : ℝ)*Real.exp (-mu (radius 8 (33623/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903471457/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33623/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1173_exp_radius
  have hrNumeric : (49204757189/50000000000 : ℝ) ≤ Real.exp (-33623/2097152 : ℝ) ∧ Real.exp (-33623/2097152 : ℝ) ≤ (984095143781/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49204757189/50000000000 : ℝ) ≤ (radius 8 (33623/262144 : ℝ)) ∧ (radius 8 (33623/262144 : ℝ)) ≤ (984095143781/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33623/262144 : ℝ)) (49204757189/50000000000 : ℝ) (984095143781/1000000000000 : ℝ) (11102636931/62500000000 : ℝ) (177642190903/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33623/262144 : ℝ)) (49204757189/50000000000 : ℝ) (984095143781/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49204757189/50000000000 : ℝ) (984095143781/1000000000000 : ℝ) (99204757189/100000000000 : ℝ) (992047571891/1000000000000 : ℝ) (198403139469/200000000000 : ℝ) (992015697347/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 1 (99204757189/100000000000 : ℝ) (992047571891/1000000000000 : ℝ) (198403139469/200000000000 : ℝ) (992015697347/1000000000000 : ℝ) (992031634617/1000000000000 : ℝ) (992031634619/1000000000000 : ℝ) (992031634489/1000000000000 : ℝ) (992031634491/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 2 (992031634617/1000000000000 : ℝ) (992031634619/1000000000000 : ℝ) (992031634489/1000000000000 : ℝ) (992031634491/1000000000000 : ℝ) (992031634553/1000000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 3 (992031634553/1000000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 4 (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 5 (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 6 (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33623/262144 : ℝ)) 7 (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33623/262144 : ℝ))) (11102636931/62500000000 : ℝ) (177642190903/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11102636931/62500000000 : ℝ) (177642190903/1000000000000 : ℝ) (73602636931/125000000000 : ℝ) (147205273863/250000000000 : ℝ) (52684525553/125000000000 : ℝ) (421476204433/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 1 (73602636931/125000000000 : ℝ) (147205273863/250000000000 : ℝ) (52684525553/125000000000 : ℝ) (421476204433/1000000000000 : ℝ) (31571790621/62500000000 : ℝ) (505148649943/1000000000000 : ℝ) (24908536709/50000000000 : ℝ) (124542683547/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 2 (31571790621/62500000000 : ℝ) (505148649943/1000000000000 : ℝ) (24908536709/50000000000 : ℝ) (124542683547/250000000000 : ℝ) (250829846029/500000000000 : ℝ) (250829846033/500000000000 : ℝ) (125411889839/250000000000 : ℝ) (100329511873/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 3 (250829846029/500000000000 : ℝ) (250829846033/500000000000 : ℝ) (125411889839/250000000000 : ℝ) (100329511873/200000000000 : ℝ) (501653625707/1000000000000 : ℝ) (125413406429/250000000000 : ℝ) (50165362567/100000000000 : ℝ) (501653625679/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 4 (501653625707/1000000000000 : ℝ) (125413406429/250000000000 : ℝ) (50165362567/100000000000 : ℝ) (501653625679/1000000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 5 (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 6 (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33623/262144 : ℝ))) 7 (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33623/262144 : ℝ)) hmem 8 (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33623/262144 : ℝ))) hcmem 8 (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33623/262144 : ℝ)) (124003954319/125000000000 : ℝ) (198406326911/200000000000 : ℝ) (62706703211/125000000000 : ℝ) (250826812849/500000000000 : ℝ) (198581286399/250000000000 : ℝ) (158865029123/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1173_exp_lower
  have heNumeric : (2054903471457/1000000000000 : ℝ)/4 ≤ Real.exp (-17051276462119/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903471457/1000000000000 : ℝ)/4 ≤ Real.exp ((67245/524288 : ℝ)-(158865029123/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67245/524288 : ℝ) (33623/262144 : ℝ) (158865029123/200000000000 : ℝ) (2054903471457/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1174; no trusted numerical premise.
theorem cover8_leaf1174_exp_radius : (997997890127503839/1000000000000000000 : ℝ) ≤ Real.exp ((-67247/4194304 : ℝ)/8) ∧ Real.exp ((-67247/4194304 : ℝ)/8) ≤ (6237486813296899/6250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67247/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1174_exp_lower : (92011355694329257/100000000000000000 : ℝ) ≤ Real.exp ((-8525638153829/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525638153829/12800000000000 : ℝ)/8) ≤ (920113556943292571/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525638153829/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1174_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431467741/62500000000 : ℝ) ≤ 4*Real.exp (33623/262144 : ℝ)*Real.exp (-mu (radius 8 (67247/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431467741/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67247/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1174_exp_radius
  have hrNumeric : (984094909153/1000000000000 : ℝ) ≤ Real.exp (-67247/4194304 : ℝ) ∧ Real.exp (-67247/4194304 : ℝ) ≤ (492047454577/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984094909153/1000000000000 : ℝ) ≤ (radius 8 (67247/524288 : ℝ)) ∧ (radius 8 (67247/524288 : ℝ)) ≤ (492047454577/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67247/524288 : ℝ)) (984094909153/1000000000000 : ℝ) (492047454577/500000000000 : ℝ) (177643490669/1000000000000 : ℝ) (7105739627/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67247/524288 : ℝ)) (984094909153/1000000000000 : ℝ) (492047454577/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984094909153/1000000000000 : ℝ) (492047454577/500000000000 : ℝ) (62002965911/62500000000 : ℝ) (992047454577/1000000000000 : ℝ) (992015579087/1000000000000 : ℝ) (992015579089/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 1 (62002965911/62500000000 : ℝ) (992047454577/1000000000000 : ℝ) (992015579087/1000000000000 : ℝ) (992015579089/1000000000000 : ℝ) (992031516831/1000000000000 : ℝ) (992031516833/1000000000000 : ℝ) (992031516703/1000000000000 : ℝ) (198406303341/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 2 (992031516831/1000000000000 : ℝ) (992031516833/1000000000000 : ℝ) (992031516703/1000000000000 : ℝ) (198406303341/200000000000 : ℝ) (992031516767/1000000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 3 (992031516767/1000000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 4 (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 5 (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 6 (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67247/524288 : ℝ)) 7 (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67247/524288 : ℝ))) (177643490669/1000000000000 : ℝ) (7105739627/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177643490669/1000000000000 : ℝ) (7105739627/40000000000 : ℝ) (294410872667/500000000000 : ℝ) (294410872669/500000000000 : ℝ) (8429554927/20000000000 : ℝ) (210738873179/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 1 (294410872667/500000000000 : ℝ) (294410872669/500000000000 : ℝ) (8429554927/20000000000 : ℝ) (210738873179/500000000000 : ℝ) (252574872921/500000000000 : ℝ) (63143718231/125000000000 : ℝ) (9963438407/20000000000 : ℝ) (498171920357/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 2 (252574872921/500000000000 : ℝ) (63143718231/125000000000 : ℝ) (9963438407/20000000000 : ℝ) (498171920357/1000000000000 : ℝ) (62707604137/125000000000 : ℝ) (501660833103/1000000000000 : ℝ) (7838260949/15625000000 : ℝ) (501648700743/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 3 (62707604137/125000000000 : ℝ) (501660833103/1000000000000 : ℝ) (7838260949/15625000000 : ℝ) (501648700743/1000000000000 : ℝ) (125413691729/250000000000 : ℝ) (501654766923/1000000000000 : ℝ) (501654766879/1000000000000 : ℝ) (501654766887/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 4 (125413691729/250000000000 : ℝ) (501654766923/1000000000000 : ℝ) (501654766879/1000000000000 : ℝ) (501654766887/1000000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 5 (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 6 (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67247/524288 : ℝ))) 7 (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67247/524288 : ℝ)) hmem 8 (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67247/524288 : ℝ))) hcmem 8 (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67247/524288 : ℝ)) (496015758383/500000000000 : ℝ) (992031516769/1000000000000 : ℝ) (501654766897/1000000000000 : ℝ) (100330953381/200000000000 : ℝ) (397163523457/500000000000 : ℝ) (79432704693/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1174_exp_lower
  have heNumeric : (128431467741/62500000000 : ℝ)/4 ≤ Real.exp (-8525638153829/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431467741/62500000000 : ℝ)/4 ≤ Real.exp ((33623/262144 : ℝ)-(79432704693/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33623/262144 : ℝ) (67247/524288 : ℝ) (79432704693/100000000000 : ℝ) (128431467741/62500000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1150_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1150_certificate
#check SmaleRate.Proofs.cover8_leaf1151_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1151_certificate
#check SmaleRate.Proofs.cover8_leaf1152_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1152_certificate
#check SmaleRate.Proofs.cover8_leaf1153_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1153_certificate
#check SmaleRate.Proofs.cover8_leaf1154_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1154_certificate
#check SmaleRate.Proofs.cover8_leaf1155_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1155_certificate
#check SmaleRate.Proofs.cover8_leaf1156_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1156_certificate
#check SmaleRate.Proofs.cover8_leaf1157_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1157_certificate
#check SmaleRate.Proofs.cover8_leaf1158_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1158_certificate
#check SmaleRate.Proofs.cover8_leaf1159_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1159_certificate
#check SmaleRate.Proofs.cover8_leaf1160_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1160_certificate
#check SmaleRate.Proofs.cover8_leaf1161_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1161_certificate
#check SmaleRate.Proofs.cover8_leaf1162_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1162_certificate
#check SmaleRate.Proofs.cover8_leaf1163_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1163_certificate
#check SmaleRate.Proofs.cover8_leaf1164_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1164_certificate
#check SmaleRate.Proofs.cover8_leaf1165_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1165_certificate
#check SmaleRate.Proofs.cover8_leaf1166_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1166_certificate
#check SmaleRate.Proofs.cover8_leaf1167_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1167_certificate
#check SmaleRate.Proofs.cover8_leaf1168_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1168_certificate
#check SmaleRate.Proofs.cover8_leaf1169_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1169_certificate
#check SmaleRate.Proofs.cover8_leaf1170_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1170_certificate
#check SmaleRate.Proofs.cover8_leaf1171_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1171_certificate
#check SmaleRate.Proofs.cover8_leaf1172_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1172_certificate
#check SmaleRate.Proofs.cover8_leaf1173_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1173_certificate
#check SmaleRate.Proofs.cover8_leaf1174_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1174_certificate
