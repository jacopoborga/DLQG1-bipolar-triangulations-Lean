module

public import DirectedDistances.PaperProofs.Section4.SelectedCutCodeDistanceLaw
public import DirectedDistances.PaperProofs.Section4.FirstHitCodeDistanceMeasurable
public import DirectedDistances.KMSW.PathSpaceTransfer
import DirectedDistances.KMSW.XDPAdditivityAtCuts
import DirectedDistances.PaperProofs.Section4.FirstHitGeodesicPiece
import DirectedDistances.RandomWalk.RenewalSuccessShift

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open MeasureTheory Quiver
open scoped Classical ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0




@[expose] noncomputable def selectedCutConditioningVersion
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (j : ℕ) : Ω → Ω × ℕ :=
  (aemeasurable_selectedCutCodeDistanceConditioning x T (j + 1) hT).mk
    (selectedCutCodeDistanceConditioning x T (j + 1))




theorem selectedCutConditioningVersion_measurable_ae_eq
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) (j : ℕ) :
    Measurable (selectedCutConditioningVersion x T hT j) ∧
      selectedCutConditioningVersion x T hT j =ᵐ[μ]
        selectedCutCodeDistanceConditioning x T (j + 1) :=
  ⟨(aemeasurable_selectedCutCodeDistanceConditioning x T (j + 1) hT).measurable_mk,
    (aemeasurable_selectedCutCodeDistanceConditioning x T (j + 1) hT).ae_eq_mk.symm⟩




@[expose] def selectedCutCoherentProperty (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (p : Ω) : Prop :=
  (∀ j, selectedCutConditioningVersion x T hT j p =
    selectedCutCodeDistanceConditioning x T (j + 1) p) ∧
  (p 0 = (0, 0) ∧ ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) ∧
  (∀ r, conditionedSecondCoordinateFirstHit r p < ⊤) ∧
  (∀ r (hr : 1 ≤ r), firstHitCodeXdpDistance x r p =
    firstHitPastXdpLength x r (stoppedMap r hr (pathCode p))) ∧
  (let w := boltzmannKMSWStream (pathCode p)
   integrateCodes w = p ∧
   ∃ hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
       ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite,
     Filter.Tendsto (L w) Filter.atTop Filter.atTop ∧
     (∀ a : ℤ, ∃ n, R w n ≤ a) ∧ (∀ n, 0 ≤ L w n) ∧
     {v : ℕ | mapCutVertex w hfin v}.Infinite ∧
     ∀ n, (mapCutVertex w hfin (activeInitial w n) ∧
       ∀ i < n, activeInitial w i ≠ activeInitial w n) ↔
       ((∀ i < n, (p n).2 ≤ (p i).2 - 1) ∧
         ∀ i ≥ n, (p n).1 ≤ (p i).1))

private theorem selectedCutCoherentProperty_ae (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂μ, selectedCutCoherentProperty x T hT p := by
  have hversions : ∀ᵐ p ∂μ, ∀ j,
      selectedCutConditioningVersion x T hT j p =
        selectedCutCodeDistanceConditioning x T (j + 1) p :=
    ae_all_iff.mpr fun j =>
      (aemeasurable_selectedCutCodeDistanceConditioning x T (j + 1) hT).ae_eq_mk.symm
  have hfinite : ∀ᵐ p ∂μ, ∀ r, 1 ≤ r →
      conditionedSecondCoordinateFirstHit r p < ⊤ :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun hr => firstHitPastMap_finite_hit_ae r hr
  have hdist : ∀ᵐ p ∂μ, ∀ r (hr : 1 ≤ r), firstHitCodeXdpDistance x r p =
      firstHitPastXdpLength x r (stoppedMap r hr (pathCode p)) :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun hr =>
      firstHitCodeXdpDistance_ae_eq_pastLength x r hr
  filter_upwards [hversions, conditionedVectorPathLaw_ae_legal, hfinite, hdist,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit]
    with p hv hl hf hd hg
  have hfall : ∀ r, conditionedSecondCoordinateFirstHit r p < ⊤ := by
    intro r
    by_cases hr : 1 ≤ r
    · exact hf r hr
    · have hr0 : r = 0 := by omega
      subst r
      have hex : ∃ n, (p n).2 = -((0 : ℕ) : ℤ) := ⟨0, by rw [hl.1]; rfl⟩
      rw [conditionedSecondCoordinateFirstHit, dite_eq_left hex]
      exact ENat.natCast_lt_top _
  have hwp := (firstHit_stoppedCode_conventions 1 p hl.1 hl.2 (hfall 1)).2.1
  obtain ⟨w, hw, hfin, htrans, hR, hL, hinf, hchar⟩ := hg
  have heq := integrateCodes_injective (hw.trans hwp.symm)
  subst w
  exact ⟨hv, hl, hfall, hd, hwp, hfin, htrans, hR, hL, hinf, hchar⟩





@[expose] noncomputable def selectedCutCoherentDomain
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) : Set Ω :=
  (toMeasurable μ {p | ¬ selectedCutCoherentProperty x T hT p})ᶜ




theorem selectedCutCoherentDomain_measurable_conull
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    MeasurableSet (selectedCutCoherentDomain x T hT) ∧
      μ (selectedCutCoherentDomain x T hT)ᶜ = 0 := by
  refine ⟨(measurableSet_toMeasurable _ _).compl, ?_⟩
  rw [selectedCutCoherentDomain, compl_compl, measure_toMeasurable]
  exact ae_iff.mp (selectedCutCoherentProperty_ae x T hT)




theorem selectedCutCoherentDomain_spec
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) :
    (∀ j, selectedCutConditioningVersion x T hT j q.1 =
      selectedCutCodeDistanceConditioning x T (j + 1) q.1) ∧
    (q.1 0 = (0, 0) ∧ ∀ n,
      q.1 (n + 1) - q.1 n ∈ Set.range lazyTwoDimensionalStep) ∧
    (∀ r, conditionedSecondCoordinateFirstHit r q.1 < ⊤) ∧
    (∀ r (hr : 1 ≤ r), firstHitCodeXdpDistance x r q.1 =
      firstHitPastXdpLength x r (stoppedMap r hr (pathCode q.1))) ∧
  (let w := boltzmannKMSWStream (pathCode q.1)
   integrateCodes w = q.1 ∧
   ∃ hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
       ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite,
     Filter.Tendsto (L w) Filter.atTop Filter.atTop ∧
     (∀ a : ℤ, ∃ n, R w n ≤ a) ∧ (∀ n, 0 ≤ L w n) ∧
     {v : ℕ | mapCutVertex w hfin v}.Infinite ∧
     ∀ n, (mapCutVertex w hfin (activeInitial w n) ∧
       ∀ i < n, activeInitial w i ≠ activeInitial w n) ↔
       ((∀ i < n, (q.1 n).2 ≤ (q.1 i).2 - 1) ∧
         ∀ i ≥ n, (q.1 n).1 ≤ (q.1 i).1)) := by
  by_contra h
  exact q.2 (subset_toMeasurable μ {p | ¬ selectedCutCoherentProperty x T hT p} h)




noncomputable abbrev selectedCutConditioningSigma
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (j : ℕ) : MeasurableSpace (selectedCutCoherentDomain x T hT) :=
  MeasurableSpace.comap
    (fun q : selectedCutCoherentDomain x T hT => selectedCutConditioningVersion x T hT j q.1)
    inferInstance




theorem selectedCutConditioningSigma_eq
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) (j : ℕ) :
    selectedCutConditioningSigma x T hT j = MeasurableSpace.comap
      (fun q : selectedCutCoherentDomain x T hT =>
        selectedCutCodeDistanceConditioning x T (j + 1) q.1) inferInstance ∧
    Measurable (fun q : selectedCutCoherentDomain x T hT =>
      selectedCutCodeDistanceConditioning x T (j + 1) q.1) := by
  have heq : (fun q : selectedCutCoherentDomain x T hT =>
      selectedCutConditioningVersion x T hT j q.1) =
      (fun q : selectedCutCoherentDomain x T hT =>
        selectedCutCodeDistanceConditioning x T (j + 1) q.1) := by
    funext q
    exact (selectedCutCoherentDomain_spec x T hT q).1 j
  constructor
  · exact congrArg (fun f => MeasurableSpace.comap f inferInstance) heq
  · rw [← heq]
    exact (aemeasurable_selectedCutCodeDistanceConditioning x T (j + 1) hT).measurable_mk.comp
      measurable_subtype_coe

private theorem success_has_selector_rank
    (T : ℕ → Ω → ℕ∞) (p : Ω)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (n : ℕ) (hn : 0 < n) (hs : literalSuccessGraph p n) :
    ∃ m, 0 < m ∧ T m p = (n : ℕ∞) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let m := positiveSuccessCount (literalSuccessGraph p) (a + 1)
  have hm : 0 < m := by
    dsimp [m]
    rw [positiveSuccessCount_succ, ite_eq_left hs]
    omega
  have hg : IsPositiveSuccessTime (literalSuccessGraph p) m ((a + 1 : ℕ) : ℕ∞) :=
    (isPositiveSuccessTime_natCast_iff _ hm _).mpr ⟨by omega, hs, rfl⟩
  obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (literalSuccessGraph p) m
  exact ⟨m, hm, (hu _ (hT m)).trans (hu _ hg).symm⟩

private theorem selectedCutTime_nat_characterization
    (T : ℕ → Ω → ℕ∞) (p : Ω) (k : ℕ)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hfinite : conditionedSecondCoordinateFirstHit k p < ⊤) :
    (selectedCutTime T k p).toNat ≤ (conditionedSecondCoordinateFirstHit k p).toNat ∧
    ((selectedCutTime T k p).toNat ≠ 0 →
      literalSuccessGraph p (selectedCutTime T k p).toNat) ∧
    (∀ n, n ≤ (conditionedSecondCoordinateFirstHit k p).toNat →
      literalSuccessGraph p n → n ≤ (selectedCutTime T k p).toNat) := by
  classical
  let K := (conditionedSecondCoordinateFirstHit k p).toNat
  let rank := selectedCutRank T k p
  have hτK : conditionedSecondCoordinateFirstHit k p = (K : ℕ∞) :=
    (ENat.natCast_toNat hfinite.ne).symm
  have hzero : T 0 p = 0 := (isPositiveSuccessTime_zero_iff _ _).mp (hT 0)
  have hrank : T rank p ≤ conditionedSecondCoordinateFirstHit k p := by
    dsimp [rank, selectedCutRank]
    apply Nat.findGreatest_spec (m := 0)
      (P := fun m => T m p ≤ conditionedSecondCoordinateFirstHit k p)
    · exact Nat.zero_le _
    · rw [hzero]
      exact bot_le
  have hsel : selectedCutTime T k p = T rank p := by
    rw [selectedCutTime, dite_eq_left hfinite]
  have hsle : selectedCutTime T k p ≤ conditionedSecondCoordinateFirstHit k p :=
    hsel ▸ hrank
  have hsfin : selectedCutTime T k p < ⊤ := hsle.trans_lt hfinite
  have hscast : selectedCutTime T k p = ((selectedCutTime T k p).toNat : ℕ∞) :=
    (ENat.natCast_toNat hsfin.ne).symm
  refine ⟨ENat.toNat_le_toNat hsle hfinite.ne, ?_, ?_⟩
  · intro hnonzero
    have hrpos : 0 < rank := by
      by_contra h
      have hr0 : rank = 0 := by omega
      have hs0 : selectedCutTime T k p = 0 := by rw [hsel, hr0, hzero]
      exact hnonzero (by rw [hs0]; rfl)
    have hg : IsPositiveSuccessTime (literalSuccessGraph p) rank
        ((selectedCutTime T k p).toNat : ℕ∞) := by
      rw [← hscast, hsel]
      exact hT rank
    exact ((isPositiveSuccessTime_natCast_iff _ hrpos _).mp hg).2.1
  · intro n hn hs
    by_cases hn0 : n = 0
    · subst n
      exact Nat.zero_le _
    obtain ⟨m, _, hmn⟩ := success_has_selector_rank T p hT n (by omega) hs
    have hmK : m ≤ K := positiveSuccessTime_le_index T p hT m K (by
      rw [hmn]
      exact ENat.natCast_le_natCast.mpr hn)
    have hmrank : m ≤ rank := by
      dsimp [rank, selectedCutRank]
      apply Nat.le_findGreatest hmK
      rw [hmn, hτK]
      exact ENat.natCast_le_natCast.mpr hn
    have hord : T m p ≤ T rank p := by
      rcases hmrank.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (positiveSuccessTime_strictMono_of_finite T p hT hlt
          (by rw [hmn]; exact ENat.natCast_ne_top n)
          (ne_of_lt (hrank.trans_lt hfinite))).le
    have hns : (n : ℕ∞) ≤ selectedCutTime T k p := by
      rw [← hmn, hsel]
      exact hord
    simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hns hsfin.ne

private theorem hit_eq_nat_iff (r n : ℕ) (p : Ω) :
    conditionedSecondCoordinateFirstHit r p = (n : ℕ∞) ↔
      (p n).2 = -(r : ℤ) ∧ ∀ i < n, (p i).2 ≠ -(r : ℤ) := by
  classical
  unfold conditionedSecondCoordinateFirstHit
  by_cases h : ∃ i, (p i).2 = -(r : ℤ)
  · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dite_eq_right h]
    constructor
    · exact fun he => (ENat.top_ne_natCast n he).elim
    · exact fun hn => (h ⟨n, hn.1⟩).elim

private theorem record_firstHit (p : Ω) (t : ℕ) (ht : (p t).2 ≤ 0)
    (hrec : ∀ i < t, (p t).2 ≤ (p i).2 - 1) :
    conditionedSecondCoordinateFirstHit (-(p t).2).toNat p = (t : ℕ∞) := by
  have hr : -(((-(p t).2).toNat : ℕ) : ℤ) = (p t).2 := by omega
  apply (hit_eq_nat_iff _ t p).mpr
  refine ⟨hr.symm, fun i hi => ?_⟩
  have h := hrec i hi
  omega

private noncomputable def recordCodeDistance (x : XDP) (w : ℕ → Fin 3)
    (m n : ℕ) : ℕ :=
  match x with
  | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
      (presentLdp (recordVertex w m) (recordVertex w n))
  | .sdp => (sdp (recordVertex w m) (recordVertex w n)).toNat

private theorem recordCodeDistance_self (x : XDP) (w : ℕ → Fin 3) (m : ℕ) :
    recordCodeDistance x w m m = 0 := by
  have hp : IsLongest (Path.nil : Path (recordVertex w m) (recordVertex w m)) :=
    fun q => Nat.le_of_eq (presentVertex_acyclic w _ q)
  cases x with
  | ldp =>
    dsimp only [recordCodeDistance]
    rw [presentLdp_eq_length hp]
    rfl
  | sdp =>
    dsimp only [recordCodeDistance]
    rw [sdp_self]
    rfl

private theorem selectedCut_record_data
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k : ℕ) :
    let p := q.1
    let t := (selectedCutTime T k p).toNat
    let w := boltzmannKMSWStream (pathCode p)
    literalSuccessGraph p t ∧ (p t).2 ≤ 0 ∧
      (selectedCutCodeDistanceConditioning x T k p).2 = recordCodeDistance x w 0 t := by
  classical
  obtain ⟨_, hl, hf, _, hwp, hfin, htrans, hR, hL, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  dsimp only
  let p := q.1
  let t := (selectedCutTime T k p).toNat
  let w := boltzmannKMSWStream (pathCode p)
  have h0 : p 0 = (0, 0) := hl.1
  have hs := (selectedCutTime_nat_characterization T p k (hT p) (hf k)).2.1
  have hsuccess : literalSuccessGraph p t := by
    by_cases ht : t = 0
    · change (∀ i < t, (p t).2 ≤ (p i).2 - 1) ∧
        ∀ i ≥ t, (p t).1 ≤ (p i).1
      rw [ht, h0]
      refine ⟨fun i hi => by omega, fun i _ => ?_⟩
      have hi := hL i
      simpa only [kmsw_L_eq, hwp] using hi
    · exact hs ht
  have hneg : (p t).2 ≤ 0 := by
    by_cases ht : t = 0
    · rw [ht, h0]
    · have h := hsuccess.1 0 (Nat.pos_of_ne_zero ht)
      rw [h0] at h
      change (p t).2 ≤ 0 - 1 at h
      omega
  refine ⟨hsuccess, hneg, ?_⟩
  have hhit := record_firstHit p t hneg hsuccess.1
  change (if hr : 1 ≤ (-(p t).2).toNat then
    firstHitCodeXdpDistance x (-(p t).2).toNat p else 0) =
      recordCodeDistance x w 0 t
  by_cases hr : 1 ≤ (-(p t).2).toNat
  · rw [dite_eq_left hr]
    simp only [firstHitCodeXdpDistance, hhit, ENat.toNat_natCast]
    cases x <;> rfl
  · rw [dite_eq_right hr]
    have ht : t = 0 := by
      by_contra ht
      have h := hsuccess.1 0 (Nat.pos_of_ne_zero ht)
      rw [h0] at h
      change (p t).2 ≤ 0 - 1 at h
      omega
    rw [ht, recordCodeDistance_self]

private theorem hit_shift_of_le (p : Ω) (r t : ℕ)
    (hf : conditionedSecondCoordinateFirstHit r p < ⊤)
    (ht : t ≤ (conditionedSecondCoordinateFirstHit r p).toNat) :
    (conditionedSecondCoordinateFirstHit r (conditionedVectorShift t p)).toNat =
      (conditionedSecondCoordinateFirstHit r p).toNat - t := by
  let N := (conditionedSecondCoordinateFirstHit r p).toNat
  have he : conditionedSecondCoordinateFirstHit r p = (N : ℕ∞) :=
    (ENat.natCast_toNat hf.ne).symm
  have hs := (hit_eq_nat_iff r N p).mp he
  have hshift : conditionedSecondCoordinateFirstHit r (conditionedVectorShift t p) =
      ((N - t : ℕ) : ℕ∞) := by
    apply (hit_eq_nat_iff r (N - t) _).mpr
    constructor
    · change (p (t + (N - t))).2 = _
      rw [Nat.add_sub_of_le ht]
      exact hs.1
    · intro i hi
      change (p (t + i)).2 ≠ _
      exact hs.2 _ (by omega)
  rw [hshift]
  rfl

private theorem centered_success_iff (p : Ω) (k : ℕ) :
    literalSuccessGraph (fun i => p i - p 0) k ↔ literalSuccessGraph p k := by
  constructor
  · rintro ⟨hr, hl⟩
    constructor
    · intro i hi
      have h := hr i hi
      change (p k).2 - (p 0).2 ≤ (p i).2 - (p 0).2 - 1 at h
      omega
    · intro i hi
      have h := hl i hi
      change (p k).1 - (p 0).1 ≤ (p i).1 - (p 0).1 at h
      omega
  · rintro ⟨hr, hl⟩
    constructor
    · intro i hi
      have h := hr i hi
      change (p k).2 - (p 0).2 ≤ (p i).2 - (p 0).2 - 1
      omega
    · intro i hi
      have h := hl i hi
      change (p k).1 - (p 0).1 ≤ (p i).1 - (p 0).1
      omega

private theorem uncentered_success_shift_iff (p : Ω) (t k : ℕ)
    (ht : ∀ i < t, (p t).2 ≤ (p i).2 - 1) (hk : 0 < k) :
    literalSuccessGraph p (t + k) ↔
      literalSuccessGraph (conditionedVectorShift t p) k := by
  exact (renewal_success_add_iff_pathShift p t k ht hk).trans
    (centered_success_iff (conditionedVectorShift t p) k)

private noncomputable def futureOffset (r : ℕ) (p : Ω) : ℕ := by
  classical
  exact Nat.findGreatest (literalSuccessGraph p)
    (conditionedSecondCoordinateFirstHit r p).toNat

private theorem measurable_futureOffset (r : ℕ) : Measurable (futureOffset r) := by
  classical
  have hh : Measurable (conditionedSecondCoordinateFirstHit r) := by
    apply ENat.measurable_iff.mpr
    intro n
    obtain ⟨S, hS, heq⟩ := MeasurableSpace.measurableSet_comap.mp
      (measurableSet_conditionedVectorPast_firstHit_eq r n)
    change MeasurableSet {p | conditionedSecondCoordinateFirstHit r p = (n : ℕ∞)}
    rw [← heq]
    exact hS.preimage (measurable_conditionedVectorPrefix n)
  have hn : Measurable (fun p => (conditionedSecondCoordinateFirstHit r p).toNat) :=
    (measurable_of_countable ENat.toNat).comp hh
  have hmax : Measurable (fun z : Ω × ℕ =>
      Nat.findGreatest (literalSuccessGraph z.1) z.2) :=
    measurable_from_prod_countable_left fun n =>
      measurable_findGreatest fun k _ => measurableSet_renewal_success k
  exact hmax.comp (measurable_id.prodMk hn)




theorem selectedCutTime_future_recovery
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (j J : ℕ) (hjJ : j < J) :
    ∃ o : Ω → ℕ, Measurable o ∧ ∀ q : selectedCutCoherentDomain x T hT,
      (selectedCutTime T (J + 1) q.1).toNat =
        (selectedCutTime T (j + 1) q.1).toNat + o (selectedCutFuture T (j + 1) q.1) ∧
      selectedCutFuture T (J + 1) q.1 =
        conditionedVectorShift (o (selectedCutFuture T (j + 1) q.1))
          (selectedCutFuture T (j + 1) q.1) := by
  classical
  refine ⟨futureOffset (J + 1), measurable_futureOffset (J + 1), ?_⟩
  intro q
  obtain ⟨_, hlegal, hfinite, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let p := q.1
  let t := (selectedCutTime T (j + 1) p).toNat
  let b := (selectedCutTime T (J + 1) p).toNat
  let N := (conditionedSecondCoordinateFirstHit (J + 1) p).toNat
  have hstep : ∀ i, (p i).2 - 1 ≤ (p (i + 1)).2 := by
    intro i
    obtain ⟨c, hc⟩ := hlegal.2 i
    change lazyTwoDimensionalStep c = p (i + 1) - p i at hc
    have hs := congrArg Prod.snd hc
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
  have hτj : conditionedSecondCoordinateFirstHit (j + 1) p =
      ((conditionedSecondCoordinateFirstHit (j + 1) p).toNat : ℕ∞) :=
    (ENat.natCast_toNat (hfinite (j + 1)).ne).symm
  have hτmono : conditionedSecondCoordinateFirstHit (j + 1) p ≤
      conditionedSecondCoordinateFirstHit (J + 1) p := by
    rw [conditionedSecondCoordinateFirstHit_shift_add p (j + 1) (J + 1)
      _ hstep h0 hτj (by omega)]
    rw [hτj]
    exact le_self_add
  obtain ⟨htτ, hts, htmax⟩ :=
    selectedCutTime_nat_characterization T p (j + 1) (hT p) (hfinite (j + 1))
  obtain ⟨hbτ, hbs, hbmax⟩ :=
    selectedCutTime_nat_characterization T p (J + 1) (hT p) (hfinite (J + 1))
  have htN : t ≤ N := htτ.trans
    (ENat.toNat_le_toNat hτmono (hfinite (J + 1)).ne)
  have htb : t ≤ b := by
    by_cases ht0 : t = 0
    · rw [ht0]
      exact Nat.zero_le _
    · exact hbmax t htN (hts ht0)
  have hrecord : ∀ i < t, (p t).2 ≤ (p i).2 - 1 := by
    by_cases ht0 : t = 0
    · intro i hi
      omega
    · exact (hts ht0).1
  have hhit : (conditionedSecondCoordinateFirstHit (J + 1)
      (selectedCutFuture T (j + 1) p)).toNat = N - t :=
    hit_shift_of_le p (J + 1) t (hfinite (J + 1)) htN
  have hoff : futureOffset (J + 1) (selectedCutFuture T (j + 1) p) = b - t := by
    unfold futureOffset
    rw [hhit, Nat.findGreatest_eq_iff]
    refine ⟨by omega, ?_, ?_⟩
    · intro hne
      have hb : b ≠ 0 := by omega
      have hs := (uncentered_success_shift_iff p t (b - t) hrecord (by omega)).mp
        (by rw [Nat.add_sub_of_le htb]; exact hbs hb)
      exact hs
    · intro n hbn hn hsuccess
      have hnpos : 0 < n := by omega
      have hs := (uncentered_success_shift_iff p t n hrecord hnpos).mpr hsuccess
      have hbound := hbmax (t + n) (by omega) hs
      omega
  have heq : b = t + futureOffset (J + 1) (selectedCutFuture T (j + 1) p) := by
    rw [hoff, Nat.add_sub_of_le htb]
  refine ⟨heq, ?_⟩
  funext n
  change p (b + n) = p (t + (futureOffset (J + 1)
    (selectedCutFuture T (j + 1) p) + n))
  rw [heq, Nat.add_assoc]

private theorem shifted_stream (p : Ω) (a : ℕ) :
    boltzmannKMSWStream (pathCode (conditionedVectorShift a p)) =
      fun i => boltzmannKMSWStream (pathCode p) (a + i) := by
  funext i
  change pathCode (conditionedVectorShift a p) (i + 1) = pathCode p (a + i + 1)
  simp only [pathCode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, conditionedVectorShift]
  rw [Nat.add_assoc]

private theorem recordCodeDistance_shift (x : XDP) (w : ℕ → Fin 3) (a n : ℕ)
    (hrec : ∀ i < a, R w a ≤ R w i - 1) :
    recordCodeDistance x w a (a + n) =
      recordCodeDistance x (fun i => w (a + i)) 0 n := by
  have hseg := recordSegment_distances_eq_shift_stage w a n hrec
  have hstage := presentDistances_to_record_eq_stage (fun i => w (a + i)) n ⟨0⟩
  cases x with
  | ldp =>
    dsimp only [recordCodeDistance]
    rw [recordVertex_zero_eq_source, hseg.1, hstage.1]
  | sdp =>
    dsimp only [recordCodeDistance]
    rw [recordVertex_zero_eq_source, hseg.2, hstage.2]

private theorem recordCodeDistance_add
    (x : XDP) (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ z : ℤ, ∃ n, R w n ≤ z) (hL : ∀ n, 0 ≤ L w n)
    (a b : ℕ) (hab : a ≤ b)
    (hAa : ∀ i < a, R w a ≤ R w i - 1)
    (hBa : ∀ i ≥ a, L w a ≤ L w i)
    (hAb : ∀ i < b, R w b ≤ R w i - 1)
    (hBb : ∀ i ≥ b, L w b ≤ L w i) :
    recordCodeDistance x w 0 b =
      recordCodeDistance x w 0 a + recordCodeDistance x w a b := by
  obtain ⟨p, q, _, _, hp, hq⟩ :=
    recordVertex_distances_attained w hab hAa hAb hBb
  obtain ⟨p0, q0, _, _, hp0, hq0⟩ :=
    recordVertex_distances_attained w (Nat.zero_le a) (by simp) hAa hBa
  have hcut := record_mapCutVertex_of_barrier w hfin hL htrans hR a hAa hBa
  have hsep : ∀ r : Path (⟨0⟩ : PresentVertex w) (recordVertex w b),
      recordVertex w a ∈ r.vertices := by
    intro r
    exact mapCutVertex_separates_reachable w hfin hL htrans hR hcut
      (recordVertex w b) ⟨p⟩ r
  have hadd := mapCutVertex_distances_eq_add w hfin htrans hR hL hcut
    (recordVertex w b) hsep
  have haddL : presentLdp (recordVertex w 0) (recordVertex w b) =
      presentLdp (recordVertex w 0) (recordVertex w a) +
        presentLdp (recordVertex w a) (recordVertex w b) := by
    simpa only [recordVertex_zero_eq_source] using hadd.2.2.1
  have haddS : sdp (recordVertex w 0) (recordVertex w b) =
      sdp (recordVertex w 0) (recordVertex w a) +
        sdp (recordVertex w a) (recordVertex w b) := by
    simpa only [recordVertex_zero_eq_source] using hadd.2.2.2
  cases x with
  | ldp =>
    dsimp only [recordCodeDistance]
    rw [haddL, hp0, hp, ← WithBot.coe_add, ← ENat.natCast_add]
    simp only [WithBot.recBotCoe_coe, ENat.toNat_natCast]
  | sdp =>
    dsimp only [recordCodeDistance]
    rw [haddS, hq0, hq, ← ENat.natCast_add]
    simp only [ENat.toNat_natCast]

private noncomputable def futureSegment (x : XDP) (o : Ω → ℕ) (p : Ω) : ℕ :=
  firstHitCodeXdpDistance x (-(p (o p)).2).toNat p

private theorem measurable_variable_firstHit (x : XDP) :
    Measurable (fun z : Ω × ℕ => firstHitCodeXdpDistance x z.2 z.1) := by
  exact measurable_from_prod_countable_left
    (f := fun z : Ω × ℕ => firstHitCodeXdpDistance x z.2 z.1)
    (fun r => measurable_firstHitCodeXdpDistance x r)

private theorem measurable_futureSegment (x : XDP) (o : Ω → ℕ) (ho : Measurable o) :
    Measurable (futureSegment x o) := by
  change Measurable (fun p : Ω => firstHitCodeXdpDistance x (-(p (o p)).2).toNat p)
  have heval : Measurable (fun z : Ω × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left (f := fun z : Ω × ℕ => z.1 z.2)
      (fun n => measurable_pi_apply n)
  have hr : Measurable (fun p : Ω => (-(p (o p)).2).toNat) :=
    (measurable_of_countable (fun z : ℤ × ℤ => (-z.2).toNat)).comp
      (heval.comp (measurable_id.prodMk ho))
  have hpair : Measurable (fun p : Ω => (p, (-(p (o p)).2).toNat)) :=
    measurable_id.prodMk hr
  exact Measurable.comp
    (g := fun z : Ω × ℕ => firstHitCodeXdpDistance x z.2 z.1)
    (f := fun p : Ω => (p, (-(p (o p)).2).toNat))
    (measurable_variable_firstHit x) hpair




theorem selectedCutCodeDistance_future_recovery
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (j J : ℕ) (hjJ : j < J) :
    ∃ d : Ω → ℕ, Measurable d ∧ ∀ q : selectedCutCoherentDomain x T hT,
      (selectedCutCodeDistanceConditioning x T (J + 1) q.1).2 =
        (selectedCutCodeDistanceConditioning x T (j + 1) q.1).2 +
          d (selectedCutFuture T (j + 1) q.1) := by
  obtain ⟨o, ho, hrecover⟩ := selectedCutTime_future_recovery x T hT j J hjJ
  refine ⟨futureSegment x o, measurable_futureSegment x o ho, ?_⟩
  intro q
  obtain ⟨_, _, _, _, hwp, hfin, htrans, hR, hL, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  let p := q.1
  let w := boltzmannKMSWStream (pathCode p)
  let a := (selectedCutTime T (j + 1) p).toNat
  let b := (selectedCutTime T (J + 1) p).toNat
  let F := selectedCutFuture T (j + 1) p
  let n := o F
  have htime : b = a + n := (hrecover q).1
  have hwp' : integrateCodes w = p := hwp
  obtain ⟨hsa, _, hda⟩ := selectedCut_record_data x T hT q (j + 1)
  obtain ⟨hsb, hnb, hdb⟩ := selectedCut_record_data x T hT q (J + 1)
  change literalSuccessGraph p a at hsa
  change literalSuccessGraph p b at hsb
  have hAa : ∀ i < a, R w a ≤ R w i - 1 := by
    simpa only [kmsw_R_eq, hwp'] using hsa.1
  have hBa : ∀ i ≥ a, L w a ≤ L w i := by
    simpa only [kmsw_L_eq, hwp'] using hsa.2
  have hAb : ∀ i < b, R w b ≤ R w i - 1 := by
    simpa only [kmsw_R_eq, hwp'] using hsb.1
  have hBb : ∀ i ≥ b, L w b ≤ L w i := by
    simpa only [kmsw_L_eq, hwp'] using hsb.2
  have hrecF : ∀ i < n, (F n).2 ≤ (F i).2 - 1 := by
    intro i hi
    change (p (a + n)).2 ≤ (p (a + i)).2 - 1
    rw [← htime]
    exact hsb.1 (a + i) (by omega)
  have hnegF : (F n).2 ≤ 0 := by
    change (p (a + n)).2 ≤ 0
    rw [← htime]
    exact hnb
  have hhit := record_firstHit F n hnegF hrecF
  have hstream : boltzmannKMSWStream (pathCode F) = fun i => w (a + i) :=
    shifted_stream p a
  have hdF : futureSegment x o F = recordCodeDistance x w a b := by
    rw [htime, recordCodeDistance_shift x w a n hAa]
    unfold futureSegment
    change firstHitCodeXdpDistance x (-(F n).2).toNat F = _
    simp only [firstHitCodeXdpDistance, hhit, ENat.toNat_natCast]
    rw [hstream]
    cases x <;> rfl
  rw [hdb, hda, hdF]
  exact recordCodeDistance_add x w hfin htrans hR hL a b (by omega) hAa hBa hAb hBb




theorem selectedCutConditioningVersion_recovery
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (j J : ℕ) (hjJ : j < J) :
    ∃ R : Ω × ℕ → Ω × ℕ, Measurable R ∧
      ∀ q : selectedCutCoherentDomain x T hT,
        selectedCutConditioningVersion x T hT J q.1 =
          R (selectedCutConditioningVersion x T hT j q.1) := by
  obtain ⟨o, ho, htime⟩ := selectedCutTime_future_recovery x T hT j J hjJ
  obtain ⟨d, hd, hdist⟩ := selectedCutCodeDistance_future_recovery x T hT j J hjJ
  let R : Ω × ℕ → Ω × ℕ := fun z =>
    (conditionedVectorShift (o z.1) z.1, z.2 + d z.1)
  have hshift : Measurable (fun z : Ω × ℕ => conditionedVectorShift z.2 z.1) :=
    measurable_from_prod_countable_left fun n => measurable_conditionedVectorShift n
  refine ⟨R, ?_, ?_⟩
  · exact (hshift.comp ((measurable_fst).prodMk (ho.comp measurable_fst))).prodMk
      (measurable_snd.add (hd.comp measurable_fst))
  · intro q
    have hv := (selectedCutCoherentDomain_spec x T hT q).1
    rw [hv J, hv j]
    apply Prod.ext
    · exact (htime q).2
    · exact hdist q




theorem selectedCutConditioningSigma_antitone
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Antitone (selectedCutConditioningSigma x T hT) := by
  intro j J hjJ
  rcases hjJ.eq_or_lt with rfl | hjJ
  · exact le_rfl
  · obtain ⟨R, hR, heq⟩ := selectedCutConditioningVersion_recovery x T hT j J hjJ
    exact MeasurableSpace.comap_le_comap_of_eq_comp R hR (funext heq)

end DirectedDistances.PaperProofs.Section4
