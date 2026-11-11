module

public import DirectedDistances.PaperProofs.Section4.SelectedCutFiltrationCore
public import DirectedDistances.PaperProofs.Section4.RenewalBlockSegments
public import DirectedDistances.PaperProofs.Section4.RenewalIIDBlockProducts
import DirectedDistances.KMSW.XDPAdditivityAtCuts

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open MeasureTheory Quiver
open scoped Classical ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0
local notation "Block" => (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)

private theorem time_nat_strictMono (T : ℕ → Ω → ℕ∞) (p : Ω)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hf : ∀ m, T m p < ⊤) : StrictMono (fun m => (T m p).toNat) := by
  intro a b hab
  have h := positiveSuccessTime_strictMono_of_finite T p hT hab (hf a).ne (hf b).ne
  have ha := ENat.natCast_toNat (hf a).ne
  have hb := ENat.natCast_toNat (hf b).ne
  rw [← ha, ← hb] at h
  exact ENat.natCast_lt_natCast.mp h

private theorem time_success (T : ℕ → Ω → ℕ∞) (p : Ω)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hf : ∀ m, T m p < ⊤) (m : ℕ) (hm : 0 < m) :
    literalSuccessGraph p (T m p).toNat := by
  have hg : IsPositiveSuccessTime (literalSuccessGraph p) m ((T m p).toNat : ℕ∞) := by
    rw [ENat.natCast_toNat (hf m).ne]
    exact hT m
  exact ((isPositiveSuccessTime_natCast_iff _ hm _).mp hg).2.1




theorem selectorRenewalBlock_prefix_sums_ae
    (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂μ,
      let Z := fun i => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)
      (∀ m, (T m p).toNat = ∑ i ∈ Finset.range m, (Z i).1) ∧
      (∀ m, p (T m p).toNat =
        ∑ i ∈ Finset.range m, (Z i).2 (Fin.last (Z i).1)) ∧
      (∀ i, ((Z i).2 (Fin.last (Z i).1)).2 ≤ -1) := by
  have hf : ∀ᵐ p ∂μ, ∀ m, T m p < ⊤ :=
    ae_all_iff.mpr (selectorRenewalTime_finite_ae T hT)
  filter_upwards [hf, selectorRenewalBlock_iterate_eq_segment_ae T hT,
    conditionedVectorPathLaw_ae_legal] with p hf hseg hl
  dsimp only
  let Z := fun i => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)
  have hm := time_nat_strictMono T p (hT p) hf
  have hlen (i : ℕ) : (Z i).1 = (T (i + 1) p).toNat - (T i p).toNat := by
    exact congrArg Sigma.fst (hseg i)
  have hend (i : ℕ) : (Z i).2 (Fin.last (Z i).1) =
      p (T (i + 1) p).toNat - p (T i p).toNat := by
    dsimp only [Z]
    rw [hseg i]
    dsimp only [Fin.val_last]
    rw [Nat.add_sub_of_le (hm.monotone (Nat.le_succ i))]
  refine ⟨?_, ?_, ?_⟩
  · intro m
    induction m with
    | zero => rw [selectorRenewalTime_zero T hT p]; rfl
    | succ m ih =>
        rw [Finset.sum_range_succ, ← ih, hlen]
        exact (Nat.add_sub_of_le (hm.monotone (Nat.le_succ m))).symm
  · intro m
    induction m with
    | zero =>
        rw [selectorRenewalTime_zero T hT p]
        exact hl.1
    | succ m ih =>
        rw [Finset.sum_range_succ, ← ih, hend, add_sub_cancel]
  · intro i
    rw [hend]
    have hs := time_success T p (hT p) hf (i + 1) (by omega)
    have h := hs.1 (T i p).toNat (hm (Nat.lt_succ_self i))
    change (p (T (i + 1) p).toNat).2 - (p (T i p).toNat).2 ≤ -1
    omega

private theorem hit_eq_nat_iff (r n : ℕ) (p : Ω) :
    conditionedSecondCoordinateFirstHit r p = (n : ℕ∞) ↔
      (p n).2 = -(r : ℤ) ∧ ∀ i < n, (p i).2 ≠ -(r : ℤ) := by
  unfold conditionedSecondCoordinateFirstHit
  by_cases h : ∃ i, (p i).2 = -(r : ℤ)
  · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dite_eq_right h]
    constructor
    · exact fun he => (ENat.top_ne_natCast n he).elim
    · exact fun hn => (h ⟨n, hn.1⟩).elim

private theorem exists_level_hit (p : Ω) (r n : ℕ)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0) (hn : (p n).2 ≤ -(r : ℤ)) :
    ∃ j ≤ n, (p j).2 = -(r : ℤ) := by
  induction n with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ n ih =>
      by_cases hprev : (p n).2 ≤ -(r : ℤ)
      · obtain ⟨j, hj, hh⟩ := ih hprev
        exact ⟨j, by omega, hh⟩
      · exact ⟨n + 1, le_rfl, by have := hstep n; omega⟩

private theorem rank_time_iff_level (T : ℕ → Ω → ℕ∞) (p : Ω)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hf : ∀ m, T m p < ⊤) (hl : p 0 = (0, 0) ∧
      ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (k : ℕ) (hk : conditionedSecondCoordinateFirstHit (k + 1) p < ⊤) (m : ℕ) :
    T m p ≤ conditionedSecondCoordinateFirstHit (k + 1) p ↔
      -((k + 1 : ℕ) : ℤ) ≤ (p (T m p).toNat).2 := by
  let t := (T m p).toNat
  let N := (conditionedSecondCoordinateFirstHit (k + 1) p).toNat
  have ht : T m p = (t : ℕ∞) := (ENat.natCast_toNat (hf m).ne).symm
  have hN : conditionedSecondCoordinateFirstHit (k + 1) p = (N : ℕ∞) :=
    (ENat.natCast_toNat hk.ne).symm
  have hh := (hit_eq_nat_iff (k + 1) N p).mp hN
  have hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2 := by
    intro j
    obtain ⟨c, hc⟩ := hl.2 j
    have hs := congrArg Prod.snd hc
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  simp only [ht, hN, ENat.toNat_natCast, ENat.natCast_le_natCast]
  constructor
  · intro hle
    by_contra hn
    obtain ⟨j, hj, he⟩ := exists_level_hit p (k + 1) t hstep (congrArg Prod.snd hl.1)
      (by omega)
    have hjN : N ≤ j := by
      by_contra h
      exact hh.2 j (by omega) he
    have hje : j = N := by omega
    subst j
    have hte : t = N := by omega
    rw [hte, hh.1] at hn
    exact hn le_rfl
  · intro hlevel
    by_contra hle
    have hmpos : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      have hz : T 0 p = 0 := (isPositiveSuccessTime_zero_iff _ _).mp (hT 0)
      have ht0 : t = 0 := by simp only [t, hm0, hz, ENat.toNat_zero]
      omega
    have hs := time_success T p hT hf m hmpos
    have hb := hs.1 N (by omega)
    change (p t).2 ≤ (p N).2 - 1 at hb
    rw [hh.1] at hb
    omega





theorem selectedCutBlock_time_endpoint_rank_ae
    (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂μ, ∀ k : ℕ,
      let Z := fun i => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)
      let m := selectedCutRank T (k + 1) p
      selectedCutTime T (k + 1) p = T m p ∧
      (selectedCutTime T (k + 1) p).toNat = ∑ i ∈ Finset.range m, (Z i).1 ∧
      p (selectedCutTime T (k + 1) p).toNat =
        ∑ i ∈ Finset.range m, (Z i).2 (Fin.last (Z i).1) ∧
      -((k + 1 : ℕ) : ℤ) ≤
        ∑ i ∈ Finset.range m, ((Z i).2 (Fin.last (Z i).1)).2 ∧
      ∀ n, -((k + 1 : ℕ) : ℤ) ≤
        ∑ i ∈ Finset.range n, ((Z i).2 (Fin.last (Z i).1)).2 → n ≤ m := by
  have hf : ∀ᵐ p ∂μ, ∀ m, T m p < ⊤ :=
    ae_all_iff.mpr (selectorRenewalTime_finite_ae T hT)
  have hh : ∀ᵐ p ∂μ, ∀ k, conditionedSecondCoordinateFirstHit (k + 1) p < ⊤ :=
    ae_all_iff.mpr fun k => firstHitPastMap_finite_hit_ae (k + 1) (by omega)
  filter_upwards [hf, hh, selectorRenewalBlock_prefix_sums_ae T hT,
    conditionedVectorPathLaw_ae_legal] with p hf hh hs hl
  intro k
  dsimp only
  let m := selectedCutRank T (k + 1) p
  have hzero : T 0 p = 0 := selectorRenewalTime_zero T hT p
  have hm : T m p ≤ conditionedSecondCoordinateFirstHit (k + 1) p := by
    apply Nat.findGreatest_spec (m := 0)
      (P := fun n => T n p ≤ conditionedSecondCoordinateFirstHit (k + 1) p)
    · exact Nat.zero_le _
    · rw [hzero]
      exact bot_le
  have hsel : selectedCutTime T (k + 1) p = T m p := by
    rw [selectedCutTime, dite_eq_left (hh k)]
  have hend (n : ℕ) : (p (T n p).toNat).2 =
      ∑ i ∈ Finset.range n,
        ((selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)).2
          (Fin.last (selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)).1)).2 := by
    rw [hs.2.1 n, Prod.snd_sum]
  refine ⟨hsel, hsel ▸ hs.1 m, hsel ▸ hs.2.1 m, ?_, ?_⟩
  · rw [← hend m]
    exact (rank_time_iff_level T p (hT p) hf hl k (hh k) m).mp hm
  · intro n hn
    rw [← hend n] at hn
    have hle := (rank_time_iff_level T p (hT p) hf hl k (hh k) n).mpr hn
    apply Nat.le_findGreatest
      (positiveSuccessTime_le_index T p (hT p) n
        (conditionedSecondCoordinateFirstHit (k + 1) p).toNat (by
          rw [ENat.natCast_toNat (hh k).ne]
          exact hle)) hle

private noncomputable def stageDistance (x : XDP) (w : ℕ → Fin 3) (n : ℕ) : ℕ :=
  match x with
  | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 id
      (ldpSup (⟨0⟩ : StagePresentVertex w n) ⟨(recordVertex w n).id⟩)
  | .sdp => (sdp (⟨0⟩ : StagePresentVertex w n) ⟨(recordVertex w n).id⟩).toNat

private def blockCodes (z : Block) (i : ℕ) : Fin 3 :=
  pathCode (fun j => z.2 ⟨min j z.1, by omega⟩) (i + 1)






@[expose] noncomputable def blockDist (x : XDP) (z : Block) : ℕ :=
  let w := fun i => pathCode (fun j => z.2 ⟨min j z.1, by omega⟩) (i + 1)
  match x with
  | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 id
      (ldpSup (⟨0⟩ : StagePresentVertex w z.1) ⟨(recordVertex w z.1).id⟩)
  | .sdp => (sdp (⟨0⟩ : StagePresentVertex w z.1) ⟨(recordVertex w z.1).id⟩).toNat




theorem measurable_blockDist (x : XDP) : Measurable (blockDist x) := by
  let : MeasurableSingletonClass Block := ⟨fun z => by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro n
    change MeasurableSet (Sigma.mk n ⁻¹' {z})
    exact (Set.to_countable _).measurableSet⟩
  exact measurable_of_countable _

private def stageCongrMap {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w' n) where
  obj v := ⟨v.id⟩
  map {_ _} e := ⟨e.val, by simpa only [h] using e.property⟩

private theorem stageCongrMap_length {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) {a b : StagePresentVertex w n}
    (p : Path a b) : ((stageCongrMap h).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem stageDistance_congr (x : XDP) {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) : stageDistance x w n = stageDistance x w' n := by
  have hid : (recordVertex w n).id = (recordVertex w' n).id :=
    congrArg (fun s : State => s.west s.active) h
  have hsets (a b : ℕ) : pathLengths (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      pathLengths (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
    ext k
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(stageCongrMap h).mapPath p, stageCongrMap_length h p⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(stageCongrMap h.symm).mapPath p, stageCongrMap_length h.symm p⟩
  cases x with
  | ldp =>
      dsimp only [stageDistance, ldpSup]
      rw [hid, hsets]
  | sdp =>
      apply congrArg ENat.toNat
      rw [hid]
      apply le_antisymm
      · apply le_iInf
        intro p
        exact (sdp_le_length ((stageCongrMap h.symm).mapPath p)).trans_eq
          (congrArg (fun k : ℕ => (k : ℕ∞)) (stageCongrMap_length h.symm p))
      · apply le_iInf
        intro p
        exact (sdp_le_length ((stageCongrMap h).mapPath p)).trans_eq
          (congrArg (fun k : ℕ => (k : ℕ∞)) (stageCongrMap_length h p))

private theorem blockDist_segment (x : XDP) (p : Ω) (a n : ℕ) :
    blockDist x (⟨n, fun i => p (a + i.val) - p a⟩ : Block) =
      stageDistance x (fun i => boltzmannKMSWStream (pathCode p) (a + i)) n := by
  change stageDistance x (blockCodes _) n = _
  apply stageDistance_congr x
  apply kmswStage_congr
  intro i hi
  change pathCode (fun j => p (a + (min j n)) - p a) (i + 1) =
    pathCode p (a + i + 1)
  have hi1 : min (i + 1) n = i + 1 := min_eq_left (by omega)
  have hi0 : min i n = i := min_eq_left (by omega)
  simp only [pathCode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, hi1, hi0, sub_sub_sub_cancel_right]
  rw [Nat.add_assoc]

private noncomputable def recordDistance (x : XDP) (w : ℕ → Fin 3)
    (a b : ℕ) : ℕ :=
  match x with
  | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
      (presentLdp (recordVertex w a) (recordVertex w b))
  | .sdp => (sdp (recordVertex w a) (recordVertex w b)).toNat

private theorem recordDistance_self (x : XDP) (w : ℕ → Fin 3) (a : ℕ) :
    recordDistance x w a a = 0 := by
  have hp : IsLongest (Path.nil : Path (recordVertex w a) (recordVertex w a)) :=
    fun q => Nat.le_of_eq (presentVertex_acyclic w _ q)
  cases x with
  | ldp =>
      dsimp only [recordDistance]
      rw [presentLdp_eq_length hp]
      rfl
  | sdp =>
      dsimp only [recordDistance]
      rw [sdp_self]
      rfl

private theorem recordDistance_segment (x : XDP) (p : Ω) (a n : ℕ)
    (hrec : ∀ i < a, R (boltzmannKMSWStream (pathCode p)) a ≤
      R (boltzmannKMSWStream (pathCode p)) i - 1) :
    recordDistance x (boltzmannKMSWStream (pathCode p)) a (a + n) =
      blockDist x (⟨n, fun i => p (a + i.val) - p a⟩ : Block) := by
  rw [blockDist_segment]
  have hs := recordSegment_distances_eq_shift_stage
    (boltzmannKMSWStream (pathCode p)) a n hrec
  cases x with
  | ldp =>
      dsimp only [recordDistance, stageDistance]
      rw [hs.1]
      generalize ldpSup (⟨0⟩ : StagePresentVertex
        (fun i => boltzmannKMSWStream (pathCode p) (a + i)) n)
          ⟨(recordVertex (fun i => boltzmannKMSWStream (pathCode p) (a + i)) n).id⟩ = d
      cases d <;> rfl
  | sdp =>
      exact congrArg ENat.toNat hs.2

private theorem recordDistance_add (x : XDP) (w : ℕ → Fin 3) (a b : ℕ) (hab : a ≤ b)
    (hAa : ∀ i < a, R w a ≤ R w i - 1) (hBa : ∀ i ≥ a, L w a ≤ L w i)
    (hAb : ∀ i < b, R w b ≤ R w i - 1) (hBb : ∀ i ≥ b, L w b ≤ L w i) :
    recordDistance x w 0 b = recordDistance x w 0 a + recordDistance x w a b := by
  obtain ⟨p, q, _, _, hp, hq⟩ := recordVertex_distances_attained w hab hAa hAb hBb
  obtain ⟨p0, q0, _, _, hp0, hq0⟩ :=
    recordVertex_distances_attained w (Nat.zero_le a) (by simp) hAa hBa
  have hadd := recordVertex_distances_eq_add w (a := 0) (Nat.zero_le a) hab hAa hBa hAb
  cases x with
  | ldp =>
      dsimp only [recordDistance]
      rw [hadd.1, hp0, hp, ← WithBot.coe_add, ← ENat.natCast_add]
      simp only [WithBot.recBotCoe_coe, ENat.toNat_natCast]
  | sdp =>
      dsimp only [recordDistance]
      rw [hadd.2, hq0, hq, ← ENat.natCast_add]
      simp only [ENat.toNat_natCast]

private theorem record_firstHit (p : Ω) (t : ℕ) (ht : (p t).2 ≤ 0)
    (hrec : ∀ i < t, (p t).2 ≤ (p i).2 - 1) :
    conditionedSecondCoordinateFirstHit (-(p t).2).toNat p = (t : ℕ∞) := by
  have hr : -(((-(p t).2).toNat : ℕ) : ℤ) = (p t).2 := by omega
  apply (hit_eq_nat_iff _ t p).mpr
  refine ⟨hr.symm, fun i hi => ?_⟩
  have h := hrec i hi
  omega

private theorem selected_distance_eq_record (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (hf : ∀ m, T m q.1 < ⊤) (k : ℕ) :
    (selectedCutCodeDistanceConditioning x T (k + 1) q.1).2 =
      recordDistance x (boltzmannKMSWStream (pathCode q.1)) 0
        (T (selectedCutRank T (k + 1) q.1) q.1).toNat := by
  obtain ⟨_, hl, hh, _, hwp, _, _, _, hL, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let p := q.1
  let m := selectedCutRank T (k + 1) p
  let t := (T m p).toNat
  let w := boltzmannKMSWStream (pathCode p)
  have h0 : p 0 = (0, 0) := hl.1
  have hwp' : integrateCodes w = p := hwp
  have hL' : ∀ n, 0 ≤ L w n := hL
  have hsel : selectedCutTime T (k + 1) p = T m p := by
    rw [selectedCutTime, dite_eq_left (hh (k + 1))]
  have hs : literalSuccessGraph p t := by
    by_cases hm : m = 0
    · have ht : t = 0 := by rw [show t = (T m p).toNat from rfl, hm,
        selectorRenewalTime_zero T hT p]; rfl
      change (∀ i < t, (p t).2 ≤ (p i).2 - 1) ∧ ∀ i ≥ t, (p t).1 ≤ (p i).1
      rw [ht, h0]
      refine ⟨fun i hi => by omega, fun i _ => ?_⟩
      simpa only [kmsw_L_eq, hwp'] using hL' i
    · exact time_success T p (hT p) hf m (by omega)
  have hneg : (p t).2 ≤ 0 := by
    by_cases ht : t = 0
    · rw [ht, h0]
    · have h := hs.1 0 (Nat.pos_of_ne_zero ht)
      rw [h0] at h
      change (p t).2 ≤ 0 - 1 at h
      omega
  have hhit := record_firstHit p t hneg hs.1
  change (if hr : 1 ≤ (-(selectedCutFuture T (k + 1) p 0).2).toNat then
    firstHitCodeXdpDistance x (-(selectedCutFuture T (k + 1) p 0).2).toNat p else 0) = _
  have hF : selectedCutFuture T (k + 1) p 0 = p t := by
    simp only [selectedCutFuture, hsel, conditionedVectorShift, Nat.add_zero]
    rfl
  rw [hF]
  by_cases hr : 1 ≤ (-(p t).2).toNat
  · rw [dite_eq_left hr]
    simp only [firstHitCodeXdpDistance, hhit, ENat.toNat_natCast]
    cases x <;> rfl
  · rw [dite_eq_right hr]
    have ht : t = 0 := by
      by_contra ht
      have h := hs.1 0 (Nat.pos_of_ne_zero ht)
      rw [h0] at h
      change (p t).2 ≤ 0 - 1 at h
      omega
    change 0 = recordDistance x w 0 t
    rw [ht, recordDistance_self]





theorem selectedCutBlock_distance_sum_ae
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂μ, ∀ k : ℕ,
      (selectedCutCodeDistanceConditioning x T (k + 1) p).2 =
        ∑ i ∈ Finset.range (selectedCutRank T (k + 1) p),
          blockDist x (selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)) := by
  have hf : ∀ᵐ p ∂μ, ∀ m, T m p < ⊤ :=
    ae_all_iff.mpr (selectorRenewalTime_finite_ae T hT)
  have hQ : ∀ᵐ p ∂μ, p ∈ selectedCutCoherentDomain x T hT :=
    ae_iff.mpr (selectedCutCoherentDomain_measurable_conull x T hT).2
  filter_upwards [hf, hQ, selectorRenewalBlock_iterate_eq_segment_ae T hT]
    with p hf hQ hseg
  let q : selectedCutCoherentDomain x T hT := ⟨p, hQ⟩
  obtain ⟨_, hl, _, _, hwp, _, _, _, hL, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let w := boltzmannKMSWStream (pathCode p)
  have h0 : p 0 = (0, 0) := hl.1
  have hwp' : integrateCodes w = p := hwp
  have hL' : ∀ n, 0 ≤ L w n := hL
  let t := fun m => (T m p).toNat
  have hm : StrictMono t := time_nat_strictMono T p (hT p) hf
  have hz : t 0 = 0 := by rw [show t 0 = (T 0 p).toNat from rfl,
    selectorRenewalTime_zero T hT p]; rfl
  have hs (m : ℕ) : literalSuccessGraph p (t m) := by
    by_cases hm : m = 0
    · subst m
      change (∀ i < t 0, (p (t 0)).2 ≤ (p i).2 - 1) ∧
        ∀ i ≥ t 0, (p (t 0)).1 ≤ (p i).1
      rw [hz, h0]
      refine ⟨fun i hi => by omega, fun i _ => ?_⟩
      simpa only [kmsw_L_eq, hwp'] using hL' i
    · exact time_success T p (hT p) hf m (by omega)
  have hA (m : ℕ) : ∀ i < t m, R w (t m) ≤ R w i - 1 := by
    simpa only [kmsw_R_eq, hwp'] using (hs m).1
  have hB (m : ℕ) : ∀ i ≥ t m, L w (t m) ≤ L w i := by
    simpa only [kmsw_L_eq, hwp'] using (hs m).2
  have hd (m : ℕ) : recordDistance x w (t m) (t (m + 1)) =
      blockDist x (selectorRenewalBlock T ((selectorRenewalFuture T)^[m] p)) := by
    rw [hseg m]
    have he : t (m + 1) = t m + (t (m + 1) - t m) :=
      (Nat.add_sub_of_le (hm.monotone (Nat.le_succ m))).symm
    conv_lhs => rw [he]
    exact recordDistance_segment x p (t m) (t (m + 1) - t m) (hA m)
  have hsum (m : ℕ) : recordDistance x w 0 (t m) =
      ∑ i ∈ Finset.range m,
        blockDist x (selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)) := by
    induction m with
    | zero => rw [hz, recordDistance_self]; rfl
    | succ m ih =>
        rw [Finset.sum_range_succ,
          recordDistance_add x w (t m) (t (m + 1)) (hm.monotone (Nat.le_succ m))
            (hA m) (hB m) (hA (m + 1)) (hB (m + 1)), ih, hd]
  intro k
  exact (selected_distance_eq_record x T hT q hf k).trans (hsum _)






@[expose] noncomputable def concatenateRenewalBlocks (z : ℕ → Block) (n : ℕ) : ℤ × ℤ :=
  let j := Nat.findGreatest (fun j => ∑ i ∈ Finset.range j, (z i).1 ≤ n) n
  (∑ i ∈ Finset.range j, (z i).2 (Fin.last (z i).1)) +
    (z j).2 ⟨min (n - ∑ i ∈ Finset.range j, (z i).1) (z j).1, by omega⟩

private theorem concatenateRenewalBlocks_shift
    (T : ℕ → Ω → ℕ∞) (p : Ω)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hf : ∀ m, T m p < ⊤)
    (hseg : ∀ j, selectorRenewalBlock T ((selectorRenewalFuture T)^[j] p) =
      (⟨(T (j + 1) p).toNat - (T j p).toNat,
        fun i => p ((T j p).toNat + i.val) - p (T j p).toNat⟩ : Block))
    (m n : ℕ) :
    concatenateRenewalBlocks
        (fun j => selectorRenewalBlock T ((selectorRenewalFuture T)^[m + j] p)) n =
      p ((T m p).toNat + n) - p (T m p).toNat := by
  let Z := fun i => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)
  let t := fun i => (T i p).toNat
  let l := fun j => ∑ i ∈ Finset.range j, (Z (m + i)).1
  let e := fun j => ∑ i ∈ Finset.range j, (Z (m + i)).2 (Fin.last (Z (m + i)).1)
  have hm : StrictMono t := time_nat_strictMono T p hT hf
  have hlen (i : ℕ) : (Z i).1 = t (i + 1) - t i :=
    congrArg Sigma.fst (hseg i)
  have hend (i : ℕ) : (Z i).2 (Fin.last (Z i).1) = p (t (i + 1)) - p (t i) := by
    dsimp only [Z]
    rw [hseg i]
    dsimp only [Fin.val_last]
    rw [Nat.add_sub_of_le (hm.monotone (Nat.le_succ i))]
  have hlength (j : ℕ) : l j = t (m + j) - t m := by
    induction j with
    | zero => simp only [l, Finset.range_zero, Finset.sum_empty, Nat.add_zero, Nat.sub_self]
    | succ j ih =>
        change (∑ i ∈ Finset.range (j + 1), (Z (m + i)).1) = _
        rw [Finset.sum_range_succ, show (∑ i ∈ Finset.range j, (Z (m + i)).1) =
          t (m + j) - t m from ih, hlen]
        have ha := hm.monotone (show m ≤ m + j by omega)
        have hb : t (m + j) ≤ t (m + (j + 1)) := hm.monotone (by omega)
        simp only [Nat.add_assoc]
        omega
  have hendpoint (j : ℕ) : e j = p (t (m + j)) - p (t m) := by
    induction j with
    | zero => simp only [e, Finset.range_zero, Finset.sum_empty, Nat.add_zero, sub_self]
    | succ j ih =>
        change (∑ i ∈ Finset.range (j + 1), (Z (m + i)).2
          (Fin.last (Z (m + i)).1)) = _
        rw [Finset.sum_range_succ, show (∑ i ∈ Finset.range j, (Z (m + i)).2
          (Fin.last (Z (m + i)).1)) = p (t (m + j)) - p (t m) from ih, hend]
        simp only [Nat.add_assoc]
        abel
  have hbound (j : ℕ) : j ≤ l j := by
    rw [hlength]
    have h := hm.add_le_nat j m
    rw [Nat.add_comm j m] at h
    omega
  let j := Nat.findGreatest (fun j => l j ≤ n) n
  have hlo : l j ≤ n := Nat.findGreatest_spec
    (P := fun j => l j ≤ n) (n := n) (m := 0) (Nat.zero_le n)
    (by change (0 : ℕ) ≤ n; exact Nat.zero_le n)
  have hhi : n < l (j + 1) := by
    by_contra h
    have hjn : j + 1 ≤ n := (hbound (j + 1)).trans (by omega)
    exact Nat.findGreatest_is_greatest (show j < j + 1 by omega) hjn (by omega)
  have hjlen : (Z (m + j)).1 = t (m + (j + 1)) - t (m + j) := by
    rw [hlen, Nat.add_assoc]
  have hmin : min (n - l j) (Z (m + j)).1 = n - l j := by
    apply min_eq_left
    rw [hjlen]
    rw [hlength] at hlo hhi ⊢
    have ha := hm.monotone (show m ≤ m + j by omega)
    omega
  have hindex : t (m + j) + (n - l j) = t m + n := by
    rw [hlength] at hlo ⊢
    have ha := hm.monotone (show m ≤ m + j by omega)
    omega
  change e j + (Z (m + j)).2 ⟨min (n - l j) (Z (m + j)).1, by omega⟩ = _
  have hvalue : ∀ i : Fin ((Z (m + j)).1 + 1),
      (Z (m + j)).2 i = p (t (m + j) + i.val) - p (t (m + j)) := by
    dsimp only [Z]
    rw [hseg (m + j)]
    intro i
    rfl
  rw [hendpoint, hvalue]
  change (p (t (m + j)) - p (t m)) +
    (p (t (m + j) + min (n - l j) (Z (m + j)).1) - p (t (m + j))) = _
  rw [hmin, hindex]
  abel





theorem selectedCutFuture_block_tail_ae
    (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂μ, ∀ k : ℕ,
      let Z := fun i => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)
      let m := selectedCutRank T (k + 1) p
      selectedCutFuture T (k + 1) p = fun n =>
        (∑ i ∈ Finset.range m, (Z i).2 (Fin.last (Z i).1)) +
          concatenateRenewalBlocks (fun j => Z (m + j)) n := by
  have hf : ∀ᵐ p ∂μ, ∀ m, T m p < ⊤ :=
    ae_all_iff.mpr (selectorRenewalTime_finite_ae T hT)
  filter_upwards [hf, selectorRenewalBlock_iterate_eq_segment_ae T hT,
    selectedCutBlock_time_endpoint_rank_ae T hT] with p hf hseg hcut
  intro k
  dsimp only
  funext n
  rw [concatenateRenewalBlocks_shift T p (hT p) hf hseg]
  rw [← (hcut k).2.2.1]
  change p ((selectedCutTime T (k + 1) p).toNat + n) = _
  rw [(hcut k).1]
  rw [add_sub_cancel]

end DirectedDistances.PaperProofs.Section4
