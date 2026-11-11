module

public import DirectedDistances.PaperProofs.Section4.FinitePastIndependenceFirstHitKernel
public import DirectedDistances.KMSW.StageDirectedMapPathLengths
public import DirectedDistances.KMSW.XDPStageIdentificationAtCuts
import DirectedDistances.KMSW.PathSpaceTransfer

/-! τ_r the past map XDP length equals the code-graph XDP distance from the source to
the cut vertex; the renewal-time selection T_{m_k} and the infinite source-map
(F4c) identification are not treated; not the paper result.

The path decoder has a dummy coordinate at zero. The KMSW stream is therefore
`fun i => pathCode p (i + 1)`. For r ≥ 1 the stopped word is the shifted prefix of
length τ − 1, excluding the hit-time down-step; for r = 0, τ = 0 and the word is empty.
Its map is stage `τ_r - 1`, with sink the active edge's head.
No identification with the graph of the unshifted dummy-containing stream is used. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory Quiver

private def stageCongr (w w' : ℕ → Fin 3) (n : ℕ)
    (h : kmswStage w n = kmswStage w' n) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w' n) where
  obj v := ⟨v.id⟩
  map e := ⟨e.val, by simpa only [h] using e.property⟩

private theorem stageCongr_length (w w' : ℕ → Fin 3) (n : ℕ)
    (h : kmswStage w n = kmswStage w' n) {a b : StagePresentVertex w n}
    (p : Path a b) : ((stageCongr w w' n h).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem stageCongr_ldp (w w' : ℕ → Fin 3) (n a b : ℕ)
    (h : kmswStage w n = kmswStage w' n) :
    ldpSup (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      ldpSup (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
  have hp : pathLengths (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      pathLengths (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
    ext k
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(stageCongr w w' n h).mapPath p, stageCongr_length w w' n h p⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(stageCongr w' w n h.symm).mapPath p,
        stageCongr_length w' w n h.symm p⟩
  unfold ldpSup
  rw [hp]

private theorem stageCongr_sdp_le (w w' : ℕ → Fin 3) (n a b : ℕ)
    (h : kmswStage w n = kmswStage w' n) :
    sdp (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ ≤
      sdp (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ := by
  apply le_iInf
  intro p
  have hp := sdp_le_length ((stageCongr w w' n h).mapPath p)
  rwa [stageCongr_length] at hp

/-- hit τ_r the past map XDP length equals the code-graph XDP distance from the source
to the cut vertex; the renewal-time selection T_{m_k} and the infinite source-map
(F4c) identification are not treated; not the paper result. This stage formula
uses the shifted stream; for r ≥ 1 the stopped word excludes the hit-time down-step. -/
theorem firstHitPastXdpLength_eq_shifted_stage (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    (firstHitPastXdpLength .ldp r (stoppedMap r hr ω) : WithBot ℕ) =
        ldpSup (⟨0⟩ : StagePresentVertex w (t - 1))
          ⟨(kmswStage w (t - 1)).east (kmswStage w (t - 1)).active⟩ ∧
      (firstHitPastXdpLength .sdp r (stoppedMap r hr ω) : ℕ∞) =
        sdp (⟨0⟩ : StagePresentVertex w (t - 1))
          ⟨(kmswStage w (t - 1)).east (kmswStage w (t - 1)).active⟩ := by
  classical
  dsimp only
  let t := boltzmannTau r ω
  let w := boltzmannKMSWStream ω
  have ht : 1 ≤ t := (boltzmann_boundary_observable r hr ω hE).1
  let c : KMSWWalkClass (L w t).toNat r t :=
    ⟨stoppedWord r ω, (stoppedWord_admissible r hr ω hE).1⟩
  let j : StoppedWalkIndex r := ⟨t, ⟨(L w t).toNat, c⟩⟩
  have hidx : stoppedIndex r hr ω = some j := by
    simp only [stoppedIndex, dite_eq_left hE, j, t, w, c]
  have hmap : stoppedMap r hr ω = some (stoppedWalkMap ⟨j, ht⟩) := by
    rw [stoppedMap, hidx]
    change stoppedWalkMapOption r j = _
    exact dite_eq_left (show 1 ≤ j.1 from ht)
  have hlen (x : XDP) : firstHitPastXdpLength x r (stoppedMap r hr ω) =
      xdpLengthBase (kmswWalkClassRep ht c).B x := by
    rw [hmap]
    rfl
  have hs : kmswStage (codeExtend c) (t - 1) = kmswStage w (t - 1) :=
    stoppedStage_eq_of_stoppedWord_eq r ω c rfl
  have hb : (kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active =
      (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := by rw [hs]
  constructor
  · rw [hlen .ldp]
    change (ldpLengthBase (kmswWalkClassRep ht c).B : WithBot ℕ) = _
    rw [kmswWalkClassRep_ldpLength_eq_stage, hb]
    exact stageCongr_ldp _ _ _ _ _ hs
  · rw [hlen .sdp]
    change (sdpLengthBase (kmswWalkClassRep ht c).B : ℕ∞) = _
    rw [kmswWalkClassRep_sdpLength_eq_stage, hb]
    exact le_antisymm (stageCongr_sdp_le _ _ _ _ _ hs.symm)
      (stageCongr_sdp_le _ _ _ _ _ hs)

private theorem pathCode_walk_eq (p : ℕ → ℤ × ℤ) (h0 : p 0 = (0, 0))
    (hp : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) :
    codeWalk (pathCode p) = p := by
  funext n
  rw [codeWalk_pathCode p hp n, h0]
  exact sub_zero _

/-- hit τ_r the past map XDP length equals the code-graph XDP distance from the source
to the cut vertex; the renewal-time selection T_{m_k} and the infinite source-map
(F4c) identification are not treated; not the paper result. These conventions
record the one-place shift and the finite-time conversion; for r ≥ 1 the stopped word is
the shifted prefix of length τ − 1, excluding the hit-time down-step; for r = 0, τ = 0
and the word is empty. -/
theorem firstHit_stoppedCode_conventions (r : ℕ) (p : ℕ → ℤ × ℤ)
    (h0 : p 0 = (0, 0))
    (hp : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hfin : conditionedSecondCoordinateFirstHit r p < ⊤) :
    boltzmannKMSWStream (pathCode p) = (fun i => pathCode p (i + 1)) ∧
      integrateCodes (boltzmannKMSWStream (pathCode p)) = p ∧
      boltzmannTau r (pathCode p) = (conditionedSecondCoordinateFirstHit r p).toNat ∧
      conditionedSecondCoordinateFirstHit r p =
        (boltzmannTau r (pathCode p) : ℕ∞) ∧
      ∀ i : Fin (boltzmannTau r (pathCode p) - 1),
        stoppedWord r (pathCode p) i = pathCode p (i.val + 1) := by
  classical
  have hw := pathCode_walk_eq p h0 hp
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hh
    simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hh, lt_self_iff_false]
      at hfin
  have ht : boltzmannTau r (pathCode p) = Nat.find hh := by
    simp only [boltzmannTau, hw, dite_eq_left hh]
  refine ⟨rfl, pathCode_walk_eq p h0 hp, ?_, ?_, fun _ => rfl⟩
  · simp only [ht, conditionedSecondCoordinateFirstHit, dite_eq_left hh, ENat.toNat_natCast]
  · simp only [ht, conditionedSecondCoordinateFirstHit, dite_eq_left hh]

private theorem pathCode_event (r : ℕ) (p : ℕ → ℤ × ℤ)
    (h0 : p 0 = (0, 0))
    (hp : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hL : ∀ n, 0 ≤ (p n).1)
    (hfin : conditionedSecondCoordinateFirstHit r p < ⊤) :
    pathCode p ∈ boltzmannEvent r := by
  classical
  have hw := pathCode_walk_eq p h0 hp
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hh
    simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hh, lt_self_iff_false]
      at hfin
  obtain ⟨n, hn⟩ := hh
  exact ⟨n, by rwa [hw], fun j _ => by rw [hw]; exact hL j⟩

/-- hit τ_r the past map XDP length equals the code-graph XDP distance from the source
to the cut vertex; the renewal-time selection T_{m_k} and the infinite source-map
(F4c) identification are not treated; not the paper result. The sink is the next
active edge's tail, at a strict vertical record of the shifted stream. -/
theorem firstHitPast_sink_eq_record_and_strict (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    (recordVertex w t).id =
        (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active ∧
      ∀ j < t, R w t ≤ R w j - 1 := by
  dsimp only
  let t := boltzmannTau r ω
  let w := boltzmannKMSWStream ω
  have hobs := boltzmann_boundary_observable r hr ω hE
  have ht : 1 ≤ t := hobs.1
  have hlast : w (t - 1) = 2 := by
    change ω (t - 1 + 1) = 2
    rw [Nat.sub_add_cancel ht]
    exact hobs.2.1
  have hUR : (kmswStage w (t - 1)).UR = [] :=
    (stoppedStage_mem_sourceClass r hr ω hE).1.1
  have htn : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := by
    obtain ⟨n, hn, _⟩ := hE
    exact ⟨n, hn⟩
  have htime : t = Nat.find hhit := by
    simp only [t, boltzmannTau, dite_eq_left hhit]
  have hno (j : ℕ) (hj : j < t) : (codeWalk ω j).2 ≠ -(r : ℤ) := by
    apply Nat.find_min hhit
    rwa [← htime]
  have hbefore (j : ℕ) (hj : j < t) : -(r : ℤ) < (codeWalk ω j).2 := by
    induction j with
    | zero => rw [codeWalk_zero]; dsimp; omega
    | succ j ih =>
      have hprev := ih (by omega)
      have hs := congrArg Prod.snd (codeWalk_succ_sub ω j)
      have hlo : -1 ≤ (lazyTwoDimensionalStep (ω (j + 1))).2 := by
        generalize ω (j + 1) = c
        fin_cases c <;> norm_num [lazyTwoDimensionalStep]
      have hn := hno (j + 1) hj
      simp only [Prod.snd_sub] at hs
      omega
  constructor
  · change (kmswStage w t).west (kmswStage w t).active = _
    conv_lhs => rw [← htn, kmswStage, kmswStep, hlast]
    simp only [kmswCodeStep, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, kmswStepOfStep, hUR,
      State.addEdge]
    rfl
  · intro j hj
    have heq (k : ℕ) : R w k = (codeWalk ω k).2 := by
      rw [kmsw_R_eq, codeWalk_eq_integrateCodes]
      rfl
    rw [heq, heq, boltzmann_tau_spec r ω hhit]
    have hb := hbefore j hj
    omega

/-- hit τ_r the past map XDP length equals the code-graph XDP distance from the source
to the cut vertex; the renewal-time selection T_{m_k} and the infinite source-map
(F4c) identification are not treated; not the paper result. Both finite lengths
are cast explicitly, on one simultaneous event of full conditioned-path measure. -/
theorem firstHitPastXdpLength_ae_eq_shifted_stage (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let t := (conditionedSecondCoordinateFirstHit r p).toNat
      let w := boltzmannKMSWStream (pathCode p)
      (firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) : WithBot ℕ) =
          ldpSup (⟨0⟩ : StagePresentVertex w (t - 1))
            ⟨(kmswStage w (t - 1)).east (kmswStage w (t - 1)).active⟩ ∧
        (firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) : ℕ∞) =
          sdp (⟨0⟩ : StagePresentVertex w (t - 1))
            ⟨(kmswStage w (t - 1)).east (kmswStage w (t - 1)).active⟩ := by
  filter_upwards [conditionedVectorPathLaw_ae_legal, firstHitPastMap_finite_hit_ae r hr,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hp hfin hex
  obtain ⟨u, hup, _, _, _, hL, _⟩ := hex
  have hLp (n : ℕ) : 0 ≤ (p n).1 := by
    have hn := hL n
    rwa [kmsw_L_eq, hup] at hn
  have hE := pathCode_event r p hp.1 hp.2 hLp hfin
  have ht := (firstHit_stoppedCode_conventions r p hp.1 hp.2 hfin).2.2.1
  have h := firstHitPastXdpLength_eq_shifted_stage r hr (pathCode p) hE
  dsimp only at h ⊢
  rwa [ht] at h

private theorem active_present (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).present (act w t) = true := by
  apply (kmswStage_status w t).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem liftPathToStage {w : ℕ → Fin 3} {t : ℕ}
    {a b : PresentVertex w} (p : Path a b)
    (hp : ∀ e ∈ pathEdgeList p, ∃ k ≤ t, e = act w k) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w t) ⟨b.id⟩,
      (stageToLimit w t).mapPath q = p := by
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons a b p e ih =>
    have hp' : ∀ f ∈ pathEdgeList p, ∃ k ≤ t, f = act w k := by
      intro f hf
      exact hp f (List.mem_append_left _ hf)
    obtain ⟨q, hq⟩ := ih hp'
    obtain ⟨k, hk, he⟩ := hp e.val (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have halloc : e.val < (kmswStage w t).nextEdge := by
      rw [he]
      exact act_lt_nextEdge w hk
    have hpres : (kmswStage w t).present e.val = true := by
      rw [he]
      exact (present_mono w (act_lt_nextEdge w (Nat.le_refl k))
        (active_present w k) t hk).2
    let f : (⟨a.id⟩ : StagePresentVertex w t) ⟶ ⟨b.id⟩ :=
      ⟨e.val, halloc, hpres,
        (edge_endpoints_eq w halloc).1.trans e.property.2.1,
        (edge_endpoints_eq w halloc).2.trans e.property.2.2⟩
    refine ⟨q.cons f, ?_⟩
    rw [Prefunctor.mapPath_cons, hq]
    have hf : (stageToLimit w t).map f = e := Subtype.ext rfl
    exact congrArg (Path.cons p) hf

private theorem recordPath_lift_pred {w : ℕ → Fin 3} {t : ℕ}
    {a : PresentVertex w} (p : Path a (recordVertex w t)) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w (t - 1)) ⟨(recordVertex w t).id⟩,
      (stageToLimit w (t - 1)).mapPath q = p := by
  apply liftPathToStage p
  intro e he
  obtain ⟨k, hk, hke⟩ := (presentPath_to_record_edges_before p).2 e he
  exact ⟨k, by omega, hke⟩

private theorem recordDistances_eq_pred (w : ℕ → Fin 3) (t : ℕ)
    (a : PresentVertex w) :
    presentLdp a (recordVertex w t) =
        WithBot.map (fun n : ℕ => (n : ℕ∞))
          (ldpSup (⟨a.id⟩ : StagePresentVertex w (t - 1)) ⟨(recordVertex w t).id⟩) ∧
      sdp a (recordVertex w t) =
        sdp (⟨a.id⟩ : StagePresentVertex w (t - 1)) ⟨(recordVertex w t).id⟩ := by
  have hp : pathLengths (⟨a.id⟩ : StagePresentVertex w t) ⟨(recordVertex w t).id⟩ =
      pathLengths (⟨a.id⟩ : StagePresentVertex w (t - 1)) ⟨(recordVertex w t).id⟩ := by
    ext k
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := recordPath_lift_pred ((stageToLimit w t).mapPath p)
      refine ⟨q, ?_⟩
      exact (stageToLimit_length w (t - 1) q).symm.trans
        ((congrArg Path.length hq).trans (stageToLimit_length w t p))
    · rintro ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := presentPath_to_record_lifts ((stageToLimit w (t - 1)).mapPath p)
      refine ⟨q, ?_⟩
      exact (stageToLimit_length w t q).symm.trans
        ((congrArg Path.length hq).trans (stageToLimit_length w (t - 1) p))
  constructor
  · rw [(presentDistances_to_record_eq_stage w t a).1]
    unfold ldpSup
    rw [hp]
  · apply le_antisymm
    · exact sdp_limit_le_sdp_stage w (t - 1) ⟨a.id⟩ ⟨(recordVertex w t).id⟩
    · apply le_iInf
      intro p
      obtain ⟨q, hq⟩ := recordPath_lift_pred p
      have hlen : q.length = p.length :=
        (stageToLimit_length w (t - 1) q).symm.trans (congrArg Path.length hq)
      exact (sdp_le_length q).trans_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hlen)

/-- hit τ_r the past map XDP length equals the code-graph XDP distance from the source
to the cut vertex; the renewal-time selection T_{m_k} and the infinite source-map
(F4c) identification are not treated; not the paper result. The limit graph here
uses the shifted stream; LDP is cast from ℕ through ℕ∞ into WithBot ℕ∞. -/
theorem firstHitPastXdpLength_eq_shifted_limit (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    ((firstHitPastXdpLength .ldp r (stoppedMap r hr ω) : ℕ∞) : WithBot ℕ∞) =
        presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w t) ∧
      (firstHitPastXdpLength .sdp r (stoppedMap r hr ω) : ℕ∞) =
        sdp (⟨0⟩ : PresentVertex w) (recordVertex w t) := by
  have hs := firstHitPastXdpLength_eq_shifted_stage r hr ω hE
  have hb := (firstHitPast_sink_eq_record_and_strict r hr ω hE).1
  have hd := recordDistances_eq_pred (boltzmannKMSWStream ω) (boltzmannTau r ω) ⟨0⟩
  dsimp only at hs hb hd ⊢
  rw [hb] at hd
  constructor
  · rw [hd.1, ← hs.1]
    rfl
  · exact hs.2.trans hd.2.symm

/-- hit τ_r the past map XDP length equals the code-graph XDP distance from the source
to the cut vertex; the renewal-time selection T_{m_k} and the infinite source-map
(F4c) identification are not treated; not the paper result. This is the limit
formula for the stream integrating the conditioned path, with the dummy removed. -/
theorem firstHitPastXdpLength_ae_eq_shifted_limit (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let t := (conditionedSecondCoordinateFirstHit r p).toNat
      let w := boltzmannKMSWStream (pathCode p)
      ((firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) : ℕ∞) : WithBot ℕ∞) =
          presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w t) ∧
        (firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) : ℕ∞) =
          sdp (⟨0⟩ : PresentVertex w) (recordVertex w t) := by
  filter_upwards [conditionedVectorPathLaw_ae_legal, firstHitPastMap_finite_hit_ae r hr,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hp hfin hex
  obtain ⟨u, hup, _, _, _, hL, _⟩ := hex
  have hLp (n : ℕ) : 0 ≤ (p n).1 := by
    have hn := hL n
    rwa [kmsw_L_eq, hup] at hn
  have hE := pathCode_event r p hp.1 hp.2 hLp hfin
  have ht := (firstHit_stoppedCode_conventions r p hp.1 hp.2 hfin).2.2.1
  have h := firstHitPastXdpLength_eq_shifted_limit r hr (pathCode p) hE
  dsimp only at h ⊢
  rwa [ht] at h

end DirectedDistances.PaperProofs.Section4
