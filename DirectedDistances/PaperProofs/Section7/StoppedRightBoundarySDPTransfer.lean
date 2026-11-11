module

public import DirectedDistances.PaperProofs.Section7.BoltzmannRightBoundarySDP
public import DirectedDistances.PaperProofs.Section7.CellSDPLowerAssembly
public import DirectedDistances.PaperProofs.Section7.HitCoupling
public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLawFull
public import DirectedDistances.KMSW.StageDirectedMapPathLengths
public import DirectedDistances.KMSW.Lemma79MarkTransport

/-! # Stopped right-boundary SDP transfer

Helpers toward Lemma 7.12 (`lem-boltzmann-sdp-lower`,
gives the exact SDP monotonicity direction. The hatted stopped-map prefix
identifies the source and every right-boundary level through `R`, yielding
the stopped right-boundary transfer implication. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap
open Quiver

/-- SDP in a quiver is at least SDP in the target under an
arrow-preserving map. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem sdp_submap_ge_of_prefunctor
    {V W : Type*} [Quiver V] [Quiver W] (F : Prefunctor V W)
    (a b : V) :
    DirectedDistances.sdp a b ≥ DirectedDistances.sdp (F.obj a) (F.obj b) := by
  have hlen : ∀ p : Path a b, (F.mapPath p).length = p.length := by
    intro p
    induction p with
    | nil => rfl
    | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
  change DirectedDistances.sdp (F.obj a) (F.obj b) ≤
    ⨅ p : Path a b, (p.length : ℕ∞)
  refine le_iInf fun p => ?_
  calc
    DirectedDistances.sdp (F.obj a) (F.obj b) ≤
        ((F.mapPath p).length : ℕ∞) := DirectedDistances.sdp_le_length _
    _ = p.length := by rw [hlen]

/-- For an arrow-preserving map of a stopped marked map into a larger present
graph, the stopped-map SDP is at least the larger-graph SDP between the mapped
endpoints. Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper
result. -/
theorem stoppedPresentSDP_ge_of_prefunctor {R : ℕ}
    (q : RightVertexMarkedBoltzmannSpace R) (w : ℕ → Fin 3)
    (F : Prefunctor (MapVertex q.1.2.2.out.B.map) (PresentVertex w))
    (a b : MapVertex q.1.2.2.out.B.map) :
    presentDartSDP q.1.2.2.out.B.map a b ≥
      DirectedDistances.sdp (F.obj a) (F.obj b) := by
  exact sdp_submap_ge_of_prefunctor F a b

/-- The stopped right-boundary SDP dominates the larger present-graph SDP
after identifying the source and endpoint. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem stoppedRightBoundarySDP_ge_of_prefunctor {R : ℕ}
    (q : RightVertexMarkedBoltzmannSpace R) (w : ℕ → Fin 3)
    (F : Prefunctor (MapVertex q.1.2.2.out.B.map) (PresentVertex w))
    (i : Fin (R + 1)) (x y : PresentVertex w)
    (hx : F.obj q.1.2.2.out.B.source = x)
    (hy : F.obj (rightBoundaryVertex q i) = y) :
    presentDartSDP q.1.2.2.out.B.map q.1.2.2.out.B.source
        (rightBoundaryVertex q i) ≥ DirectedDistances.sdp x y := by
  rw [← hx, ← hy]
  exact stoppedPresentSDP_ge_of_prefunctor q w F
    q.1.2.2.out.B.source (rightBoundaryVertex q i)

/-- The canonical inclusion of the present-edge quiver at stage `n` into
stage `m` when `n ≤ m`, retaining edge IDs and vertex labels. Helper toward
Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper result. -/
@[expose] noncomputable def stagePresentMapToLater (w : ℕ → Fin 3)
    {n m : ℕ} (hnm : n ≤ m) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w m) where
  obj v := ⟨v.id⟩
  map {_ _} e := by
    have hp := present_mono w e.property.1 e.property.2.1 m hnm
    have he := present_endpoints_stable w e.property.1 e.property.2.1 hnm
    refine ⟨e.val, hp.1, hp.2, ?_, ?_⟩
    · exact he.1.trans e.property.2.2.1
    · exact he.2.trans e.property.2.2.2

/-- The stage inclusion preserves path lengths. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem stagePresentMapToLater_length (w : ℕ → Fin 3)
    {n m : ℕ} (hnm : n ≤ m) {a b : StagePresentVertex w n}
    (p : Path a b) :
    ((stagePresentMapToLater w hnm).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- The raw stage embeds injectively in the limit present graph. Helper toward
Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result. -/
theorem stageToLimit_injective (w : ℕ → Fin 3) (n : ℕ) :
    Function.Injective (stageToLimit w n).obj := by
  intro a b hab
  cases a
  cases b
  cases hab
  rfl

/-- The hatted present quiver maps to its aligned raw stage, preserving each
present dart. Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper
result. -/
@[expose] noncomputable def hatStagePresentMapToRawStage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) :
    Prefunctor (StagePresentVertex (hatCodes w h) m)
      (StagePresentVertex w (quadrantRStageTime w h m)) where
  obj v := ⟨hatAllVertexMap w h m v.id⟩
  map {_ _} e := by
    have hp := hatAll_present w h m e.val e.property.1 e.property.2.1
    refine ⟨hatAllEdgeMap w h m e.val, hp.1, hp.2.1, ?_, ?_⟩
    · rw [hp.2.2.1, e.property.2.2.1]
    · rw [hp.2.2.2, e.property.2.2.2]

/-- The hatted stage vertex map is injective on allocated vertices. Helper
toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result. -/
theorem hatAllVertexMap_injective_of_allocated (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) {a b : ℕ}
    (ha : a < (kmswStage (hatCodes w h) m).nextVertex)
    (hb : b < (kmswStage (hatCodes w h) m).nextVertex)
    (hab : hatAllVertexMap w h m a = hatAllVertexMap w h m b) :
    a = b := by
  let x : {v : PresentVertex (hatCodes w h) //
      ∃ k, v.id < (kmswStage (hatCodes w h) k).nextVertex} :=
    ⟨⟨a⟩, ⟨m, ha⟩⟩
  let y : {v : PresentVertex (hatCodes w h) //
      ∃ k, v.id < (kmswStage (hatCodes w h) k).nextVertex} :=
    ⟨⟨b⟩, ⟨m, hb⟩⟩
  have hxy : hatExplicitVertexEquiv w h x = hatExplicitVertexEquiv w h y := by
    apply Subtype.ext
    apply congrArg PresentVertex.mk
    simp only [x, y]
    rw [hatLimitVertexMap_eq_stage w h m a ha,
      hatLimitVertexMap_eq_stage w h m b hb]
    exact hab
  have hxy' := (hatExplicitVertexEquiv w h).injective hxy
  exact congrArg (fun z => z.1.id) hxy'

/-- SDP in a finite stage is at least SDP in any later stage, with the same
source and endpoint IDs. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem sdp_stage_ge_later (w : ℕ → Fin 3) {n m : ℕ} (hnm : n ≤ m)
    (a b : StagePresentVertex w n) :
    DirectedDistances.sdp a b ≥
      DirectedDistances.sdp (⟨a.id⟩ : StagePresentVertex w m) ⟨b.id⟩ := by
  let F := stagePresentMapToLater w hnm
  change DirectedDistances.sdp a b ≥
    DirectedDistances.sdp (F.obj a) (F.obj b)
  exact sdp_submap_ge_of_prefunctor F a b

/-- SDP at a pre-hit stage is at least SDP at the stage immediately before
the hit. Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper
result. -/
theorem sdp_stage_ge_preHitCut (w : ℕ → Fin 3) (n τ : ℕ) (hn : n < τ)
    (a b : StagePresentVertex w n) :
    DirectedDistances.sdp a b ≥
      DirectedDistances.sdp (⟨a.id⟩ : StagePresentVertex w (τ - 1)) ⟨b.id⟩ := by
  exact sdp_stage_ge_later w (by omega) a b

/-- Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper result.
The source hit time equals the selected hatted source time -/
theorem stoppedCellHitTime_eq_hattedSourceTime (ω : ℕ → Fin 3) (R : ℕ)
    (hR : 1 ≤ R) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) :
    boundaryHitTime (fun i => ω (i + 1)) hb (R : ℤ) =
      sourceQuadrantS (fun i => ω (i + 1)) h
        (hattedRightVertexHitTime (fun i => ω (i + 1)) h hb R hR) :=
  sourceHitTime_eq_sourceHattedRightVertexHit (fun i => ω (i + 1)) h hb R hR

/-- Remaining stopped-map identification goal. Given the infinite-map SDP
bound and the pre-hit stage boundary witness, identify an injective, dart
preserving map whose stopped right boundary contains that witness, then
transfer the bound. Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not -/
@[expose] def stoppedCellRightBoundaryIdentificationGoal
    (ω : ℕ → Fin 3) (R : ℕ) (hR : 1 ≤ R)
    (_h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (n s : ℕ) (c : ℕ∞) : Prop :=
  (n < boundaryHitTime (fun i => ω (i + 1)) hb (R : ℤ)) →
    1 ≤ s → s ≤ R →
    (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
      (kmswStage (fun i => ω (i + 1)) n).west e =
          boundaryVertex (fun i => ω (i + 1)) hb (s : ℤ) ∨
        (kmswStage (fun i => ω (i + 1)) n).east e =
          boundaryVertex (fun i => ω (i + 1)) hb (s : ℤ)) →
    c ≤ DirectedDistances.sdp
      (boundaryPresentVertex (fun i => ω (i + 1)) hb 0)
      (boundaryPresentVertex (fun i => ω (i + 1)) hb (s : ℤ)) →
  let q := stoppedMarked R hR (quadrantHatWalk ω)
  ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map)
      (PresentVertex (fun i => ω (i + 1))),
    Function.Injective F.obj ∧
      F.obj q.1.2.2.out.B.source =
        boundaryPresentVertex (fun i => ω (i + 1)) hb 0 ∧
      ∃ i : Fin (R + 1),
        F.obj (rightBoundaryVertex q i) =
          boundaryPresentVertex (fun i => ω (i + 1)) hb (s : ℤ) ∧
        c ≤ presentDartSDP q.1.2.2.out.B.map q.1.2.2.out.B.source
          (rightBoundaryVertex q i)

/-- The stopped map of the hatted quadrant walk is represented by the
corresponding hatted KMSW code prefix. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem quadrantHatWalk_stoppedMap_value (ω : ℕ → Fin 3) (R : ℕ)
    (hR : 1 ≤ R) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) :
    let w : ℕ → Fin 3 := fun i => ω (i + 1)
    let p := DirectedDistances.RandomWalk.quadrantHatWalk ω
    let t := hattedRightVertexHitTime w h hb R hR
    ∃ (ht : 1 ≤ t) (ell : ℕ) (c : KMSWWalkClass ell R t),
      (∀ i : Fin (t - 1), c.val i = pathCode p (i.val + 1)) ∧
      (∀ i : Fin (t - 1), c.val i = hatCodes w h i.val) ∧
      stoppedMap R hR (pathCode p) =
        some ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ := by
  classical
  dsimp only
  let p := DirectedDistances.RandomWalk.quadrantHatWalk ω
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let t := hattedRightVertexHitTime w h hb R hR
  have hcodeTime : t = hattedRightHitTime w h R hR :=
    hattedRightVertexHitTime_eq_hattedRightHitTime w h hb R hR
  have hp : p = integrateCodes (hatCodes w h) := by
    change DirectedDistances.RandomWalk.quadrantHatWalk ω = _
    rw [DirectedDistances.RandomWalk.quadrantHatWalk_eq_interval ω h]
    rfl
  have hp0 : p 0 = (0, 0) := by
    change DirectedDistances.RandomWalk.quadrantHatWalk ω 0 = (0, 0)
    rw [DirectedDistances.RandomWalk.quadrantHatWalk_eq_interval ω h]
    exact (quadrantIntervalWalk_initial ω h).1
  have hpstep (i : ℕ) :
      p (i + 1) - p i ∈ Set.range lazyTwoDimensionalStep := by
    rw [hp]
    refine ⟨hatCodes w h i, ?_⟩
    simp only [integrateCodes, Finset.sum_range_succ]
    abel
  have hcoord (i : ℕ) : (p i).2 = DirectedDistances.KMSW.R (hatCodes w h) i := by
    rw [hp]
    simp [DirectedDistances.KMSW.R, integrateCodes, Prod.snd_sum]
  have hnonneg (i : ℕ) : 0 ≤ (p i).1 := by
    rw [hp, ← rCodeSequence_quadrantTrajectory_eq_hatCodes w h]
    change 0 ≤ (integrateCodes (pitmanCode _) i).1
    exact integrateCodes_pitmanCode_fst_nonneg _ i
  have hhitCoord : (p t).2 = -(R : ℤ) := by
    rw [hcoord, hcodeTime]
    exact hattedRightHitTime_spec w h R hR
  have hhitCode : (codeWalk (pathCode p) t).2 = -(R : ℤ) := by
    calc
      (codeWalk (pathCode p) t).2 = (p t - p 0).2 :=
        congrArg Prod.snd (codeWalk_pathCode p hpstep t)
      _ = (p t).2 := by simp [hp0]
      _ = -(R : ℤ) := hhitCoord
  have hhit : ∃ k, (codeWalk (pathCode p) k).2 = -(R : ℤ) := by
    exact ⟨t, hhitCode⟩
  have hfirst : ∀ k, (codeWalk (pathCode p) k).2 = -(R : ℤ) → t ≤ k := by
    intro k hk
    have hk' : DirectedDistances.KMSW.R (hatCodes w h) k = -(R : ℤ) := by
      calc
        DirectedDistances.KMSW.R (hatCodes w h) k = (p k).2 :=
          (hcoord k).symm
        _ = (codeWalk (pathCode p) k).2 := by
          symm
          calc
            (codeWalk (pathCode p) k).2 = (p k - p 0).2 :=
              congrArg Prod.snd (codeWalk_pathCode p hpstep k)
            _ = (p k).2 := by simp [hp0]
        _ = -(R : ℤ) := hk
    by_contra hkt
    have hlt : k < t := by omega
    have hlt' : k < hattedRightHitTime w h R hR := by
      rw [← hcodeTime]
      exact hlt
    exact (Nat.find_min (hattedRightHit_exists w h R hR) hlt') hk'
  have htau : boltzmannTau R (pathCode p) = t := by
    have hfind : boltzmannTau R (pathCode p) = Nat.find hhit := by
      unfold boltzmannTau
      rw [dite_eq_left hhit]
    rw [hfind]
    apply Nat.le_antisymm
    · exact Nat.find_min' hhit hhitCode
    · exact hfirst _ (Nat.find_spec hhit)
  have hE : pathCode p ∈ boltzmannEvent R := by
    refine ⟨t, ?_, ?_⟩
    · exact hhitCode
    · intro j hj
      have hdecode := congrArg Prod.fst (codeWalk_pathCode p hpstep j)
      have hfirstCoord : (codeWalk (pathCode p) j).1 = (p j).1 := by
        calc
          (codeWalk (pathCode p) j).1 = (p j - p 0).1 := hdecode
          _ = (p j).1 := by simp [hp0]
      rw [hfirstCoord]
      exact hnonneg j
  have hobs := boltzmann_boundary_observable R hR (pathCode p) hE
  dsimp only at hobs
  rcases hobs with ⟨ht, _, _, _, _, _, _, _⟩
  have hstream : boltzmannKMSWStream (pathCode p) = hatCodes w h := by
    funext i
    dsimp only [boltzmannKMSWStream]
    have hs := step_pathCode p i (hpstep i)
    have hi : p (i + 1) - p i = lazyTwoDimensionalStep (hatCodes w h i) := by
      rw [hp]
      simp only [integrateCodes, Finset.sum_range_succ]
      abel
    rw [hi] at hs
    exact lazyTwoDimensionalStep_injective hs
  let tau := boltzmannTau R (pathCode p)
  let ell := (L (boltzmannKMSWStream (pathCode p)) tau).toNat
  let c₀ : KMSWWalkClass ell R tau :=
    ⟨stoppedWord R (pathCode p), (stoppedWord_admissible R hR
      (pathCode p) hE).1⟩
  have hprefix₀ : ∀ i : Fin (tau - 1), c₀.val i = pathCode p (i.val + 1) := by
    intro i
    rfl
  have hprefixHat₀ : ∀ i : Fin (tau - 1), c₀.val i = hatCodes w h i.val := by
    intro i
    calc
      c₀.val i = pathCode p (i.val + 1) := hprefix₀ i
      _ = boltzmannKMSWStream (pathCode p) i.val := by rfl
      _ = hatCodes w h i.val := congrFun hstream i.val
  have hidx : stoppedIndex R hR (pathCode p) =
      some ⟨tau, ⟨ell, c₀⟩⟩ := by
    simp [stoppedIndex, hE, tau, ell, c₀]
  have hmap₀ : stoppedMap R hR (pathCode p) =
      some ⟨ell, ⟨tau, kmswToMapIsoClass ht c₀⟩⟩ := by
    unfold stoppedMap
    rw [hidx]
    change stoppedWalkMapOption R ⟨tau, ⟨ell, c₀⟩⟩ = _
    unfold stoppedWalkMapOption
    rw [dite_eq_left ht]
    rfl
  have htau' : hattedRightVertexHitTime w h hb R hR = tau := htau.symm
  rw [htau']
  exact ⟨ht, ell, c₀, hprefix₀, hprefixHat₀, hmap₀⟩

/-- The stopped map value is the walk-class quotient on its stopping event.
Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result. -/
theorem stoppedMarked_map_value_of_stoppedMap_eq {r t ell : ℕ}
    (hr : 1 ≤ r) (ht : 1 ≤ t) (p : ℕ → ℤ × ℤ)
    (c : KMSWWalkClass ell r t)
    (hmap : stoppedMap r hr (pathCode p) =
      some ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩) :
    (stoppedMarked r hr p).1 =
      ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ := by
  change (stoppedMap r hr (pathCode p)).getD (stoppedMarkedDefault r hr) = _
  rw [hmap]
  rfl

/-- The stopped marked value is the class selected by the hatted right hit.
Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result. -/
theorem quadrantHatWalk_stoppedMarked_value (ω : ℕ → Fin 3) (R : ℕ)
    (hR : 1 ≤ R) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) :
    let q := stoppedMarked R hR (quadrantHatWalk ω)
    ∃ (ht : 1 ≤ hattedRightVertexHitTime (fun i => ω (i + 1)) h hb R hR)
      (ell : ℕ)
      (c : KMSWWalkClass ell R
        (hattedRightVertexHitTime (fun i => ω (i + 1)) h hb R hR)),
      q.1 = ⟨ell, ⟨hattedRightVertexHitTime (fun i => ω (i + 1)) h hb R hR,
        kmswToMapIsoClass ht c⟩⟩ := by
  dsimp only
  obtain ⟨ht, ell, c, _, _, hmap⟩ :=
    quadrantHatWalk_stoppedMap_value ω R hR h hb
  exact ⟨ht, ell, c,
    stoppedMarked_map_value_of_stoppedMap_eq hR ht
      (quadrantHatWalk ω) c hmap⟩

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The selected stopped class retains its hatted code prefix -/
theorem quadrantHatWalk_stoppedMarked_value_with_prefix (ω : ℕ → Fin 3)
    (R : ℕ) (hR : 1 ≤ R) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) :
    let w : ℕ → Fin 3 := fun i => ω (i + 1)
    let q := stoppedMarked R hR (quadrantHatWalk ω)
    ∃ (ht : 1 ≤ hattedRightVertexHitTime w h hb R hR) (ell : ℕ)
      (c : KMSWWalkClass ell R (hattedRightVertexHitTime w h hb R hR)),
      q.1 = ⟨ell, ⟨hattedRightVertexHitTime w h hb R hR,
        kmswToMapIsoClass ht c⟩⟩ ∧
      ∀ i : Fin (hattedRightVertexHitTime w h hb R hR - 1),
        c.val i = hatCodes w h i.val := by
  dsimp only
  obtain ⟨ht, ell, c, _, hprefix, hmap⟩ :=
    quadrantHatWalk_stoppedMap_value ω R hR h hb
  exact ⟨ht, ell, c,
    stoppedMarked_map_value_of_stoppedMap_eq hR ht
      (quadrantHatWalk ω) c hmap,
    hprefix⟩

/-- The canonical walk-class representative is boundary-isomorphic to the
quotient representative of its KMSW map class. Helper toward Lemma 7.12
(lem-boltzmann-sdp-lower); not a paper result. -/
theorem kmswWalkClassRep_out_baseIso {r t ell : ℕ} (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t) :
    Nonempty (BipolarBoundaryBaseIso (kmswWalkClassRep ht c).B
      (kmswToMapIsoClass ht c).out.B) := by
  let rep := (kmswToMapIsoClass ht c).out
  have hmk : KMSWMapIsoClass.mk (kmswWalkClassRep ht c) =
      KMSWMapIsoClass.mk rep := by
    calc
      KMSWMapIsoClass.mk (kmswWalkClassRep ht c) = kmswToMapIsoClass ht c := rfl
      _ = KMSWMapIsoClass.mk rep := (Quotient.out_eq _).symm
  exact (KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hmk

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The stopped quotient representative embeds into the raw present graph through -/
@[expose] noncomputable def stoppedRightBoundaryPresentPrefunctor
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (R ell t : ℕ)
    (q : RightVertexMarkedBoltzmannSpace R) (ht : 1 ≤ t)
    (c : KMSWWalkClass ell R t)
    (hclass : q.1 = ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩)
    (hprefix : ∀ i : Fin (t - 1), c.val i = hatCodes w h i.val) :
    Prefunctor (MapVertex q.1.2.2.out.B.map) (PresentVertex w) := by
  classical
  rcases q with ⟨q₁, mark⟩
  rcases q₁ with ⟨ellQ, q₂⟩
  rcases q₂ with ⟨tQ, classQ⟩
  change (⟨ellQ, ⟨tQ, classQ⟩⟩ : AllBoltzmannSpace R) =
    ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ at hclass
  cases hclass
  let m := t - 1
  let qRep := (kmswToMapIsoClass ht c).out
  have hmk : KMSWMapIsoClass.mk (kmswWalkClassRep ht c) =
      KMSWMapIsoClass.mk qRep := by
    calc
      KMSWMapIsoClass.mk (kmswWalkClassRep ht c) = kmswToMapIsoClass ht c := rfl
      _ = KMSWMapIsoClass.mk qRep := (Quotient.out_eq _).symm
  have hbase : Nonempty (BipolarBoundaryBaseIso
      (kmswWalkClassRep ht c).B qRep.B) :=
    (KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hmk
  let I : BipolarBoundaryBaseIso qRep.B
      (kmswWalkClassBase ht c) :=
    (Classical.choice hbase).symm.trans (kmswWalkClassRep_baseIso ht c)
  have hcodes : ∀ i < m, codeExtend c i = hatCodes w h i := by
    intro i hi
    rw [codeExtend_of_lt c i hi]
    exact hprefix ⟨i, hi⟩
  have hstage : kmswStage (codeExtend c) m = kmswStage (hatCodes w h) m :=
    kmswStage_eq_of_prefix (codeExtend c) (hatCodes w h) m hcodes
  let G : Prefunctor (MapVertex qRep.B.map)
      (StagePresentVertex (codeExtend c) m) := {
    obj := fun v => stageMapVertex (codeExtend c) m (I.vertexEquiv v)
    map := fun {u v} e => by
      have hs : (kmswWalkClassBase ht c).map.directedStep
          (I.vertexEquiv u) (I.vertexEquiv v) := by
        refine ⟨I.toEquiv e.val, ?_, ?_, ?_, ?_⟩
        · intro hm
          exact e.property.1 ((I.missing_iff e.val).mp hm)
        · exact (I.tail_iff e.val).2 e.property.2.1
        · change dartTailVertex (kmswWalkClassBase ht c).map
            (I.toEquiv e.val) = I.vertexEquiv u
          calc
            dartTailVertex (kmswWalkClassBase ht c).map (I.toEquiv e.val) =
                I.vertexEquiv (dartTailVertex qRep.B.map e.val) :=
              (I.vertexEquiv_dartTailVertex e.val).symm
            _ = I.vertexEquiv u := congrArg I.vertexEquiv e.property.2.2.1
        · change dartHeadVertex (kmswWalkClassBase ht c).map
            (I.toEquiv e.val) = I.vertexEquiv v
          calc
            dartHeadVertex (kmswWalkClassBase ht c).map (I.toEquiv e.val) =
                I.vertexEquiv (dartHeadVertex qRep.B.map e.val) :=
              (I.vertexEquiv_dartHeadVertex e.val).symm
            _ = I.vertexEquiv v := congrArg I.vertexEquiv e.property.2.2.2
      exact Classical.choice
        ((stageMap_directedStep_iff (codeExtend c) m
          (I.vertexEquiv u) (I.vertexEquiv v)).mp hs)
  }
  let Ghat : Prefunctor (MapVertex qRep.B.map)
      (StagePresentVertex (hatCodes w h) m) := {
    obj := fun v => ⟨(G.obj v).id⟩
    map := fun {u v} e => by
      let a := G.map e
      refine ⟨a.val, ?_, ?_, ?_, ?_⟩
      · rw [← hstage]
        exact a.property.1
      · rw [← hstage]
        exact a.property.2.1
      · change (kmswStage (hatCodes w h) m).west a.val = (G.obj u).id
        rw [← hstage]
        exact a.property.2.2.1
      · change (kmswStage (hatCodes w h) m).east a.val = (G.obj v).id
        rw [← hstage]
        exact a.property.2.2.2
  }
  exact (Ghat.comp (hatStagePresentMapToRawStage w h m)).comp
    (stageToLimit w (quadrantRStageTime w h m))

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The stopped representative's map into the present graph is injective. -/
theorem stoppedRightBoundaryPresentPrefunctor_injective
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (R ell t : ℕ)
    (q : RightVertexMarkedBoltzmannSpace R) (ht : 1 ≤ t)
    (c : KMSWWalkClass ell R t)
    (hclass : q.1 = ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩)
    (hprefix : ∀ i : Fin (t - 1), c.val i = hatCodes w h i.val) :
    Function.Injective
      (stoppedRightBoundaryPresentPrefunctor w h R ell t q ht c hclass hprefix).obj := by
  classical
  rcases q with ⟨q₁, mark⟩
  rcases q₁ with ⟨ellQ, q₂⟩
  rcases q₂ with ⟨tQ, classQ⟩
  change (⟨ellQ, ⟨tQ, classQ⟩⟩ : AllBoltzmannSpace R) =
    ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ at hclass
  cases hclass
  let m := t - 1
  let qRep := (kmswToMapIsoClass ht c).out
  have hmk : KMSWMapIsoClass.mk (kmswWalkClassRep ht c) =
      KMSWMapIsoClass.mk qRep := by
    calc
      KMSWMapIsoClass.mk (kmswWalkClassRep ht c) = kmswToMapIsoClass ht c := rfl
      _ = KMSWMapIsoClass.mk qRep := (Quotient.out_eq _).symm
  have hbase : Nonempty (BipolarBoundaryBaseIso
      (kmswWalkClassRep ht c).B qRep.B) :=
    (KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hmk
  let I : BipolarBoundaryBaseIso qRep.B (kmswWalkClassBase ht c) :=
    (Classical.choice hbase).symm.trans (kmswWalkClassRep_baseIso ht c)
  have hcodes : ∀ i < m, codeExtend c i = hatCodes w h i := by
    intro i hi
    rw [codeExtend_of_lt c i hi]
    exact hprefix ⟨i, hi⟩
  have hstage : kmswStage (codeExtend c) m = kmswStage (hatCodes w h) m :=
    kmswStage_eq_of_prefix (codeExtend c) (hatCodes w h) m hcodes
  let G : Prefunctor (MapVertex qRep.B.map)
      (StagePresentVertex (codeExtend c) m) := {
    obj := fun v => stageMapVertex (codeExtend c) m (I.vertexEquiv v)
    map := fun {u v} e => by
      have hs : (kmswWalkClassBase ht c).map.directedStep
          (I.vertexEquiv u) (I.vertexEquiv v) := by
        refine ⟨I.toEquiv e.val, ?_, ?_, ?_, ?_⟩
        · intro hm
          exact e.property.1 ((I.missing_iff e.val).mp hm)
        · exact (I.tail_iff e.val).2 e.property.2.1
        · change dartTailVertex (kmswWalkClassBase ht c).map
            (I.toEquiv e.val) = I.vertexEquiv u
          calc
            dartTailVertex (kmswWalkClassBase ht c).map (I.toEquiv e.val) =
                I.vertexEquiv (dartTailVertex qRep.B.map e.val) :=
              (I.vertexEquiv_dartTailVertex e.val).symm
            _ = I.vertexEquiv u := congrArg I.vertexEquiv e.property.2.2.1
        · change dartHeadVertex (kmswWalkClassBase ht c).map
            (I.toEquiv e.val) = I.vertexEquiv v
          calc
            dartHeadVertex (kmswWalkClassBase ht c).map (I.toEquiv e.val) =
                I.vertexEquiv (dartHeadVertex qRep.B.map e.val) :=
              (I.vertexEquiv_dartHeadVertex e.val).symm
            _ = I.vertexEquiv v := congrArg I.vertexEquiv e.property.2.2.2
      exact Classical.choice
        ((stageMap_directedStep_iff (codeExtend c) m
          (I.vertexEquiv u) (I.vertexEquiv v)).mp hs)
  }
  let Ghat : Prefunctor (MapVertex qRep.B.map)
      (StagePresentVertex (hatCodes w h) m) := {
    obj := fun v => ⟨(G.obj v).id⟩
    map := fun {u v} e => by
      let a := G.map e
      refine ⟨a.val, ?_, ?_, ?_, ?_⟩
      · rw [← hstage]
        exact a.property.1
      · rw [← hstage]
        exact a.property.2.1
      · change (kmswStage (hatCodes w h) m).west a.val = (G.obj u).id
        rw [← hstage]
        exact a.property.2.2.1
      · change (kmswStage (hatCodes w h) m).east a.val = (G.obj v).id
        rw [← hstage]
        exact a.property.2.2.2
  }
  let H := hatStagePresentMapToRawStage w h m
  let L := stageToLimit w (quadrantRStageTime w h m)
  change Function.Injective (fun v => L.obj (H.obj (Ghat.obj v)))
  have hG : Function.Injective G.obj := by
    intro a b hab
    apply I.vertexEquiv.injective
    apply stageMapVertex_injective
    exact hab
  intro a b hab
  have hlimit := stageToLimit_injective w (quadrantRStageTime w h m) hab
  have hhat : hatAllVertexMap w h m (Ghat.obj a).id =
      hatAllVertexMap w h m (Ghat.obj b).id := by
    exact congrArg StagePresentVertex.id hlimit
  have ha : (Ghat.obj a).id < (kmswStage (hatCodes w h) m).nextVertex := by
    change (G.obj a).id < (kmswStage (hatCodes w h) m).nextVertex
    rw [← hstage]
    exact (stageVertexEquiv (codeExtend c) m (I.vertexEquiv a)).isLt
  have hb : (Ghat.obj b).id < (kmswStage (hatCodes w h) m).nextVertex := by
    change (G.obj b).id < (kmswStage (hatCodes w h) m).nextVertex
    rw [← hstage]
    exact (stageVertexEquiv (codeExtend c) m (I.vertexEquiv b)).isLt
  have hids := hatAllVertexMap_injective_of_allocated w h m ha hb hhat
  change (G.obj a).id = (G.obj b).id at hids
  have hGobj : G.obj a = G.obj b := by
    have h := congrArg
      (fun k : ℕ => (⟨k⟩ : StagePresentVertex (codeExtend c) m)) hids
    calc
      G.obj a = ⟨(G.obj a).id⟩ := by cases G.obj a; rfl
      _ = ⟨(G.obj b).id⟩ := h
      _ = G.obj b := by cases G.obj b; rfl
  exact hG hGobj

private theorem stoppedStageLRHeadZero (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.head? = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.head? = _
      cases kmswCodeStep (w n) with
      | up => exact ih
      | left =>
          simp only [kmswStepOfStep]
          split <;> exact ih
      | down =>
          simp only [kmswStepOfStep]
          split
          · exact ih
          · change ((kmswStage w n).LR ++
              [(kmswStage w n).nextEdge]).head? = _
            simpa only [List.head?_append_of_ne_nil _
              (kmswStage_LR_nonempty w n)] using ih

/-- Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper result.
The finite walk-class source maps to stage vertex zero. -/
theorem stoppedWalkClassBase_source_stage_label {ell R t : ℕ}
    (ht : 1 ≤ t) (c : KMSWWalkClass ell R t) :
    stageMapVertex (codeExtend c) (t - 1)
      (kmswWalkClassBase ht c).source = ⟨0⟩ := by
  let w := codeExtend c
  let m := t - 1
  let s := kmswStage w m
  have hf := kmswWalkClassMap_mem_sourceClass ht c
  dsimp only at hf
  rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, hLL,
    _, _, _, _, _⟩
  have hs := (kmswStage_boundary_chain_invariant w m).2.2.1
  have hUL := (kmswStage_UL_nonempty_active_last w m).1
  have h0 := (initial_edge_endpoints w m).1
  have hURs : s.UR = [] := hUR
  have hLLs : s.LL = [] := hLL
  change boundaryStart s (s.UL ++ s.UR) =
    boundaryStart s (s.LL ++ s.LR) at hs
  rw [hURs, hLLs, List.append_nil, List.nil_append] at hs
  have huhead : s.UL.head? = some (s.UL.head hUL) := List.head?_eq_some_head hUL
  have hrhead : s.LR.head? = some 0 := stoppedStageLRHeadZero w m
  change s.UL.head?.map s.west = s.LR.head?.map s.west at hs
  rw [huhead, hrhead] at hs
  change stageMapVertex w m (kmswWalkClassBase ht c).source = ⟨0⟩
  apply congrArg (StagePresentVertex.mk (w := w) (n := m))
  change s.west (s.UL.head hUL) = 0
  exact (Option.some.inj hs).trans h0

/-- Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper result.
The stopped representative source maps to the raw boundary source. -/
theorem stoppedRightBoundaryPresentPrefunctor_source
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (R ell t : ℕ)
    (q : RightVertexMarkedBoltzmannSpace R) (ht : 1 ≤ t)
    (c : KMSWWalkClass ell R t)
    (hclass : q.1 = ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩)
    (hprefix : ∀ i : Fin (t - 1), c.val i = hatCodes w h i.val)
    (hb : BoundaryHitWitnesses w) :
    (stoppedRightBoundaryPresentPrefunctor w h R ell t q ht c hclass hprefix).obj
        q.1.2.2.out.B.source = boundaryPresentVertex w hb 0 := by
  classical
  rcases q with ⟨q₁, mark⟩
  rcases q₁ with ⟨ellQ, q₂⟩
  rcases q₂ with ⟨tQ, classQ⟩
  change (⟨ellQ, ⟨tQ, classQ⟩⟩ : AllBoltzmannSpace R) =
    ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ at hclass
  cases hclass
  let m := t - 1
  let qRep := (kmswToMapIsoClass ht c).out
  have hmk : KMSWMapIsoClass.mk (kmswWalkClassRep ht c) =
      KMSWMapIsoClass.mk qRep := by
    calc
      KMSWMapIsoClass.mk (kmswWalkClassRep ht c) = kmswToMapIsoClass ht c := rfl
      _ = KMSWMapIsoClass.mk qRep := (Quotient.out_eq _).symm
  have hbase : Nonempty (BipolarBoundaryBaseIso
      (kmswWalkClassRep ht c).B qRep.B) :=
    (KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hmk
  let I : BipolarBoundaryBaseIso qRep.B (kmswWalkClassBase ht c) :=
    (Classical.choice hbase).symm.trans (kmswWalkClassRep_baseIso ht c)
  have hlabel : stageMapVertex (codeExtend c) m (I.vertexEquiv qRep.B.source) =
      ⟨0⟩ := by
    rw [I.vertexEquiv_source]
    exact stoppedWalkClassBase_source_stage_label ht c
  change (⟨hatAllVertexMap w h m
      (stageMapVertex (codeExtend c) m (I.vertexEquiv qRep.B.source)).id⟩ :
        PresentVertex w) = boundaryPresentVertex w hb 0
  rw [hlabel]
  simp [boundaryPresentVertex, boundaryVertex_zero, hatAllVertexMap_root]

/-- Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper result.
The finite walk-class base right path is the reversed inverse of the final stage's
LR dart run. -/
theorem stoppedWalkClassBase_rightPath_darts {ell R t : ℕ}
    (ht : 1 ≤ t) (c : KMSWWalkClass ell R t) :
    (kmswWalkClassBase ht c).rightPath.darts.reverse.map
        (kmswStageDirectedMap (codeExtend c) (t - 1)).toCombinatorialMap.edgeInv =
      kmswStageLRDartRun (codeExtend c) (t - 1) := by
  have hp := kmswWalkClassBase_paths ht c
  exact (Classical.choose_spec (Classical.choose_spec hp)).2

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The outer LR run traverses the LR edges in reverse order, from sink to source -/
theorem stoppedStageLRDartRun_edge_ids (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageLRDartRun w n).map (fun d => d.1.val) =
      (kmswStage w n).LR.reverse := by
  simp [kmswStageLRDartRun, stageDarts, List.map_map]

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The tail of the first outer LR dart is the east endpoint of the last LR edge -/
theorem stoppedWalkClassBase_sink_stage_label {ell R t : ℕ}
    (ht : 1 ≤ t) (c : KMSWWalkClass ell R t) :
    stageMapVertex (codeExtend c) (t - 1)
        (kmswWalkClassBase ht c).sink =
      ⟨(kmswStage (codeExtend c) (t - 1)).east
        ((kmswStage (codeExtend c) (t - 1)).LR.getLast
          (kmswStage_LR_nonempty (codeExtend c) (t - 1)))⟩ := by
  apply congrArg (StagePresentVertex.mk (w := codeExtend c) (n := t - 1))
  change stageEndpoint (kmswStage (codeExtend c) (t - 1))
    ((kmswStageLRDartRun (codeExtend c) (t - 1)).head _) = _
  simp only [kmswStageLRDartRun, stageDarts, List.head_map, List.head_attach,
    stageEndpoint, List.head_reverse, ↓reduceIte]

private theorem stoppedRightCoordinate_step_abs (w : ℕ → Fin 3) (i : ℕ) :
    |DirectedDistances.KMSW.R w (i + 1) - DirectedDistances.KMSW.R w i| ≤ 1 := by
  have hs : DirectedDistances.KMSW.R w (i + 1) =
      DirectedDistances.KMSW.R w i + (lazyTwoDimensionalStep (w i)).2 :=
    Finset.sum_range_succ _ _
  rw [hs, add_sub_cancel_left]
  generalize w i = c
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

private theorem stoppedRightHit_record (w : ℕ → Fin 3) (s : ℕ) (hs : 1 ≤ s)
    (hhit : ∃ k, DirectedDistances.KMSW.R w k = -(s : ℤ)) :
    0 < Nat.find hhit ∧ ∀ j < Nat.find hhit,
      DirectedDistances.KMSW.R w (Nat.find hhit) < DirectedDistances.KMSW.R w j := by
  have hc := (strict_running_minimum_iff_first_hit (DirectedDistances.KMSW.R w)
    (by simp [DirectedDistances.KMSW.R]) (stoppedRightCoordinate_step_abs w)
    (Nat.find hhit) (Nat.find hhit) (-(s : ℤ)) (by omega) hhit).2
      ⟨le_rfl, Nat.find_spec hhit, rfl⟩
  have hm := Finset.mem_filter.mp hc.1
  exact ⟨(Finset.mem_Icc.mp hm.1).1, hm.2⟩

private theorem stoppedStageLR_append (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    ∃ es, (kmswStage w n).LR = (kmswStage w m).LR ++ es := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨[], (List.append_nil _).symm⟩
  | succ n _ ih =>
    obtain ⟨es, hes⟩ := ih
    obtain ⟨fs, hfs⟩ := kmswStage_LR_succ_eq_append w n
    exact ⟨es ++ fs, by rw [hfs, hes, List.append_assoc]⟩

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
A first hit of level `-s` identifies an endpoint of every LR chain having at
least `s` edges, including its terminal endpoint before that hit -/
theorem stoppedStageLR_contains_firstHit (w : ℕ → Fin 3) (s m : ℕ)
    (hs : 1 ≤ s) (hhit : ∃ k, DirectedDistances.KMSW.R w k = -(s : ℤ))
    (hlen : s ≤ (kmswStage w m).LR.length) :
    ∃ e ∈ (kmswStage w m).LR,
      (kmswStage w m).west e = activeInitial w (Nat.find hhit) ∨
        (kmswStage w m).east e = activeInitial w (Nat.find hhit) := by
  classical
  obtain ⟨hqpos, hrec⟩ := stoppedRightHit_record w s hs hhit
  by_cases hqm : Nat.find hhit ≤ m
  · have he : act w (Nat.find hhit) ∈ (kmswStage w m).LR := by
      rw [kmswStage_LR_eq]
      exact List.mem_map.mpr ⟨Nat.find hhit, List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega), decide_eq_true hrec⟩, rfl⟩
    refine ⟨act w (Nat.find hhit), he, Or.inl ?_⟩
    exact ((kmswStage_endpoints_stable w hqm
      (act_lt_nextEdge w le_rfl)).1).trans
        (CutConverse.activeInitial_eq w (Nat.find hhit)).symm
  · let p := Nat.find hhit - 1
    have hq : Nat.find hhit = p + 1 := by dsimp [p]; omega
    have hp : m ≤ p := by dsimp [p]; omega
    have hlevel := Nat.find_spec hhit
    have hprev := hrec p (by omega)
    have hcoord : DirectedDistances.KMSW.R w (p + 1) =
        DirectedDistances.KMSW.R w p + (lazyTwoDimensionalStep (w p)).2 :=
      Finset.sum_range_succ _ _
    have hcode : w p = 2 := by
      rw [hq] at hprev
      generalize hc : w p = c at hcoord
      fin_cases c <;> norm_num [lazyTwoDimensionalStep] at hcoord ⊢ <;> omega
    have hprevlevel : DirectedDistances.KMSW.R w p = -(s : ℤ) + 1 := by
      rw [hcode, lazyTwoDimensionalStep_two] at hcoord
      dsimp only at hcoord
      rw [hq] at hlevel
      omega
    have hmin : minR w p = -(s : ℤ) + 1 := by
      obtain ⟨j, hj, hval⟩ := runningMin_attained (DirectedDistances.KMSW.R w) p
      have hlow := hrec j (by omega)
      have hupper := runningMin_le (DirectedDistances.KMSW.R w) p p le_rfl
      change minR w p = DirectedDistances.KMSW.R w j at hval
      change minR w p ≤ DirectedDistances.KMSW.R w p at hupper
      omega
    have hur : (kmswStage w p).UR = [] := by
      apply List.length_eq_zero_iff.mp
      have h := kmswStage_UR_length w p
      rw [hmin, hprevlevel] at h
      omega
    have hpLen : (kmswStage w p).LR.length = s := by
      have h := kmswStage_LR_length w p
      rw [hmin] at h
      omega
    obtain ⟨es, hes⟩ := stoppedStageLR_append w hp
    have hesLen := congrArg List.length hes
    simp only [List.length_append] at hesLen
    have hesNil : es = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hesNil, List.append_nil] at hes
    have hne := kmswStage_LR_nonempty w m
    let e := (kmswStage w m).LR.getLast hne
    have hem : e ∈ (kmswStage w m).LR := List.getLast_mem hne
    have heBound := stageRun_edge_bound w m e (Or.inr hem)
    have htip := (kmswStage_boundary_chain_invariant w p).2.2.2.2.2.2
      (kmswStage_LR_nonempty w p) hur
    have htip' : (kmswStage w p).east (act w p) = (kmswStage w p).east e := by
      simpa only [hes, act, e] using htip
    have hnew : activeInitial w (Nat.find hhit) =
        (kmswStage w p).east (act w p) := by
      rw [hq, CutConverse.activeInitial_eq]
      simp [kmswStage, kmswStep, hcode, kmswCodeStep, kmswStepOfStep,
        hur, State.addEdge, act]
    refine ⟨e, hem, Or.inr ?_⟩
    exact ((kmswStage_endpoints_stable w hp heBound).2).symm.trans
      (htip'.symm.trans hnew.symm)

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Every endpoint of an LR edge is represented on the finite base right path -/
theorem stoppedWalkClassBase_LR_endpoint {ell R t : ℕ}
    (ht : 1 ≤ t) (c : KMSWWalkClass ell R t) (v : ℕ)
    (hv : ∃ e ∈ (kmswStage (codeExtend c) (t - 1)).LR,
      (kmswStage (codeExtend c) (t - 1)).west e = v ∨
        (kmswStage (codeExtend c) (t - 1)).east e = v) :
    ∃ x ∈ (kmswWalkClassBase ht c).rightPath.vertices,
      (stageMapVertex (codeExtend c) (t - 1) x).id = v := by
  let w := codeExtend c
  let m := t - 1
  let B := kmswWalkClassBase ht c
  obtain ⟨e, he, hv⟩ := hv
  have heb := stageRun_edge_bound w m e (Or.inr he)
  let ef : Fin (kmswStage w m).nextEdge := ⟨e, heb⟩
  have hd : (ef, true) ∈ kmswStageLRDartRun w m := by
    unfold kmswStageLRDartRun
    apply (stageDarts_mem (kmswStage w m) (kmswStage w m).LR.reverse
      true _ (ef, true)).2
    refine ⟨e, List.mem_reverse.mpr he, ?_⟩
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  rw [← stoppedWalkClassBase_rightPath_darts ht c] at hd
  obtain ⟨d, hd, hflip⟩ := List.mem_map.mp hd
  have hdP : d ∈ B.rightPath.darts := List.mem_reverse.mp hd
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hdP
  have hstep := B.rightPath.edge_step j
  rw [hj] at hstep
  have hdEq : d = (ef, false) := by
    apply (edgeFlip (kmswStage w m).nextEdge).injective
    exact hflip
  have hjR : j.val < R := by simpa only [B.rightPath.darts_length] using j.isLt
  let jv : Fin B.rightPath.vertices.length :=
    ⟨j.val, by rw [B.rightPath.vertices_length]; omega⟩
  let jv' : Fin B.rightPath.vertices.length :=
    ⟨j.val + 1, by rw [B.rightPath.vertices_length]; omega⟩
  rcases hv with hv | hv
  · refine ⟨B.rightPath.vertices.get jv, List.get_mem _ _, ?_⟩
    rw [hstep.2.2.1, hdEq]
    exact hv
  · refine ⟨B.rightPath.vertices.get jv', List.get_mem _ _, ?_⟩
    rw [hstep.2.2.2, hdEq]
    exact hv

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
An LR endpoint in the hatted stage gives a right-boundary index of the stopped -/
theorem stoppedRightBoundaryPresentPrefunctor_LR_endpoint
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (R ell t : ℕ)
    (q : RightVertexMarkedBoltzmannSpace R) (ht : 1 ≤ t)
    (c : KMSWWalkClass ell R t)
    (hclass : q.1 = ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩)
    (hprefix : ∀ i : Fin (t - 1), c.val i = hatCodes w h i.val) (v : ℕ)
    (hv : ∃ e ∈ (kmswStage (hatCodes w h) (t - 1)).LR,
      (kmswStage (hatCodes w h) (t - 1)).west e = v ∨
        (kmswStage (hatCodes w h) (t - 1)).east e = v) :
    ∃ i : Fin (R + 1),
      (stoppedRightBoundaryPresentPrefunctor w h R ell t q ht c hclass hprefix).obj
        (rightBoundaryVertex q i) = ⟨hatAllVertexMap w h (t - 1) v⟩ := by
  classical
  rcases q with ⟨q₁, mark⟩
  rcases q₁ with ⟨ellQ, q₂⟩
  rcases q₂ with ⟨tQ, classQ⟩
  change (⟨ellQ, ⟨tQ, classQ⟩⟩ : AllBoltzmannSpace R) =
    ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ at hclass
  cases hclass
  let m := t - 1
  let qRep := (kmswToMapIsoClass ht c).out
  have hmk : KMSWMapIsoClass.mk (kmswWalkClassRep ht c) =
      KMSWMapIsoClass.mk qRep := by
    calc
      KMSWMapIsoClass.mk (kmswWalkClassRep ht c) = kmswToMapIsoClass ht c := rfl
      _ = KMSWMapIsoClass.mk qRep := (Quotient.out_eq _).symm
  have hbase : Nonempty (BipolarBoundaryBaseIso
      (kmswWalkClassRep ht c).B qRep.B) :=
    (KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hmk
  let I : BipolarBoundaryBaseIso qRep.B (kmswWalkClassBase ht c) :=
    (Classical.choice hbase).symm.trans (kmswWalkClassRep_baseIso ht c)
  have hcodes : ∀ i < m, codeExtend c i = hatCodes w h i := by
    intro i hi
    rw [codeExtend_of_lt c i hi]
    exact hprefix ⟨i, hi⟩
  have hstage := kmswStage_eq_of_prefix (codeExtend c) (hatCodes w h) m hcodes
  have hv' : ∃ e ∈ (kmswStage (codeExtend c) m).LR,
      (kmswStage (codeExtend c) m).west e = v ∨
        (kmswStage (codeExtend c) m).east e = v := by
    rw [hstage]
    exact hv
  obtain ⟨x, hx, hlabel⟩ := stoppedWalkClassBase_LR_endpoint ht c v hv'
  have hp : I.transportPath qRep.B.rightPath = (kmswWalkClassBase ht c).rightPath := by
    apply SimpleDirectedDartPath.eq_of_darts_eq
    rw [BipolarBoundaryBaseIso.transportPath_darts, I.rightDarts]
  have hverts : qRep.B.rightPath.vertices.map I.vertexEquiv =
      (kmswWalkClassBase ht c).rightPath.vertices :=
    congrArg SimpleDirectedDartPath.vertices hp
  rw [← hverts] at hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hy
  have hjR : j.val < R + 1 := by
    simpa only [qRep.B.rightPath.vertices_length] using j.isLt
  refine ⟨⟨j.val, hjR⟩, ?_⟩
  change (⟨hatAllVertexMap w h m
      (stageMapVertex (codeExtend c) m
        (I.vertexEquiv (qRep.B.rightPath.vertices.get j))).id⟩ : PresentVertex w) = _
  rw [hj, hyx, hlabel]

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
Each positive source boundary vertex through level `R` occurs on the stopped -/
theorem stoppedRightBoundaryPresentPrefunctor_boundary_vertex
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (R ell t : ℕ)
    (q : RightVertexMarkedBoltzmannSpace R) (ht : 1 ≤ t)
    (c : KMSWWalkClass ell R t)
    (hclass : q.1 = ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩)
    (hprefix : ∀ i : Fin (t - 1), c.val i = hatCodes w h i.val)
    (hb : BoundaryHitWitnesses w) (s : ℕ) (hs : 1 ≤ s) (hsR : s ≤ R) :
    ∃ i : Fin (R + 1),
      (stoppedRightBoundaryPresentPrefunctor w h R ell t q ht c hclass hprefix).obj
        (rightBoundaryVertex q i) = boundaryPresentVertex w hb (s : ℤ) := by
  have hcodes : ∀ i < t - 1, codeExtend c i = hatCodes w h i := by
    intro i hi
    rw [codeExtend_of_lt c i hi]
    exact hprefix ⟨i, hi⟩
  have hstage := kmswStage_eq_of_prefix (codeExtend c) (hatCodes w h) (t - 1) hcodes
  have hlen : (kmswStage (hatCodes w h) (t - 1)).LR.length = R := by
    rw [← hstage]
    exact (kmswWalkClassMap_mem_sourceClass ht c).2.2.2.2.2.2.2.2.2.1
  let qhit := hattedRightHitTime w h s hs
  have hv : ∃ e ∈ (kmswStage (hatCodes w h) (t - 1)).LR,
      (kmswStage (hatCodes w h) (t - 1)).west e =
          activeInitial (hatCodes w h) qhit ∨
        (kmswStage (hatCodes w h) (t - 1)).east e =
          activeInitial (hatCodes w h) qhit :=
    stoppedStageLR_contains_firstHit (hatCodes w h) s (t - 1) hs
      (hattedRightHit_exists w h s hs) (by omega)
  have hvBound : activeInitial (hatCodes w h) qhit <
      (kmswStage (hatCodes w h) (t - 1)).nextVertex := by
    obtain ⟨e, he, heq⟩ := hv
    have heb := stageRun_edge_bound (hatCodes w h) (t - 1) e (Or.inr he)
    have hends := kmswStage_endpoints_lt_nextVertex (hatCodes w h) (t - 1) e heb
    rcases heq with heq | heq
    · rw [← heq]
      exact hends.1
    · rw [← heq]
      exact hends.2
  obtain ⟨i, hi⟩ := stoppedRightBoundaryPresentPrefunctor_LR_endpoint
    w h R ell t q ht c hclass hprefix (activeInitial (hatCodes w h) qhit) hv
  have hident := (hattedRightHitTime_isLeast_sourceVertex w h hb s hs).1
  change hatLimitVertexMap w h (activeInitial (hatCodes w h) qhit) =
    boundaryVertex w hb (s : ℤ) at hident
  rw [hatLimitVertexMap_eq_stage w h (t - 1) _ hvBound] at hident
  exact ⟨i, hi.trans (congrArg PresentVertex.mk hident)⟩

/-- Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper result.
Once the stopped map's source and right-boundary endpoint are identified, the
infinite-map lower bound transfers by path inclusion. -/
theorem stoppedCellSDPTransfer_of_identification {R : ℕ}
    (q : RightVertexMarkedBoltzmannSpace R) (w : ℕ → Fin 3) (c : ℕ∞)
    (F : Prefunctor (MapVertex q.1.2.2.out.B.map) (PresentVertex w))
    (i : Fin (R + 1)) (x y : PresentVertex w)
    (hx : F.obj q.1.2.2.out.B.source = x)
    (hy : F.obj (rightBoundaryVertex q i) = y)
    (hc : c ≤ DirectedDistances.sdp x y) :
    c ≤ presentDartSDP q.1.2.2.out.B.map q.1.2.2.out.B.source
      (rightBoundaryVertex q i) := by
  exact hc.trans (stoppedRightBoundarySDP_ge_of_prefunctor q w F i x y hx hy)

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The complete stopped right-boundary transfer implication -/
theorem stoppedRightBoundaryTransfer :
    ∀ (ω : ℕ → Fin 3) (R : ℕ) (hR : 1 ≤ R)
      (_h : HasFlowLineHits (fun i => ω (i + 1)))
      (hb : BoundaryHitWitnesses (fun i => ω (i + 1)))
      (n s : ℕ) (c : ℕ∞),
      n < boundaryHitTime (fun i => ω (i + 1)) hb (R : ℤ) →
      1 ≤ s → s ≤ R →
      (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
        (kmswStage (fun i => ω (i + 1)) n).west e =
            boundaryVertex (fun i => ω (i + 1)) hb (s : ℤ) ∨
          (kmswStage (fun i => ω (i + 1)) n).east e =
            boundaryVertex (fun i => ω (i + 1)) hb (s : ℤ)) →
      c ≤ DirectedDistances.sdp
        (boundaryPresentVertex (fun i => ω (i + 1)) hb 0)
        (boundaryPresentVertex (fun i => ω (i + 1)) hb (s : ℤ)) →
      let q := stoppedMarked R hR (quadrantHatWalk ω)
      ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map)
          (PresentVertex (fun i => ω (i + 1))),
        Function.Injective F.obj ∧
          F.obj q.1.2.2.out.B.source =
            boundaryPresentVertex (fun i => ω (i + 1)) hb 0 ∧
          ∃ i : Fin (R + 1),
            F.obj (rightBoundaryVertex q i) =
              boundaryPresentVertex (fun i => ω (i + 1)) hb (s : ℤ) ∧
            c ≤ presentDartSDP q.1.2.2.out.B.map q.1.2.2.out.B.source
              (rightBoundaryVertex q i) := by
  intro ω R hR h hb n s c _hn hs hsR _hstage hc
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let q := stoppedMarked R hR (quadrantHatWalk ω)
  obtain ⟨ht, ell, word, hclass, hprefix⟩ :=
    quadrantHatWalk_stoppedMarked_value_with_prefix ω R hR h hb
  let t := hattedRightVertexHitTime w h hb R hR
  let F := stoppedRightBoundaryPresentPrefunctor w h R ell t q ht word hclass hprefix
  have hF := stoppedRightBoundaryPresentPrefunctor_injective
    w h R ell t q ht word hclass hprefix
  have hsource := stoppedRightBoundaryPresentPrefunctor_source
    w h R ell t q ht word hclass hprefix hb
  obtain ⟨i, hi⟩ := stoppedRightBoundaryPresentPrefunctor_boundary_vertex
    w h R ell t q ht word hclass hprefix hb s hs hsR
  exact ⟨F, hF, hsource, i, hi,
    stoppedCellSDPTransfer_of_identification q w c F i
      (boundaryPresentVertex w hb 0) (boundaryPresentVertex w hb (s : ℤ))
      hsource hi hc⟩

end DirectedDistances.PaperProofs.Section7
