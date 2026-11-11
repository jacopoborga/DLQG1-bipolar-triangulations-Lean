module

public import DirectedDistances.PaperProofs.Section7.CellLDPUpperAssembly
public import DirectedDistances.PaperProofs.Section7.HitCoupling
public import DirectedDistances.PaperProofs.Section7.UIQBOTBoltzmannGeometricFinal
public import DirectedDistances.KMSW.QuadKMSWHatAllStages
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.StageDirectedMapPathLengths
public import DirectedDistances.Recursive.LeftStationaryBusemann
import DirectedDistances.RandomWalk.CellSDPLowerBdy
import DirectedDistances.PaperProofs.Section7.CellLDPUpperPathwise
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Supporting lemmas for paper labels `lem-boltzmann-ldp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory Quiver Filter Topology
open DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.RandomWalk DirectedDistances.Recursive ProbabilityTheory
open DirectedDistances.PlanarMap

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym; not a paper result.
This combines the failure probabilities of two -/
theorem probability_intersection_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H C : Set Ω) (hH : MeasurableSet H) (hC : MeasurableSet C)
    (b c : ℝ) (hb : 1 - b ≤ μ.real H) (hc : 1 - c ≤ μ.real C) :
    1 - (b + c) ≤ μ.real (H ∩ C) := by
  have hu := measureReal_union_le (μ := μ) Hᶜ Cᶜ
  have hcomp := measureReal_compl (μ := μ) ((hH.inter hC))
  rw [probReal_univ] at hcomp
  have hsets : (H ∩ C)ᶜ = Hᶜ ∪ Cᶜ := by
    simp only [Set.compl_inter]
  rw [hsets] at hcomp
  rw [measureReal_compl hH, measureReal_compl hC, probReal_univ] at hu
  linarith only [hu, hcomp, hb, hc]

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The source right-boundary hit has a quadratic time tail -/
theorem iidSourceRightHitByTime_probability
    (r N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    1 - 4 * (r : ℝ) / Real.sqrt N ≤
      iidCodeMeasure.real {ω | ∃ k ≤ N,
        R (fun i => ω (i + 1)) k = -(r : ℤ)} := by
  have hR (ω : ℕ → Fin 3) (k : ℕ) :
      R (fun i => ω (i + 1)) k = (codeWalk ω k).2 := by
    simp [R, codeWalk, Prod.snd_sum]
  have hiff (ω : ℕ → Fin 3) :
      (∃ k ≤ N, (codeWalk ω k).2 = -(r : ℤ)) ↔
        codeSndFirstHit (-(r : ℤ)) ω ≤ (N : ℕ∞) := by
    by_cases hx : ∃ k, (codeWalk ω k).2 = -(r : ℤ)
    · have ht : codeSndFirstHit (-(r : ℤ)) ω = (Nat.find hx : ℕ∞) := by
        simp [codeSndFirstHit, hx]
      rw [ht]
      constructor
      · rintro ⟨k, hk, he⟩
        have hmin := Nat.find_min' hx he
        exact_mod_cast hmin.trans hk
      · intro h
        have h' : Nat.find hx ≤ N := by exact_mod_cast h
        exact ⟨Nat.find hx, h', Nat.find_spec hx⟩
    · have ht : codeSndFirstHit (-(r : ℤ)) ω = ⊤ := by
        simp only [codeSndFirstHit, dite_eq_right hx]
      rw [ht]
      constructor
      · rintro ⟨k, hk, he⟩
        exact (hx ⟨k, he⟩).elim
      · intro h
        simp at h
  have hset : {ω | ∃ k ≤ N, R (fun i => ω (i + 1)) k = -(r : ℤ)} =
      {ω | codeSndFirstHit (-(r : ℤ)) ω ≤ (N : ℕ∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    simp_rw [hR]
    exact hiff ω
  rw [hset]
  exact codeSndFirstHit_le_prob_ge r N hr hN

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. A finite LDP supremum bounds each path length -/
theorem stagePathLength_le_of_ldpSup_le
    {w : ℕ → Fin 3} {n K : ℕ} {a b : StagePresentVertex w n}
    (hfinite : BddAbove (pathLengths a b))
    (hK : ldpSup a b ≤ (K : WithBot ℕ)) (p : Path a b) :
    (p.length : WithBot ℕ) ≤ (K : WithBot ℕ) := by
  have himage : BddAbove
      ((fun k : ℕ => (k : WithBot ℕ)) '' pathLengths a b) := by
    obtain ⟨N, hN⟩ := hfinite
    refine ⟨(N : WithBot ℕ), ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact WithBot.coe_le_coe.mpr (hN hk)
  have hmem : (p.length : WithBot ℕ) ∈
      (fun k : ℕ => (k : WithBot ℕ)) '' pathLengths a b := by
    exact ⟨p.length, ⟨p, rfl⟩, rfl⟩
  have hp : (p.length : WithBot ℕ) ≤ ldpSup a b := by
    exact le_csSup himage hmem
  exact hp.trans hK

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. Paths in a fixed KMSW stage have bounded length -/
theorem stagePathLengths_bddAbove
    (w : ℕ → Fin 3) (n : ℕ) (a b : StagePresentVertex w n)
    (ha : a.id < (kmswStage w n).nextVertex)
    (hb : b.id < (kmswStage w n).nextVertex) :
    BddAbove (pathLengths a b) := by
  classical
  let M := kmswStageDirectedMap w n
  let u : MapVertex M := (stageVertexEquiv w n).symm ⟨a.id, ha⟩
  let v : MapVertex M := (stageVertexEquiv w n).symm ⟨b.id, hb⟩
  have hu0 : stageMapVertex w n u = a := by
    apply congrArg (StagePresentVertex.mk (w := w) (n := n))
    simp only [u, Equiv.apply_symm_apply]
  have hv0 : stageMapVertex w n v = b := by
    apply congrArg (StagePresentVertex.mk (w := w) (n := n))
    simp only [v, Equiv.apply_symm_apply]
  have hu : a = stageMapVertex w n u := hu0.symm
  have hv : b = stageMapVertex w n v := hv0.symm
  refine ⟨M.toCombinatorialMap.numVertices, ?_⟩
  rintro k ⟨p, rfl⟩
  have hpath : ∃ q : Path (stageMapVertex w n u) (stageMapVertex w n v),
      q.length = p.length := by
    rw [← hu, ← hv]
    exact ⟨p, rfl⟩
  obtain ⟨P⟩ := (stageMap_path_iff w n p.length u v).2 hpath
  have hvertices := P.vertices_nodup.length_le_card
  rw [P.vertices_length] at hvertices
  have hcard : p.length + 1 ≤ M.toCombinatorialMap.numVertices := by
    change p.length + 1 ≤ Fintype.card (MapVertex M)
    exact hvertices
  exact (Nat.le_succ p.length).trans hcard

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The finite-stage LDP bound controls every path -/
theorem stagePathLength_le_of_ldpSup_le_of_vertices
    (w : ℕ → Fin 3) (n K : ℕ) (a b : StagePresentVertex w n)
    (ha : a.id < (kmswStage w n).nextVertex)
    (hb : b.id < (kmswStage w n).nextVertex)
    (hK : ldpSup a b ≤ (K : WithBot ℕ)) (p : Path a b) :
    (p.length : WithBot ℕ) ≤ (K : WithBot ℕ) :=
  stagePathLength_le_of_ldpSup_le (stagePathLengths_bddAbove w n a b ha hb) hK p




theorem hatted_stage_pathLengths_subset_aligned
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (a b : StagePresentVertex (hatCodes w h) m) :
    pathLengths a b ⊆ pathLengths
      (⟨hatAllVertexMap w h m a.id⟩ :
        StagePresentVertex w (quadrantRStageTime w h m))
      (⟨hatAllVertexMap w h m b.id⟩ :
        StagePresentVertex w (quadrantRStageTime w h m)) := by
  let F : Prefunctor (StagePresentVertex (hatCodes w h) m)
      (StagePresentVertex w (quadrantRStageTime w h m)) := {
    obj := fun v => ⟨hatAllVertexMap w h m v.id⟩
    map := fun {u v} e => by
      have hp := hatAll_present w h m e.val e.property.1 e.property.2.1
      refine ⟨hatAllEdgeMap w h m e.val, hp.1, hp.2.1, ?_, ?_⟩
      · rw [hp.2.2.1, e.property.2.2.1]
      · rw [hp.2.2.2, e.property.2.2.2]
  }
  rintro _ ⟨p, rfl⟩
  refine ⟨F.mapPath p, ?_⟩
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]





theorem hatted_first_hit_pathLengths_subset_sourceStage
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r N : ℕ) (hr : 1 ≤ r)
    (hN : boundaryHitTime w hb (r : ℤ) ≤ N)
    (a b : StagePresentVertex (hatCodes w h)
      (hattedRightVertexHitTime w h hb r hr)) :
    pathLengths a b ⊆ pathLengths
      (⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) a.id⟩ :
        StagePresentVertex w N)
      (⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) b.id⟩ :
        StagePresentVertex w N) := by
  let m := hattedRightVertexHitTime w h hb r hr
  have hmn : quadrantRStageTime w h m ≤ N := by
    calc
      quadrantRStageTime w h m = sourceQuadrantS w h m :=
        quadrantRStageTime_eq_sourceQuadrantS w h m
      _ = boundaryHitTime w hb (r : ℤ) := by
        symm
        exact sourceHitTime_eq_sourceHattedRightVertexHit w h hb r hr
      _ ≤ N := hN
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, hq⟩ := hatted_stage_pathLengths_subset_aligned w h m a b ⟨p, rfl⟩
  refine ⟨(kmswStageInclusion w (quadrantRStageTime w h m) N hmn).mapPath q,
    ?_⟩
  calc
    _ = q.length := kmswStageInclusion_length w (quadrantRStageTime w h m) N hmn q
    _ = p.length := hq





theorem hatted_first_hit_ldpSup_le_of_sourceStage_path_bound
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r N K : ℕ) (hr : 1 ≤ r)
    (hN : boundaryHitTime w hb (r : ℤ) ≤ N)
    (a b : StagePresentVertex (hatCodes w h)
      (hattedRightVertexHitTime w h hb r hr))
    (hK : ∀ q : Path
      (⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) a.id⟩ :
        StagePresentVertex w N)
      (⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) b.id⟩ :
        StagePresentVertex w N), q.length ≤ K) :
    ldpSup a b ≤ (K : WithBot ℕ) := by
  unfold ldpSup
  apply csSup_le'
  rintro _ ⟨k, ⟨p, rfl⟩, rfl⟩
  obtain ⟨q, hq⟩ := hatted_first_hit_pathLengths_subset_sourceStage
    w h hb r N hr hN a b ⟨p, rfl⟩
  rw [← hq]
  exact WithBot.coe_le_coe.mpr (hK q)

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The stopped hatted stage embeds in the source stage -/
theorem hatted_first_hit_prevStage_ldpSup_le_of_sourceStage_path_bound
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r N K : ℕ) (hr : 1 ≤ r)
    (hN : boundaryHitTime w hb (r : ℤ) ≤ N)
    (a b : StagePresentVertex (hatCodes w h)
      (hattedRightVertexHitTime w h hb r hr - 1))
    (hK : ∀ q : Path
      (⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) a.id⟩ :
        StagePresentVertex w N)
      (⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) b.id⟩ :
        StagePresentVertex w N), q.length ≤ K) :
    ldpSup a b ≤ (K : WithBot ℕ) := by
  let m := hattedRightVertexHitTime w h hb r hr
  have hmn : m - 1 ≤ m := Nat.sub_le m 1
  let I := kmswStageInclusion (hatCodes w h) (m - 1) m hmn
  let a' : StagePresentVertex (hatCodes w h) m := ⟨a.id⟩
  let b' : StagePresentVertex (hatCodes w h) m := ⟨b.id⟩
  have hpaths : pathLengths a b ⊆ pathLengths a' b' := by
    rintro _ ⟨p, rfl⟩
    refine ⟨I.mapPath p, ?_⟩
    exact kmswStageInclusion_length (hatCodes w h) (m - 1) m hmn p
  have hsource : pathLengths a' b' ⊆ pathLengths
      (⟨hatAllVertexMap w h m a'.id⟩ :
        StagePresentVertex w (quadrantRStageTime w h m))
      (⟨hatAllVertexMap w h m b'.id⟩ :
        StagePresentVertex w (quadrantRStageTime w h m)) := by
    exact hatted_stage_pathLengths_subset_aligned w h m a' b'
  have hsubset : pathLengths a b ⊆ pathLengths
      (⟨hatAllVertexMap w h m a.id⟩ : StagePresentVertex w N)
      (⟨hatAllVertexMap w h m b.id⟩ : StagePresentVertex w N) := by
    intro k hk
    obtain ⟨q, hq⟩ := hpaths hk
    obtain ⟨p, hp⟩ := hsource ⟨q, hq⟩
    have hmnN : quadrantRStageTime w h m ≤ N := by
      calc
        quadrantRStageTime w h m = sourceQuadrantS w h m :=
          quadrantRStageTime_eq_sourceQuadrantS w h m
        _ = boundaryHitTime w hb (r : ℤ) := by
          symm
          exact sourceHitTime_eq_sourceHattedRightVertexHit w h hb r hr
        _ ≤ N := hN
    let J := kmswStageInclusion w (quadrantRStageTime w h m) N hmnN
    refine ⟨J.mapPath p, ?_⟩
    simpa only [a', b', J, kmswStageInclusion] using
      (kmswStageInclusion_length w (quadrantRStageTime w h m) N hmnN p).trans hp
  unfold ldpSup
  apply csSup_le'
  rintro _ ⟨k, ⟨p, rfl⟩, rfl⟩
  obtain ⟨q, hq⟩ := hsubset ⟨p, rfl⟩
  rw [← hq]
  exact WithBot.coe_le_coe.mpr (hK q)

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The source-stage LDP bound transfers to the stopped hatted -/
theorem hatted_first_hit_prevStage_ldpSup_le_of_sourceStage_ldpSup_bound
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r N K : ℕ) (hr : 1 ≤ r)
    (hN : boundaryHitTime w hb (r : ℤ) ≤ N)
    (a b : StagePresentVertex (hatCodes w h)
      (hattedRightVertexHitTime w h hb r hr - 1))
    (ha : hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) a.id <
      (kmswStage w N).nextVertex)
    (hbb : hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) b.id <
      (kmswStage w N).nextVertex)
    (hK : ldpSup
      (⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) a.id⟩ :
        StagePresentVertex w N)
      ⟨hatAllVertexMap w h (hattedRightVertexHitTime w h hb r hr) b.id⟩ ≤
      (K : WithBot ℕ)) :
    ldpSup a b ≤ (K : WithBot ℕ) := by
  apply hatted_first_hit_prevStage_ldpSup_le_of_sourceStage_path_bound
    w h hb r N K hr hN a b
  intro q
  exact WithBot.coe_le_coe.mp
    (stagePathLength_le_of_ldpSup_le_of_vertices w N K _ _ ha hbb hK q)

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. A uniform source-stage bound applies to the stopped hatted -/
theorem hatted_first_hit_prevStage_ldpSup_le_of_sourceStage_uniform_bound
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w)
    (r N K : ℕ) (hr : 1 ≤ r)
    (hN : boundaryHitTime w hb (r : ℤ) ≤ N)
    (hgood : ∀ x y : StagePresentVertex w N,
      x.id < (kmswStage w N).nextVertex →
      y.id < (kmswStage w N).nextVertex →
      ldpSup x y ≤ (K : WithBot ℕ)) :
    ldpSup (⟨0⟩ : StagePresentVertex (hatCodes w h)
        (hattedRightVertexHitTime w h hb r hr - 1))
      ⟨(kmswStage (hatCodes w h)
        (hattedRightVertexHitTime w h hb r hr - 1)).east
          (kmswStage (hatCodes w h)
            (hattedRightVertexHitTime w h hb r hr - 1)).active⟩ ≤
      (K : WithBot ℕ) := by
  let m := hattedRightVertexHitTime w h hb r hr
  have hmn : quadrantRStageTime w h m ≤ N := by
    calc
      quadrantRStageTime w h m = sourceQuadrantS w h m :=
        quadrantRStageTime_eq_sourceQuadrantS w h m
      _ = boundaryHitTime w hb (r : ℤ) := by
        symm
        exact sourceHitTime_eq_sourceHattedRightVertexHit w h hb r hr
      _ ≤ N := hN
  have hmstep : m - 1 ≤ m := Nat.sub_le m 1
  have hact : act (hatCodes w h) (m - 1) <
      (kmswStage (hatCodes w h) (m - 1)).nextEdge :=
    act_lt_nextEdge (hatCodes w h) (Nat.le_refl (m - 1))
  have hlocal : (kmswStage (hatCodes w h) (m - 1)).east
      (kmswStage (hatCodes w h) (m - 1)).active <
        (kmswStage (hatCodes w h) m).nextVertex := by
    exact ((kmswStage_endpoints_lt_nextVertex (hatCodes w h) (m - 1)
      (act (hatCodes w h) (m - 1)) hact).2).trans_le
        (CutConverse.nextVertex_mono (hatCodes w h) hmstep)
  have hsource := (hatAll_sim w h m).incidenceSim.vertex_bound _ hlocal
  have hsourceN : hatAllVertexMap w h m
      ((kmswStage (hatCodes w h) (m - 1)).east
        (kmswStage (hatCodes w h) (m - 1)).active) <
      (kmswStage w N).nextVertex :=
    hsource.trans_le (CutConverse.nextVertex_mono w hmn)
  have hroot : 0 < (kmswStage w N).nextVertex := by
    have hp := kmswStage_endpoints_lt_nextVertex w N 0
      (initial_edge_present w N).1
    rw [(initial_edge_endpoints w N).1] at hp
    exact hp.1
  have hrootN : hatAllVertexMap w h m 0 < (kmswStage w N).nextVertex := by
    rw [hatAllVertexMap_root]
    exact hroot
  have hK := hgood ⟨hatAllVertexMap w h m 0⟩
    ⟨hatAllVertexMap w h m
      ((kmswStage (hatCodes w h) (m - 1)).east
        (kmswStage (hatCodes w h) (m - 1)).active)⟩ hrootN hsourceN
  exact hatted_first_hit_prevStage_ldpSup_le_of_sourceStage_ldpSup_bound
    w h hb r N K hr hN _ _ hrootN hsourceN hK




theorem stoppedClass_ldpLength_le_of_hattedStage_path_bound
    {ℓ r t K : ℕ} (ht : 1 ≤ t) (c : KMSWWalkClass ℓ r t)
    (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hprefix : ∀ i < t - 1, (codeExtend c) i = hatCodes w h i)
    (hbound : ∀ q : Path (⟨0⟩ : StagePresentVertex (hatCodes w h) (t - 1))
      ⟨(kmswStage (codeExtend c) (t - 1)).east
        (kmswStage (codeExtend c) (t - 1)).active⟩, q.length ≤ K) :
    (ldpLengthBase (kmswWalkClassRep ht c).B : WithBot ℕ) ≤ (K : WithBot ℕ) := by
  rw [kmswWalkClassRep_ldpLength_eq_stage ht c]
  have hs := kmswStage_eq_of_prefix (codeExtend c) (hatCodes w h) (t - 1)
    hprefix
  let F : Prefunctor (StagePresentVertex (codeExtend c) (t - 1))
      (StagePresentVertex (hatCodes w h) (t - 1)) := {
    obj := fun v => ⟨v.id⟩
    map := fun {u v} e => ⟨e.val, by simpa only [hs] using e.property⟩
  }
  let a : StagePresentVertex (codeExtend c) (t - 1) := ⟨0⟩
  let b : StagePresentVertex (codeExtend c) (t - 1) :=
    ⟨(kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active⟩
  let a' : StagePresentVertex (hatCodes w h) (t - 1) := ⟨0⟩
  let b' : StagePresentVertex (hatCodes w h) (t - 1) :=
    ⟨(kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active⟩
  have hstart : F.obj a = a' := by
    rfl
  have hlen : ∀ {x y : StagePresentVertex (codeExtend c) (t - 1)}
      (p : Path x y), (F.mapPath p).length = p.length := by
    intro x y p
    induction p with
    | nil => rfl
    | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
  unfold ldpSup
  apply csSup_le'
  rintro _ ⟨k, ⟨p, rfl⟩, rfl⟩
  let q : Path a' b' := hstart ▸ F.mapPath p
  have hq : q.length = p.length := by
    dsimp only [q]
    cases hstart
    exact hlen p
  have hqbound : q.length ≤ K := hbound q
  rw [hq] at hqbound
  exact WithBot.coe_le_coe.mpr hqbound

private theorem measurable_vectorPitmanCodeWalk_conditional :
    Measurable DirectedDistances.RandomWalk.vectorPitmanCodeWalk := by
  change Measurable (fun ω k => vectorPitman (codeWalk ω) k)
  have hL : Measurable (fun ω k => (codeWalk ω k).1) :=
    Measurable.of_eval fun n => ((measurable_pi_apply n).comp measurable_codeWalk).fst
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hL).prodMk
    (((measurable_pi_apply n).comp measurable_codeWalk).snd.add
      ((measurable_globalLazyRunningMinimum n).comp hL))

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The hatted path pushforward is the conditioned walk law -/
theorem iidCodeMeasure_map_quadrantHatWalk_conditional :
    iidCodeMeasure.map DirectedDistances.RandomWalk.quadrantHatWalk =
      conditionedVectorPathLaw 0 0 := by
  have hEq : DirectedDistances.RandomWalk.quadrantHatWalk =ᵐ[iidCodeMeasure]
      (fun ω => DirectedDistances.RandomWalk.vectorPitmanCodeWalk
        ((DirectedDistances.RandomWalk.phaseSplit ω).1)) :=
    DirectedDistances.RandomWalk.iidCodeMeasure_ae_quadrantHatWalk_eq_vectorPitmanCodeWalk
  calc
    iidCodeMeasure.map DirectedDistances.RandomWalk.quadrantHatWalk =
        iidCodeMeasure.map (fun ω => DirectedDistances.RandomWalk.vectorPitmanCodeWalk
          ((DirectedDistances.RandomWalk.phaseSplit ω).1)) := Measure.map_congr hEq
    _ = iidCodeMeasure.map DirectedDistances.RandomWalk.vectorPitmanCodeWalk :=
      DirectedDistances.RandomWalk.map_phaseSplit_fst_comp
        measurable_vectorPitmanCodeWalk_conditional
    _ = conditionedVectorPathLaw 0 0 := DirectedDistances.RandomWalk.map_vectorPitman_codeWalk

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The code decoded from the hatted path is its selected code -/
theorem quadrantHatWalk_pathCode_stream_eq_hatCodes (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    boltzmannKMSWStream (pathCode (quadrantHatWalk ω)) =
      hatCodes (fun i => ω (i + 1)) h := by
  funext i
  dsimp only [boltzmannKMSWStream]
  rw [quadrantHatWalk_eq_interval]
  change pathCode (integrateCodes (hatCodes (fun i => ω (i + 1)) h)) (i + 1) = _
  have hstep : integrateCodes (hatCodes (fun i => ω (i + 1)) h) (i + 1) -
      integrateCodes (hatCodes (fun i => ω (i + 1)) h) i =
        lazyTwoDimensionalStep (hatCodes (fun i => ω (i + 1)) h i) := by
    simp only [integrateCodes, Finset.sum_range_succ]
    abel
  have hdecode := step_pathCode
    (integrateCodes (hatCodes (fun i => ω (i + 1)) h)) i
    (Set.mem_range.mpr ⟨hatCodes (fun i => ω (i + 1)) h i, hstep.symm⟩)
  rw [hstep] at hdecode
  exact lazyTwoDimensionalStep_injective hdecode

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. A stopped class whose code prefix is read from the
`quadrantHatWalk` inherits the corresponding hatted-stage path bound -/
theorem stoppedClass_ldpLength_le_of_quadrantHatWalk_path_bound
    {ℓ r t K : ℕ} (ht : 1 ≤ t) (c : KMSWWalkClass ℓ r t)
    (ω : ℕ → Fin 3) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hprefix : ∀ i < t - 1,
      (codeExtend c) i = pathCode (DirectedDistances.RandomWalk.quadrantHatWalk ω)
        (i + 1))
    (hbound : ∀ q : Path
      (⟨0⟩ : StagePresentVertex (hatCodes (fun i => ω (i + 1)) h) (t - 1))
      ⟨(kmswStage (codeExtend c) (t - 1)).east
        (kmswStage (codeExtend c) (t - 1)).active⟩, q.length ≤ K) :
    (ldpLengthBase (kmswWalkClassRep ht c).B : WithBot ℕ) ≤ (K : WithBot ℕ) := by
  apply stoppedClass_ldpLength_le_of_hattedStage_path_bound ht c
    (fun i => ω (i + 1)) h ?_ hbound
  intro i hi
  have hstream := quadrantHatWalk_pathCode_stream_eq_hatCodes ω h
  simpa only [boltzmannKMSWStream] using (hprefix i hi).trans
    (congrFun hstream i)

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The hatted-walk stopped-mark law is the marked Boltzmann -/
theorem iidCodeMeasure_map_quadrantHatWalk_stoppedMarked
    (r : ℕ) (hr : 1 ≤ r) :
    iidCodeMeasure.map (fun ω =>
      DirectedDistances.KMSW.stoppedMarked r hr
        (DirectedDistances.RandomWalk.quadrantHatWalk ω)) =
      rightVertexMarkedBoltzmannLaw r := by
  change iidCodeMeasure.map
    (DirectedDistances.KMSW.stoppedMarked r hr ∘
      DirectedDistances.RandomWalk.quadrantHatWalk) = _
  rw [← AEMeasurable.map_map_of_aemeasurable
    (measurable_stoppedMarked r hr).aemeasurable
    aemeasurable_quadrantHatWalk,
    iidCodeMeasure_map_quadrantHatWalk_conditional,
    DirectedDistances.KMSW.stoppedMarked_law r hr]

private theorem conditional_process_event_measurable (k : ℕ) (t : ℝ) :
    MeasurableSet {f : ℤ → ℤ | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(f l : ℝ)| ≤ t} := by
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le
    ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
      (measurable_pi_apply l))
    measurable_const

private theorem conditional_cell_good_event_measurable
    (n : ℕ) (ε A : ℝ) :
    MeasurableSet {ω : ℕ → Fin 3 |
      (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
      ∀ l : ℤ,
        |l| ≤ ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
        |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
        |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 4 : ℝ) / 4} := by
  let k := ⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1
  let t := A * (n : ℝ) ^ (3 / 4 : ℝ) / 4
  let S : Set (ℤ → ℤ) := {f | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
    |(f l : ℝ)| ≤ t}
  let E : Set (ℕ → Fin 3) := {ω | busemannLDPMeasurableVersion ω ∈ S}
  let F : Set (ℕ → Fin 3) :=
    {ω | busemannLDPMeasurableVersion (codeShift n ω) ∈ S}
  let B : Set (ℕ → Fin 3) := {ω |
    ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
        A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
    ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
        A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
    ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
        A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
    ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
        A ^ (ε / 2) * Real.sqrt (n : ℝ)}
  have hS : MeasurableSet S := conditional_process_event_measurable k t
  have hm : Measurable busemannLDPMeasurableVersion :=
    measurable_pi_iff.mpr measurable_busemannLDPMeasurableVersion
  have hE : MeasurableSet E := hS.preimage hm
  have hF : MeasurableSet F := hS.preimage (hm.comp (measurable_codeShift n))
  have hB : MeasurableSet B := by
    exact measurableSet_kmswStage_shift n (fun s =>
      (s.UL.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      (s.UR.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      (s.LL.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      (s.LR.length : ℝ) ≤ A ^ (ε / 2) * Real.sqrt (n : ℝ))
  have hEq : {ω : ℕ → Fin 3 |
      (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
      ∀ l : ℤ,
        |l| ≤ ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
        |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
        |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 4 : ℝ) / 4} = B ∩ (E ∩ F) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, E, F, B]
    constructor
    · rintro ⟨hb, hvalues⟩
      refine ⟨hb, ⟨?_, ?_⟩⟩
      · intro l hl hl'
        exact (hvalues l (abs_le.mpr ⟨hl, hl'⟩)).1
      · intro l hl hl'
        exact (hvalues l (abs_le.mpr ⟨hl, hl'⟩)).2
    · rintro ⟨hb, he, hf⟩
      refine ⟨hb, fun l hl => ?_⟩
      have hh := abs_le.mp hl
      exact ⟨he l hh.1 hh.2, hf l hh.1 hh.2⟩
  rw [hEq]
  exact hB.inter (hE.inter hF)

private theorem conditional_source_hit_event_measurable (r N : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 | ∃ k ≤ N,
      R (fun i => ω (i + 1)) k = -(r : ℤ)} := by
  have hR (ω : ℕ → Fin 3) (k : ℕ) :
      R (fun i => ω (i + 1)) k = (codeWalk ω k).2 := by
    simp [R, codeWalk, Prod.snd_sum]
  have hEq : {ω : ℕ → Fin 3 | ∃ k ≤ N,
      R (fun i => ω (i + 1)) k = -(r : ℤ)} =
      ⋃ k : ℕ, {ω | k ≤ N ∧ (codeWalk ω k).2 = -(r : ℤ)} := by
    ext ω
    simp_rw [hR]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [hEq]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases hk : k ≤ N
  · have hm : Measurable (fun ω : ℕ → Fin 3 => (codeWalk ω k).2) :=
      ((measurable_pi_apply k).comp measurable_codeWalk).snd
    have hs : MeasurableSet {ω : ℕ → Fin 3 | (codeWalk ω k).2 = -(r : ℤ)} :=
      (measurableSet_singleton (-(r : ℤ))).preimage hm
    simpa [hk] using hs
  · simp [hk]

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The cell and right-hit estimates hold jointly -/
theorem cellAndHit_intersection_probability_conditional
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        ∀ r : ℕ, 1 ≤ r →
          1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
            4 * (r : ℝ) / Real.sqrt n) ≤
            iidCodeMeasure.real
              ({ω : ℕ → Fin 3 |
                (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
                  ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
                  ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
                  ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
                    A ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
                ∀ l : ℤ,
                  |l| ≤
                    ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
                  |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
                      A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
                  |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
                      A * (n : ℝ) ^ (3 / 4 : ℝ) / 4} ∩
                {ω | ∃ k ≤ n,
                  R (fun i => ω (i + 1)) k = -(r : ℤ)}) := by
  intro ε hε hεlt
  obtain ⟨C, hC, hcell⟩ := cell_ldp_upper_good_event hind
    busemannLDPMeasurableVersion_left_stationary hsym ε hε hεlt
  refine ⟨C, hC, fun n hn A hA r hr => ?_⟩
  exact probability_intersection_lower_bound iidCodeMeasure
    {ω : ℕ → Fin 3 |
      (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
          A ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
      ∀ l : ℤ,
        |l| ≤ ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
        |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
        |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
            A * (n : ℝ) ^ (3 / 4 : ℝ) / 4}
    {ω : ℕ → Fin 3 |
      ∃ k ≤ n, R (fun i => ω (i + 1)) k = -(r : ℤ)}
    (conditional_cell_good_event_measurable n ε A)
    (conditional_source_hit_event_measurable r n)
    (C * A ^ (-(2 / 3 : ℝ) + ε))
    (4 * (r : ℝ) / Real.sqrt n)
    (hcell n hn A hA)
    (iidSourceRightHitByTime_probability r n hr hn)

private theorem cell_event_sourceStage_uniform_bound
    (ω : ℕ → Fin 3) (n : ℕ) (A ε : ℝ)
    (h0 : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (hn : BoundaryHitWitnesses (fun i => ω (n + i + 1)))
    (hfin0 : ∀ v, {e : ℕ | ∃ m,
      e < (kmswStage (fun i => ω (i + 1)) m).nextEdge ∧
        ((kmswStage (fun i => ω (i + 1)) m).west e = v ∨
          (kmswStage (fun i => ω (i + 1)) m).east e = v)}.Finite)
    (hfinn : ∀ v, {e : ℕ | ∃ m,
      e < (kmswStage (fun i => ω (n + i + 1)) m).nextEdge ∧
        ((kmswStage (fun i => ω (n + i + 1)) m).west e = v ∨
          (kmswStage (fun i => ω (n + i + 1)) m).east e = v)}.Finite)
    (hX : IsBoundaryBusemannLDP
      (presentPathLengthsBounded_of_hfin _ hfin0)
      (boundaryPresentVertex _ h0) (busemannLDPMeasurableVersion ω))
    (hXn : IsBoundaryBusemannLDP
      (presentPathLengthsBounded_of_hfin _ hfinn)
      (boundaryPresentVertex _ hn)
      (busemannLDPMeasurableVersion (codeShift n ω)))
    (hUL : ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
      A ^ (ε / 2) * Real.sqrt (n : ℝ))
    (hUR : ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
      A ^ (ε / 2) * Real.sqrt (n : ℝ))
    (hLL : ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
      A ^ (ε / 2) * Real.sqrt (n : ℝ))
    (hLR : ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
      A ^ (ε / 2) * Real.sqrt (n : ℝ))
    (hvalues : ∀ l : ℤ,
      |l| ≤ ((⌈A ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
      |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
          A * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
      |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
          A * (n : ℝ) ^ (3 / 4 : ℝ) / 4)
    :
    ∀ x y : StagePresentVertex (fun i => ω (i + 1)) n,
      x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
      y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
      ldpSup x y ≤
        ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ) := by
  classical
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let T : ℝ := A ^ (ε / 2) * Real.sqrt (n : ℝ)
  let k : ℕ := ⌈T⌉₊ + 1
  let B : ℝ := A * (n : ℝ) ^ (3 / 4 : ℝ) / 4
  have hceil : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
  have hULN : (kmswStage w n).UL.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hUL.trans hceil
  have hURN : (kmswStage w n).UR.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hUR.trans hceil
  have hLLN : (kmswStage w n).LL.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hLL.trans hceil
  have hLRN : (kmswStage w n).LR.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hLR.trans hceil
  have hB0 : ∀ i : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ i →
      i ≤ ((kmswStage w n).LR.length : ℤ) →
      |(busemannLDPMeasurableVersion ω i : ℝ)| ≤ B := by
    intro i hiL hiR
    apply (hvalues i ?_).1
    change |i| ≤ (k : ℤ)
    apply abs_le.mpr
    dsimp only [k]
    constructor <;> omega
  have hBn : ∀ i : ℤ,
      -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ i →
      i ≤ (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) →
      |(busemannLDPMeasurableVersion (codeShift n ω) i : ℝ)| ≤ B := by
    intro i hiL hiR
    apply (hvalues i ?_).2
    change |i| ≤ (k : ℤ)
    apply abs_le.mpr
    dsimp only [k]
    constructor <;> omega
  intro x y hx hy
  unfold ldpSup
  apply csSup_le'
  rintro _ ⟨m, ⟨p, rfl⟩, rfl⟩
  have hp := cell_path_length_le_of_real_busemann_bounds w n h0 hn
    (presentPathLengthsBounded_of_hfin w hfin0)
    (presentPathLengthsBounded_of_hfin (fun i => w (n + i)) hfinn)
    hX hXn B B hB0 hBn x y hx hy p
  apply WithBot.coe_le_coe.mpr
  apply Nat.le_floor
  change (p.length : ℝ) ≤ A * (n : ℝ) ^ (3 / 4 : ℝ)
  dsimp only [B] at hp
  linarith only [hp]

private theorem quadrantHatWalk_hit_time_eq_hatted
    (ω : ℕ → Fin 3) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (r : ℕ) (hr : 1 ≤ r) :
    conditionedSecondCoordinateFirstHit r
        (DirectedDistances.RandomWalk.quadrantHatWalk ω) =
      (hattedRightHitTime (fun i => ω (i + 1)) h r hr : ℕ∞) := by
  classical
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  have hp : DirectedDistances.RandomWalk.quadrantHatWalk ω =
      integrateCodes (hatCodes w h) := by
    rw [DirectedDistances.RandomWalk.quadrantHatWalk_eq_interval ω h]
    rfl
  have hcoord (k : ℕ) :
      (DirectedDistances.RandomWalk.quadrantHatWalk ω k).2 = R (hatCodes w h) k := by
    rw [hp]
    simp [R, integrateCodes, Prod.snd_sum]
  have hhit : ∃ k,
      (DirectedDistances.RandomWalk.quadrantHatWalk ω k).2 = -(r : ℤ) := by
    exact ⟨hattedRightHitTime w h r hr,
      (hcoord (hattedRightHitTime w h r hr)).trans
        (hattedRightHitTime_spec w h r hr)⟩
  have hfind : Nat.find hhit = Nat.find (hattedRightHit_exists w h r hr) := by
    apply Nat.find_congr'
    intro k
    rw [hcoord k]
  unfold conditionedSecondCoordinateFirstHit
  rw [dite_eq_left hhit, hfind]
  rfl

/-- Helper toward Lemma 7.10 (lem-boltzmann-ldp-upper); conditional on hind/hsym;
not a paper result. The cell event and a right hit control the marked stopped -/
theorem boltzmann_ldp_upper_conditional
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
        1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
          {q : RightVertexMarkedBoltzmannSpace r |
            (ldpLengthBase q.1.2.2.out.B : ℝ) ≤
              A * (r : ℝ) ^ (3 / 2 : ℝ)} := by
  classical
  intro δ hδ hδlt
  let ε : ℝ := 1 / 3
  have hε : 0 < ε := by dsimp [ε]; norm_num
  have hεlt : ε < 2 / 3 := by dsimp [ε]; norm_num
  obtain ⟨C, hC, hcell⟩ := cellAndHit_intersection_probability_conditional
    hind hsym ε hε hεlt
  have hlim : Tendsto (fun x : ℝ => C * x ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul C
  have hev : ∀ᶠ x : ℝ in atTop, C * x ^ (-(1 / 3 : ℝ)) < δ / 4 :=
    hlim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 4))
  obtain ⟨a, ha⟩ := (eventually_atTop.1 hev)
  let α : ℝ := max a 2
  have hαa : a ≤ α := le_max_left _ _
  have hα2 : 2 ≤ α := le_max_right _ _
  have hα : 1 < α := by dsimp [α]; exact lt_of_lt_of_le (by norm_num) hα2
  have hαerr : C * α ^ (-(1 / 3 : ℝ)) < δ / 4 := ha α hαa
  let β : ℝ := 8 / δ
  let κ : ℝ := β ^ 2
  let Aout : ℝ := α * (κ + 1) ^ (3 / 4 : ℝ)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ1 : 1 ≤ κ + 1 := by linarith [hκ]
  have hAout : 1 < Aout := by
    have hfac : 1 ≤ (κ + 1) ^ (3 / 4 : ℝ) :=
      Real.one_le_rpow hκ1 (by norm_num)
    dsimp [Aout]
    nlinarith
  refine ⟨Aout, hAout, fun r hr => ?_⟩
  let n : ℕ := ⌈κ * (r : ℝ) ^ 2⌉₊
  have hn : 1 ≤ n := by
    have hr0 : 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have hβ8 : 8 < β := by
      dsimp [β]
      rw [lt_div_iff₀ hδ]
      nlinarith [hδlt]
    have hx : 1 ≤ κ * (r : ℝ) ^ 2 := by
      dsimp [κ]
      nlinarith [hβ8, sq_nonneg (β - 1), sq_nonneg ((r : ℝ) - 1)]
    have hxn : 1 ≤ (n : ℝ) := by
      dsimp [n]
      exact hx.trans (Nat.le_ceil _)
    exact_mod_cast hxn
  have hnlo : κ * (r : ℝ) ^ 2 ≤ (n : ℝ) := by
    dsimp [n]
    exact Nat.le_ceil _
  have hhitScale : 4 * (r : ℝ) / Real.sqrt (n : ℝ) ≤ δ / 2 := by
    have hr0 : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hsq : (β * (r : ℝ)) ^ 2 ≤ (n : ℝ) := by
      dsimp [κ] at hnlo
      nlinarith [hnlo]
    have hroot : β * (r : ℝ) ≤ Real.sqrt (n : ℝ) :=
      (Real.le_sqrt (by positivity) (by positivity)).2 hsq
    have hden : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hquot : (r : ℝ) / Real.sqrt (n : ℝ) ≤ 1 / β := by
      rw [div_le_div_iff₀ hden hβ]
      nlinarith [hroot]
    have hquot' : (r : ℝ) / Real.sqrt (n : ℝ) ≤ β⁻¹ := by
      simpa [one_div] using hquot
    calc
      4 * (r : ℝ) / Real.sqrt (n : ℝ) =
          4 * ((r : ℝ) / Real.sqrt (n : ℝ)) := by ring
      _ ≤ 4 * β⁻¹ := mul_le_mul_of_nonneg_left hquot' (by norm_num)
      _ = δ / 2 := by dsimp [β]; field_simp; ring
  let E : Set (ℕ → Fin 3) := {ω |
    (((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
        α ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
        α ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
        α ^ (ε / 2) * Real.sqrt (n : ℝ) ∧
      ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
        α ^ (ε / 2) * Real.sqrt (n : ℝ)) ∧
    ∀ l : ℤ,
      |l| ≤ ((⌈α ^ (ε / 2) * Real.sqrt (n : ℝ)⌉₊ + 1 : ℕ) : ℤ) →
      |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
          α * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ∧
      |(busemannLDPMeasurableVersion (codeShift n ω) l : ℝ)| ≤
          α * (n : ℝ) ^ (3 / 4 : ℝ) / 4}
  let H : Set (ℕ → Fin 3) := {ω | ∃ k ≤ n,
    R (fun i => ω (i + 1)) k = -(r : ℤ)}
  let T : Set (RightVertexMarkedBoltzmannSpace r) :=
    {q | (ldpLengthBase q.1.2.2.out.B : ℝ) ≤ Aout * (r : ℝ) ^ (3 / 2 : ℝ)}
  have hprob := hcell n hn α hα r hr
  have hprob' : 1 - δ ≤ iidCodeMeasure.real (E ∩ H) := by
    change 1 - (C * α ^ (-(2 / 3 : ℝ) + ε) +
      4 * (r : ℝ) / Real.sqrt n) ≤ iidCodeMeasure.real (E ∩ H) at hprob
    have hexp : -(2 / 3 : ℝ) + ε = -(1 / 3 : ℝ) := by dsimp [ε]; ring
    rw [hexp] at hprob
    have herr : C * α ^ (-(1 / 3 : ℝ)) +
        4 * (r : ℝ) / Real.sqrt n ≤ δ := by linarith [hαerr, hhitScale]
    linarith [hprob, herr]
  let f : (ℕ → Fin 3) → RightVertexMarkedBoltzmannSpace r := fun ω =>
    stoppedMarked r hr (DirectedDistances.RandomWalk.quadrantHatWalk ω)
  have hsub : (E ∩ H) ≤ᵐ[iidCodeMeasure] {ω | f ω ∈ T} := by
    have hclass0 := stoppedMap_stageClass_ae r hr
    have hwalklaw := iidCodeMeasure_map_quadrantHatWalk_conditional
    rw [← hwalklaw] at hclass0
    have hclass : ∀ᵐ ω ∂iidCodeMeasure,
        let p := DirectedDistances.RandomWalk.quadrantHatWalk ω
        let t := (conditionedSecondCoordinateFirstHit r p).toNat
        ∃ (ht : 1 ≤ t) (ell : ℕ) (c : KMSWWalkClass ell r t),
          (∀ i : Fin (t - 1), c.val i = pathCode p (i.val + 1)) ∧
          stoppedMap r hr (pathCode p) = some ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ ∧
          Nonempty (DirectedMapWithMissingIso
            (kmswStageDirectedMap (codeExtend c) (t - 1))
            (kmswStageDirectedMap (boltzmannKMSWStream (pathCode p)) (t - 1))) := by
      have hmap := (Measure.tendsto_ae_map
        aemeasurable_quadrantHatWalk).eventually hclass0
      exact hmap
    have hmark0 := stoppedMarked_clamp_inactive_ae r hr
    rw [← hwalklaw] at hmark0
    have hmark : ∀ᵐ ω ∂iidCodeMeasure,
        (stoppedMarked r hr (DirectedDistances.RandomWalk.quadrantHatWalk ω)).2.val =
          (postHitMinimum r (DirectedDistances.RandomWalk.quadrantHatWalk ω)).toNat ∧
        stoppedMap r hr
          (pathCode (DirectedDistances.RandomWalk.quadrantHatWalk ω)) =
          some (stoppedMarked r hr (DirectedDistances.RandomWalk.quadrantHatWalk ω)).1 := by
      have hmap := (Measure.tendsto_ae_map
        aemeasurable_quadrantHatWalk).eventually hmark0
      exact hmap
    filter_upwards [hclass, hmark, iidCodes_ae_boundaryBusemannLDPMeasurableVersion,
      iidCodes_ae_boundaryBusemannLDPMeasurableVersion_shift n,
      iidCodes_ae_hasFlowLineHits_all_future_times] with ω hc hm hbase hshift hflow hmem
    change ω ∈ E ∩ H at hmem
    rcases hmem with ⟨hcellω, hhitω⟩
    rcases hbase with ⟨hfin0, h0, hX⟩
    rcases hshift with ⟨hfinn, hnWitness, hXn⟩
    rcases hcellω with ⟨⟨hUL, hUR, hLL, hLR⟩, hvalues⟩
    let w : ℕ → Fin 3 := fun i => ω (i + 1)
    have h : HasFlowLineHits w := by simpa [w] using hflow 0
    have hgood := cell_event_sourceStage_uniform_bound ω n α ε
      h0 hnWitness hfin0 hfinn hX hXn hUL hUR hLL hLR hvalues
    obtain ⟨k, hk, hR⟩ := hhitω
    have hrZ : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    have hN : boundaryHitTime w h0 (r : ℤ) ≤ n := by
      have hex := h0.rightHit (r : ℤ) hrZ
      have hfirst := Nat.find_min' hex hR
      have heq : boundaryHitTime w h0 (r : ℤ) = Nat.find hex := by
        unfold boundaryHitTime
        simp only [dite_eq_right (by omega : (r : ℤ) ≠ 0),
          dite_eq_left (by omega : 0 < (r : ℤ))]
      rw [heq]
      exact hfirst.trans hk
    dsimp only at hc hm
    let p := DirectedDistances.RandomWalk.quadrantHatWalk ω
    let m := hattedRightVertexHitTime w h h0 r hr
    have htime : (conditionedSecondCoordinateFirstHit r p).toNat = m := by
      rw [quadrantHatWalk_hit_time_eq_hatted ω h r hr,
        ← hattedRightVertexHitTime_eq_hattedRightHitTime w h h0 r hr]
      rfl
    rw [htime] at hc
    obtain ⟨ht, ell, c, hprefix, hmapClass, _⟩ := hc
    have hldp := hatted_first_hit_prevStage_ldpSup_le_of_sourceStage_uniform_bound
      w h h0 r n (⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊) hr hN hgood
    have hprefixHat : ∀ i < m - 1, (codeExtend c) i = hatCodes w h i := by
      intro i hi
      rw [codeExtend_of_lt c i hi, hprefix ⟨i, hi⟩]
      exact congrFun (quadrantHatWalk_pathCode_stream_eq_hatCodes ω h) i
    have hstage := kmswStage_eq_of_prefix (codeExtend c) (hatCodes w h)
      (m - 1) hprefixHat
    have hbound : ∀ q : Path (⟨0⟩ : StagePresentVertex (hatCodes w h) (m - 1))
        ⟨(kmswStage (codeExtend c) (m - 1)).east
          (kmswStage (codeExtend c) (m - 1)).active⟩,
        q.length ≤ ⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ := by
      intro q
      have hldpCode := hldp
      rw [← hstage] at hldpCode
      have hact : act (hatCodes w h) (m - 1) <
          (kmswStage (hatCodes w h) (m - 1)).nextEdge :=
        act_lt_nextEdge (hatCodes w h) (Nat.le_refl _)
      have hroot : 0 < (kmswStage (hatCodes w h) (m - 1)).nextVertex := by
        have hp := kmswStage_endpoints_lt_nextVertex (hatCodes w h) (m - 1) 0
          (initial_edge_present (hatCodes w h) (m - 1)).1
        rw [(initial_edge_endpoints (hatCodes w h) (m - 1)).1] at hp
        exact hp.1
      have hsink := (kmswStage_endpoints_lt_nextVertex (hatCodes w h)
        (m - 1) (act (hatCodes w h) (m - 1)) hact).2
      have hsinkCode : (kmswStage (codeExtend c) (m - 1)).east
          (kmswStage (codeExtend c) (m - 1)).active <
            (kmswStage (hatCodes w h) (m - 1)).nextVertex := by
        rw [hstage]
        exact hsink
      exact WithBot.coe_le_coe.mp
        (stagePathLength_le_of_ldpSup_le_of_vertices (hatCodes w h) (m - 1)
          (⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊) _ _ hroot hsinkCode hldpCode q)
    have hprefixPath : ∀ i < m - 1,
        (codeExtend c) i = pathCode p (i + 1) := by
      intro i hi
      rw [codeExtend_of_lt c i hi]
      exact hprefix ⟨i, hi⟩
    have hlen := stoppedClass_ldpLength_le_of_quadrantHatWalk_path_bound
      ht c ω h hprefixPath hbound
    have hmarked : (stoppedMarked r hr p).1 =
        ⟨ell, ⟨m, kmswToMapIsoClass ht c⟩⟩ :=
      Option.some.inj (hm.2.symm.trans hmapClass)
    let rep := (stoppedMarked r hr p).1.2.2.out
    have hrepLen : ldpLengthBase rep.B =
        ldpLengthBase (kmswToMapIsoClass ht c).out.B := by
      dsimp only [rep]
      have hh := congrArg
        (fun z : Σ j : ℕ, Σ k : ℕ, KMSWMapIsoClass j r k =>
          ldpLengthBase z.2.2.out.B) hmarked
      exact hh
    have hmk : KMSWMapIsoClass.mk (kmswToMapIsoClass ht c).out =
        KMSWMapIsoClass.mk (kmswWalkClassRep ht c) := by
      calc
        KMSWMapIsoClass.mk (kmswToMapIsoClass ht c).out =
          kmswToMapIsoClass ht c := Quotient.out_eq _
        _ = KMSWMapIsoClass.mk (kmswWalkClassRep ht c) := rfl
    have hbaseIso : Nonempty (BipolarBoundaryBaseIso
        (kmswToMapIsoClass ht c).out.B (kmswWalkClassRep ht c).B) :=
      (KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hmk
    obtain ⟨I⟩ := hbaseIso
    have hclassLen : ldpLengthBase (kmswWalkClassRep ht c).B ≤
        ⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ :=
      WithBot.coe_le_coe.mp hlen
    have hcanonicalLen :
        ldpLengthBase (kmswToMapIsoClass ht c).out.B ≤
          ⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ := by
      rw [← ldpLengthBase_eq_of_baseIso I]
      exact hclassLen
    have hactualLen : ldpLengthBase rep.B ≤
        ⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ := by
      rw [hrepLen]
      exact hcanonicalLen
    have hfloor : (⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℝ) ≤
        α * (n : ℝ) ^ (3 / 4 : ℝ) := Nat.floor_le (by positivity)
    have hnr : (n : ℝ) ≤ (κ + 1) * (r : ℝ) ^ 2 := by
      have hceil : (n : ℝ) < κ * (r : ℝ) ^ 2 + 1 := by
        dsimp [n]
        exact Nat.ceil_lt_add_one (by positivity)
      have hr2 : 1 ≤ (r : ℝ) ^ 2 := by
        have hr0 : 1 ≤ (r : ℝ) := by exact_mod_cast hr
        nlinarith
      calc
        (n : ℝ) ≤ κ * (r : ℝ) ^ 2 + 1 := le_of_lt hceil
        _ ≤ κ * (r : ℝ) ^ 2 + (r : ℝ) ^ 2 := by linarith
        _ = (κ + 1) * (r : ℝ) ^ 2 := by ring
    have hrpow : ((n : ℝ) ^ (3 / 4 : ℝ)) ≤
        (κ + 1) ^ (3 / 4 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) := by
      have hmono := Real.rpow_le_rpow (by positivity) hnr
        (by norm_num : (0 : ℝ) ≤ 3 / 4)
      have heq : ((κ + 1) * (r : ℝ) ^ 2) ^ (3 / 4 : ℝ) =
          (κ + 1) ^ (3 / 4 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast (r : ℝ) 2,
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (r : ℝ))]
        congr 1
        norm_num
      exact hmono.trans_eq heq
    have htarget : (ldpLengthBase rep.B : ℝ) ≤ Aout * (r : ℝ) ^ (3 / 2 : ℝ) := by
      dsimp [Aout]
      calc
        (ldpLengthBase rep.B : ℝ) ≤
            (⌊α * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℝ) := by
          exact_mod_cast hactualLen
        _ ≤ α * (n : ℝ) ^ (3 / 4 : ℝ) := hfloor
        _ ≤ α * ((κ + 1) ^ (3 / 4 : ℝ) *
            (r : ℝ) ^ (3 / 2 : ℝ)) := by gcongr
        _ = α * (κ + 1) ^ (3 / 4 : ℝ) *
            (r : ℝ) ^ (3 / 2 : ℝ) := by ring
    change f ω ∈ T
    exact htarget
  have hmeas : MeasurableSet T := by
    exact (Set.to_countable _).measurableSet
  have hf : AEMeasurable f iidCodeMeasure :=
    (measurable_stoppedMarked r hr).comp_aemeasurable aemeasurable_quadrantHatWalk
  have hmapreal : iidCodeMeasure.real {ω | f ω ∈ T} =
      (rightVertexMarkedBoltzmannLaw r).real T := by
    have hmap := iidCodeMeasure_map_quadrantHatWalk_stoppedMarked r hr
    change ENNReal.toReal (iidCodeMeasure {ω | f ω ∈ T}) =
      ENNReal.toReal ((rightVertexMarkedBoltzmannLaw r) T)
    rw [← hmap, Measure.map_apply_of_aemeasurable hf hmeas]
    rfl
  have hmono : iidCodeMeasure.real (E ∩ H) ≤
      iidCodeMeasure.real {ω | f ω ∈ T} := by
    apply ENNReal.toReal_mono (by finiteness)
    exact measure_mono_ae hsub
  calc
    1 - δ ≤ iidCodeMeasure.real (E ∩ H) := hprob'
    _ ≤ iidCodeMeasure.real {ω | f ω ∈ T} := hmono
    _ = (rightVertexMarkedBoltzmannLaw r).real T := hmapreal

end DirectedDistances.PaperProofs.Section7
