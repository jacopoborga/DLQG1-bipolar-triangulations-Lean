/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperExitEmbedding
public import DirectedDistances.KMSW.StageDirectedMapPathLengths
import Mathlib.Data.List.GetD

public section

namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk Quiver

attribute [local instance 1100] presentDartQuiver

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
Identify the finite stage map with its present-edge quiver, retaining each dart's edge ID.
The object map is an injection into the natural-number stage carrier. -/
@[expose] noncomputable def boltzmannSdpUpper_stageMapPrefunctor
    (w : ℕ → Fin 3) (n : ℕ) :
    Prefunctor (MapVertex (kmswStageDirectedMap w n)) (StagePresentVertex w n) where
  obj := stageMapVertex w n
  map {u v} e := by
    have he := (stageMap_dart_arrow_iff w n e.val u v).1 e.property
    exact ⟨e.val.1.val, e.val.1.isLt, he.2⟩

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
A common code prefix gives exactly the same finite KMSW stage. The finite class contains
`t - 1` letters; no equality of the padded streams after that prefix is asserted. -/
theorem boltzmannSdpUpper_stoppedPrefix_stage_eq {ell r t : ℕ}
    (c : KMSWWalkClass ell r t) (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hp : ∀ i : Fin (t - 1), c.val i = hatCodes w h i.val) :
    kmswStage (codeExtend c) (t - 1) = kmswStage (hatCodes w h) (t - 1) := by
  apply kmswStage_eq_of_prefix
  intro i hi
  rw [codeExtend_of_lt c i hi]
  exact hp ⟨i, hi⟩

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
Transport present darts through a boundary isomorphism and a common stage, preserving
edge identities after the boundary dart relabelling. -/
@[expose] noncomputable def boltzmannSdpUpper_baseHatPrefunctor
    {D : Type*} [Fintype D] [DecidableEq D] {ell r t : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ell r) (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t) (I : BipolarBoundaryBaseIso B (kmswWalkClassBase ht c))
    (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hs : kmswStage (codeExtend c) (t - 1) = kmswStage (hatCodes w h) (t - 1)) :
    Prefunctor (MapVertex B.map) (StagePresentVertex (hatCodes w h) (t - 1)) where
  obj v := ⟨(stageMapVertex (codeExtend c) (t - 1) (I.vertexEquiv v)).id⟩
  map {u v} e := by
    let d := I.toEquiv e.val
    have he : ¬ (kmswWalkClassBase ht c).map.missing d ∧
        (kmswWalkClassBase ht c).map.tail d ∧
        dartTailVertex (kmswWalkClassBase ht c).map d = I.vertexEquiv u ∧
        dartHeadVertex (kmswWalkClassBase ht c).map d = I.vertexEquiv v := by
      refine ⟨?_, (I.tail_iff e.val).2 e.property.2.1, ?_, ?_⟩
      · intro hm
        exact e.property.1 ((I.missing_iff e.val).1 hm)
      · exact (I.vertexEquiv_dartTailVertex e.val).symm.trans
          (congrArg I.vertexEquiv e.property.2.2.1)
      · exact (I.vertexEquiv_dartHeadVertex e.val).symm.trans
          (congrArg I.vertexEquiv e.property.2.2.2)
    have ha := (stageMap_dart_arrow_iff (codeExtend c) (t - 1) d
      (I.vertexEquiv u) (I.vertexEquiv v)).1 he
    refine ⟨d.1.val, ?_, ?_, ?_, ?_⟩
    · rw [← hs]
      exact d.1.isLt
    · rw [← hs]
      exact ha.2.1
    · rw [← hs]
      exact ha.2.2.1
    · rw [← hs]
      exact ha.2.2.2

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
The finite stage source has natural-number label zero. -/
theorem boltzmannSdpUpper_stageBase_source {ell r t : ℕ} (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t) :
    stageMapVertex (codeExtend c) (t - 1) (kmswWalkClassBase ht c).source = ⟨0⟩ := by
  let w := codeExtend c
  let m := t - 1
  let s := kmswStage w m
  have hf := kmswWalkClassMap_mem_sourceClass ht c
  dsimp only at hf
  rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, hLL, _⟩
  apply congrArg (StagePresentVertex.mk (w := w) (n := m))
  change s.west (s.UL.head _) = 0
  have hs := (kmswStage_boundary_chain_invariant w m).2.2.1
  have hUL := (kmswStage_UL_nonempty_active_last w m).1
  have h0 := (initial_edge_endpoints w m).1
  change boundaryStart s (s.UL ++ s.UR) = boundaryStart s (s.LL ++ s.LR) at hs
  have hURs : s.UR = [] := hUR
  have hLLs : s.LL = [] := hLL
  rw [hURs, hLLs, List.append_nil, List.nil_append] at hs
  have huhead : s.UL.head? = some (s.UL.head hUL) := List.head?_eq_some_head hUL
  have hrhead : s.LR.head? = some 0 := by
    change (kmswStage w m).LR.head? = some 0
    induction m with
    | zero => rfl
    | succ m ih =>
      change (kmswStepOfStep (kmswStage w m) (kmswCodeStep (w m))).LR.head? = _
      cases kmswCodeStep (w m) with
      | up => exact ih
      | left => simp only [kmswStepOfStep]; split <;> exact ih
      | down =>
        simp only [kmswStepOfStep]
        split
        · exact ih
        · change ((kmswStage w m).LR ++ [(kmswStage w m).nextEdge]).head? = _
          simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w m)] using ih
  change s.UL.head?.map s.west = s.LR.head?.map s.west at hs
  rw [huhead, hrhead] at hs
  exact (Option.some.inj hs).trans h0

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
Every ordered left vertex, including both endpoints and indices below the mark, is
preserved by the boundary isomorphism. -/
theorem boltzmannSdpUpper_baseIso_leftVertex {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) (ht : 1 ≤ q.1.2.1)
    (c : KMSWWalkClass q.1.1 r q.1.2.1)
    (I : BipolarBoundaryBaseIso q.1.2.2.out.B (kmswWalkClassBase ht c))
    (j : Fin (q.1.1 + 1)) :
    I.vertexEquiv (boltzmannSdpUpper_leftVertex q j) =
      (kmswWalkClassBase ht c).leftPath.vertices.get
        ⟨j.val, by rw [(kmswWalkClassBase ht c).leftPath.vertices_length]; exact j.isLt⟩ := by
  let B := q.1.2.2.out.B
  let C := kmswWalkClassBase ht c
  have hp : I.mapPath B.leftPath = C.leftPath :=
    SimpleDirectedDartPath.eq_of_darts_eq I.leftDarts
  have hv : B.leftPath.vertices.map I.vertexEquiv = C.leftPath.vertices :=
    congrArg SimpleDirectedDartPath.vertices hp
  have hg := congrArg (fun xs => xs.getD j.val (I.vertexEquiv B.source)) hv
  rw [List.getD_map] at hg
  rw [List.getD_eq_get B.leftPath.vertices B.source
    ⟨j.val, by rw [B.leftPath.vertices_length]; exact j.isLt⟩,
    List.getD_eq_get C.leftPath.vertices (I.vertexEquiv B.source)
    ⟨j.val, by rw [C.leftPath.vertices_length]; exact j.isLt⟩] at hg
  exact hg

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
The stopped marked map embeds in the raw cell after the right hit. The existential
witnesses record the actual stopped code prefix and boundary isomorphism. Every left
vertex maps to the same indexed vertex of the stopped stage's left path; that path is
UL because `stoppedStage_LL_nil`. This makes no assertion identifying the mark with
all of UL. -/
theorem boltzmannSdpUpper_exitMap (ω : ℕ → Fin 3) (r : ℕ) (hr : 1 ≤ r)
    (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) (n : ℕ)
    (hhit : ∃ k ≤ n, R (fun i => ω (i + 1)) k = -(r : ℤ)) :
    let w := fun i => ω (i + 1)
    let q := stoppedMarked r hr (quadrantHatWalk ω)
    ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map) (StagePresentVertex w n),
      F.obj q.1.2.2.out.B.source = ⟨0⟩ ∧ Function.Injective F.obj ∧
      ∃ (ht : 1 ≤ q.1.2.1) (c : KMSWWalkClass q.1.1 r q.1.2.1)
        (I : BipolarBoundaryBaseIso q.1.2.2.out.B (kmswWalkClassBase ht c)),
        q.1.2.1 = hattedRightVertexHitTime w h hb r hr ∧
        (∀ i : Fin (q.1.2.1 - 1), c.val i = hatCodes w h i.val) ∧
        kmswStage (codeExtend c) (q.1.2.1 - 1) =
          kmswStage (hatCodes w h) (q.1.2.1 - 1) ∧
        ∀ j : Fin (q.1.1 + 1),
          I.vertexEquiv (boltzmannSdpUpper_leftVertex q j) =
            (kmswWalkClassBase ht c).leftPath.vertices.get
              ⟨j.val, by
                rw [(kmswWalkClassBase ht c).leftPath.vertices_length]
                exact j.isLt⟩ ∧
          F.obj (boltzmannSdpUpper_leftVertex q j) =
            ⟨boltzmannSdpUpper_hatRawVertex w h (q.1.2.1 - 1)
              (stageMapVertex (codeExtend c) (q.1.2.1 - 1)
                ((kmswWalkClassBase ht c).leftPath.vertices.get
                  ⟨j.val, by
                    rw [(kmswWalkClassBase ht c).leftPath.vertices_length]
                    exact j.isLt⟩)).id⟩ := by
  classical
  let P (q : RightVertexMarkedBoltzmannSpace r) : Prop :=
    ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map) (StagePresentVertex (fun i => ω (i + 1)) n),
      F.obj q.1.2.2.out.B.source = ⟨0⟩ ∧ Function.Injective F.obj ∧
      ∃ (ht : 1 ≤ q.1.2.1) (c : KMSWWalkClass q.1.1 r q.1.2.1)
        (I : BipolarBoundaryBaseIso q.1.2.2.out.B (kmswWalkClassBase ht c)),
        q.1.2.1 = hattedRightVertexHitTime (fun i => ω (i + 1)) h hb r hr ∧
        (∀ i : Fin (q.1.2.1 - 1), c.val i = hatCodes (fun i => ω (i + 1)) h i.val) ∧
        kmswStage (codeExtend c) (q.1.2.1 - 1) =
          kmswStage (hatCodes (fun i => ω (i + 1)) h) (q.1.2.1 - 1) ∧
        ∀ j : Fin (q.1.1 + 1),
          I.vertexEquiv (boltzmannSdpUpper_leftVertex q j) =
            (kmswWalkClassBase ht c).leftPath.vertices.get
              ⟨j.val, by
                rw [(kmswWalkClassBase ht c).leftPath.vertices_length]
                exact j.isLt⟩ ∧
          F.obj (boltzmannSdpUpper_leftVertex q j) =
            ⟨boltzmannSdpUpper_hatRawVertex (fun i => ω (i + 1)) h (q.1.2.1 - 1)
              (stageMapVertex (codeExtend c) (q.1.2.1 - 1)
                ((kmswWalkClassBase ht c).leftPath.vertices.get
                  ⟨j.val, by
                    rw [(kmswWalkClassBase ht c).leftPath.vertices_length]
                    exact j.isLt⟩)).id⟩
  change P (stoppedMarked r hr (quadrantHatWalk ω))
  obtain ⟨ht, ell, c, hclass, hp⟩ :=
    quadrantHatWalk_stoppedMarked_value_with_prefix ω r hr h hb
  generalize hq : stoppedMarked r hr (quadrantHatWalk ω) = q at *
  rcases q with ⟨⟨ellQ, tQ, classQ⟩, mark⟩
  change (⟨ellQ, ⟨tQ, classQ⟩⟩ : AllBoltzmannSpace r) =
    ⟨ell, ⟨hattedRightVertexHitTime (fun i => ω (i + 1)) h hb r hr,
      kmswToMapIsoClass ht c⟩⟩ at hclass
  cases hclass
  dsimp only [P]
  let w := fun i => ω (i + 1)
  let t := hattedRightVertexHitTime w h hb r hr
  let B := (kmswToMapIsoClass ht c).out.B
  let I := (stoppedStage_out_baseIso ht c).some.symm
  have hs := boltzmannSdpUpper_stoppedPrefix_stage_eq c w h hp
  have hn := boltzmannSdpUpper_stoppedStage_time_le_of_raw_hit ω r hr h hb n hhit
  let G := boltzmannSdpUpper_baseHatPrefunctor B ht c I w h hs
  let H := boltzmannSdpUpper_hatRawStagePrefunctor w h (t - 1) n hn
  let F := G.comp H
  have hGroot : G.obj B.source = ⟨0⟩ := by
    change (⟨(stageMapVertex (codeExtend c) (t - 1)
      (I.vertexEquiv B.source)).id⟩ : StagePresentVertex (hatCodes w h) (t - 1)) = ⟨0⟩
    rw [I.vertexEquiv_source, boltzmannSdpUpper_stageBase_source ht c]
  have hGinj : Function.Injective G.obj := by
    intro a b hab
    apply I.vertexEquiv.injective
    apply stageMapVertex_injective (codeExtend c) (t - 1)
    exact congrArg (StagePresentVertex.mk (w := codeExtend c) (n := t - 1))
      (congrArg StagePresentVertex.id hab)
  refine ⟨F, ?_, ?_, ht, c, I, rfl, hp, hs, ?_⟩
  · change H.obj (G.obj B.source) = ⟨0⟩
    rw [hGroot]
    exact boltzmannSdpUpper_hatRawStagePrefunctor_root w h (t - 1) n hn
  · exact (boltzmannSdpUpper_hatRawStagePrefunctor_obj_injective
      w h (t - 1) n hn).comp hGinj
  · intro j
    have hj := boltzmannSdpUpper_baseIso_leftVertex
      (⟨⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩, mark⟩ :
        RightVertexMarkedBoltzmannSpace r) ht c I j
    refine ⟨hj, ?_⟩
    change (⟨boltzmannSdpUpper_hatRawVertex w h (t - 1)
      (stageMapVertex (codeExtend c) (t - 1)
        (I.vertexEquiv (boltzmannSdpUpper_leftVertex
          (⟨⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩, mark⟩ :
            RightVertexMarkedBoltzmannSpace r) j))).id⟩ :
          StagePresentVertex w n) = _
    rw [hj]

end DirectedDistances.PaperProofs.Section7
