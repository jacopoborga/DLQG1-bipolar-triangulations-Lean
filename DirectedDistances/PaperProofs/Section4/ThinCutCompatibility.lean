module

public import DirectedDistances.PaperProofs.Section4.ThinHalfTruncate
public import DirectedDistances.PaperProofs.Section4.ThinGoodCutExists
public import DirectedDistances.PaperProofs.Section4.ThinTruncationDecoder
public import DirectedDistances.KMSW.XDPStageIdentificationAtCuts
public import DirectedDistances.PlanarMap.PlanarPathCutLeftHalfBase
public import DirectedDistances.PlanarMap.PlanarPathCutRightHalfBase
public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.PathSpaceTransferCarrier
public import DirectedDistances.KMSW.StageMapCongr
import DirectedDistances.KMSW.HatInducedExit
public import DirectedDistances.KMSW.KMSWWalkClassRepStage

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/






























































public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left half embedding preserves the indexed outer-boundary target, independently -/
theorem leftHalf_boundary_target_map {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] (i : ℕ) :
    (((pathCutLeftHalfBase B P).leftPath.darts[i]?).map
      (dartHeadVertex (pathCutLeftHalfBase B P).map)).map
        (pathCutLeftHalfVertexMap B P) =
      (B.leftPath.darts[i]?).map (dartHeadVertex B.map) := by
  have h := congrArg (fun ds => ds[i]?)
    (pathCutLeftHalfBase_leftPath_darts_unattach B P)
  change ((pathCutLeftHalfBase B P).leftPath.darts.map Subtype.val)[i]? = _ at h
  rw [List.getElem?_map] at h
  change (((pathCutLeftHalfBase B P).leftPath.darts[i]?).map
    (dartHeadVertex (pathCutLeftHalfDirectedMap B P))).map _ = _
  rw [← h, Option.map_map, Option.map_map]
  apply congrArg (fun f => ((pathCutLeftHalfBase B P).leftPath.darts[i]?).map f)
  funext d
  exact pathCutLeftHalfVertexMap_dartHeadVertex B P d

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right half embedding preserves the indexed outer-boundary target, independently -/
theorem rightHalf_boundary_target_map {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r n : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] (i : ℕ) :
    (((pathCutRightHalfBase B P).rightPath.darts[i]?).map
      (dartHeadVertex (pathCutRightHalfBase B P).map)).map
        (pathCutRightHalfVertexMap B P) =
      (B.rightPath.darts[i]?).map (dartHeadVertex B.map) := by
  have h := congrArg (fun ds => ds[i]?)
    (pathCutRightHalfBase_rightPath_darts_unattach B P)
  change ((pathCutRightHalfBase B P).rightPath.darts.map Subtype.val)[i]? = _ at h
  rw [List.getElem?_map] at h
  change (((pathCutRightHalfBase B P).rightPath.darts[i]?).map
    (dartHeadVertex (pathCutRightHalfDirectedMap B P))).map _ = _
  rw [← h, Option.map_map, Option.map_map]
  apply congrArg (fun f => ((pathCutRightHalfBase B P).rightPath.darts[i]?).map f)
  funext d
  exact pathCutRightHalfVertexMap_dartHeadVertex B P d

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Indexed boundary targets commute with an isomorphism of finite bases. -/
theorem boundaryTarget_baseIso {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) (a : ThinMapSide) (s : ℕ) :
    (boundaryTarget B a s).map I.vertexEquiv = boundaryTarget C a s := by
  cases s with
  | zero => simp only [boundaryTarget, Option.map_some, I.vertexEquiv_source]
  | succ i =>
    have hb : (boundaryDarts B a).map I.toEquiv = boundaryDarts C a := by
      cases a with
      | left => exact I.leftDarts
      | right => exact I.rightDarts
    simp only [boundaryTarget, ← hb, List.getElem?_map, Option.map_map]
    congr 1
    funext d
    exact I.vertexEquiv_dartHeadVertex d

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The relabelled left-cut representative embeds into its original finite base. -/
@[expose] noncomputable def cutLRepVertexMap {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    MapVertex (cutLRep R hR).2.B.map → MapVertex R.B.map :=
  let P := selectedGeodesicOfLen R.B x hR
  pathCutLeftHalfVertexMap R.B P ∘
    ((pathCutLeftHalfBase R.B P).transportIso (Fintype.equivFin _)).symm.vertexEquiv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The relabelled right-cut representative embeds into its original finite base. -/
@[expose] noncomputable def cutRRepVertexMap {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    MapVertex (cutRRep R hR).2.B.map → MapVertex R.B.map :=
  let P := selectedGeodesicOfLen R.B x hR
  pathCutRightHalfVertexMap R.B P ∘
    ((pathCutRightHalfBase R.B P).transportIso (Fintype.equivFin _)).symm.vertexEquiv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Relabelling the left cut preserves every indexed outer-boundary target,
including zero and indices beyond the boundary. -/
theorem cutLRep_boundaryTarget_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) (s : ℕ) :
    (boundaryTarget (cutLRep R hR).2.B .left s).map (cutLRepVertexMap R hR) =
      boundaryTarget R.B .left s := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  let f : MapVertex B.map → MapVertex R.B.map := pathCutLeftHalfVertexMap R.B P
  change (boundaryTarget (B.transport (Fintype.equivFin _)) .left s).map
    (f ∘ I.vertexEquiv) = _
  rw [← Option.map_map, boundaryTarget_baseIso I]
  cases s with
  | zero =>
    change some (pathCutLeftHalfVertexMap R.B P (pathCutLeftHalfSource R.B P)) = _
    rw [pathCutLeftHalfSource_map]
    rfl
  | succ i => exact leftHalf_boundary_target_map R.B P i

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Relabelling the right cut preserves every indexed outer-boundary target,
including zero and indices beyond the boundary. -/
theorem cutRRep_boundaryTarget_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) (s : ℕ) :
    (boundaryTarget (cutRRep R hR).2.B .right s).map (cutRRepVertexMap R hR) =
      boundaryTarget R.B .right s := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  let f : MapVertex B.map → MapVertex R.B.map := pathCutRightHalfVertexMap R.B P
  change (boundaryTarget (B.transport (Fintype.equivFin _)) .right s).map
    (f ∘ I.vertexEquiv) = _
  rw [← Option.map_map, boundaryTarget_baseIso I]
  cases s with
  | zero =>
    change some (pathCutRightHalfVertexMap R.B P (pathCutRightHalfSource R.B P)) = _
    rw [pathCutRightHalfSource_map]
    rfl
  | succ i => exact rightHalf_boundary_target_map R.B P i

private theorem cut_baseIso_step_map {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) {u v : MapVertex B.map}
    (h : B.map.directedStep u v) : C.map.directedStep (I.vertexEquiv u)
      (I.vertexEquiv v) := by
  obtain ⟨d, hd, ht, hu, hv⟩ := h
  refine ⟨I.toEquiv d, fun hh => hd ((I.missing_iff d).mp hh),
    (I.tail_iff d).mpr ht, ?_, ?_⟩
  · exact (I.vertexEquiv_dartTailVertex d).symm.trans (congrArg I.vertexEquiv hu)
  · exact (I.vertexEquiv_dartHeadVertex d).symm.trans (congrArg I.vertexEquiv hv)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The concrete left-cut embedding preserves ancestor reachability to every target. -/
theorem cutLRep_ancestors_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (v t : MapVertex (cutLRep R hR).2.B.map)
    (hv : v ∈ ancestors (presentation (cutLRep R hR).2 .left t)) :
    cutLRepVertexMap R hR v ∈
      ancestors (presentation R .left (cutLRepVertexMap R hR t)) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hi : Relation.ReflTransGen B.map.directedStep (I.vertexEquiv v)
      (I.vertexEquiv t) :=
    Relation.ReflTransGen.lift I.vertexEquiv (fun _ _ h => cut_baseIso_step_map I h) v t hv
  apply Relation.ReflTransGen.lift (pathCutLeftHalfVertexMap R.B P) _ _ _ hi
  intro u z h
  obtain ⟨d, _, ht, hu, hz⟩ := h
  refine ⟨d.1, R.B.noMissingDarts _,
    ((pathCutLeftHalf_embedding_fields R.B P).2.2.1 d).mp ht, ?_, ?_⟩
  · exact (pathCutLeftHalfVertexMap_dartTailVertex R.B P d).symm.trans
      (congrArg (pathCutLeftHalfVertexMap R.B P) hu)
  · exact (pathCutLeftHalfVertexMap_dartHeadVertex R.B P d).symm.trans
      (congrArg (pathCutLeftHalfVertexMap R.B P) hz)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The concrete right-cut embedding preserves ancestor reachability to every target. -/
theorem cutRRep_ancestors_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (v t : MapVertex (cutRRep R hR).2.B.map)
    (hv : v ∈ ancestors (presentation (cutRRep R hR).2 .right t)) :
    cutRRepVertexMap R hR v ∈
      ancestors (presentation R .right (cutRRepVertexMap R hR t)) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hi : Relation.ReflTransGen B.map.directedStep (I.vertexEquiv v)
      (I.vertexEquiv t) :=
    Relation.ReflTransGen.lift I.vertexEquiv (fun _ _ h => cut_baseIso_step_map I h) v t hv
  apply Relation.ReflTransGen.lift (pathCutRightHalfVertexMap R.B P) _ _ _ hi
  intro u z h
  obtain ⟨d, _, ht, hu, hz⟩ := h
  refine ⟨d.1, R.B.noMissingDarts _,
    ((pathCutRightHalf_embedding_fields R.B P).2.2.1 d).mp ht, ?_, ?_⟩
  · exact (pathCutRightHalfVertexMap_dartTailVertex R.B P d).symm.trans
      (congrArg (pathCutRightHalfVertexMap R.B P) hu)
  · exact (pathCutRightHalfVertexMap_dartHeadVertex R.B P d).symm.trans
      (congrArg (pathCutRightHalfVertexMap R.B P) hz)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The dart inclusion of the relabelled left cut retains the original geometric dart. -/
@[expose] noncomputable def cutLRepDartMap {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    Fin (cutLRep R hR).2.dartCount → Fin R.dartCount :=
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  fun d => (((B.transportIso (Fintype.equivFin _)).symm.toEquiv d)).1

private theorem cutLRep_endpoints {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutLRep R hR).2.dartCount) :
    cutLRepVertexMap R hR (dartTailVertex (cutLRep R hR).2.B.map d) =
        dartTailVertex R.B.map (cutLRepDartMap R hR d) ∧
      cutLRepVertexMap R hR (dartHeadVertex (cutLRep R hR).2.B.map d) =
        dartHeadVertex R.B.map (cutLRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  constructor
  · exact (congrArg (pathCutLeftHalfVertexMap R.B P)
      (I.vertexEquiv_dartTailVertex d)).trans
        (pathCutLeftHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))
  · exact (congrArg (pathCutLeftHalfVertexMap R.B P)
      (I.vertexEquiv_dartHeadVertex d)).trans
        (pathCutLeftHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every geometric dart in the left ancestor restriction maps into the original
ancestor restriction, preserving both endpoints, including darts against orientation. -/
theorem cutLRep_selectedDarts_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutLRep R hR).2.B.map)
    (d : Fin (cutLRep R hR).2.dartCount)
    (hd : d ∈ selectedDarts (presentation (cutLRep R hR).2 .left t)) :
    cutLRepDartMap R hR d ∈
      selectedDarts (presentation R .left (cutLRepVertexMap R hR t)) := by
  constructor
  · exact (cutLRep_endpoints R hR d).1 ▸
      cutLRep_ancestors_map R hR _ t hd.1
  · exact (cutLRep_endpoints R hR d).2 ▸
      cutLRep_ancestors_map R hR _ t hd.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The dart inclusion of the relabelled right cut retains the original geometric dart. -/
@[expose] noncomputable def cutRRepDartMap {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    Fin (cutRRep R hR).2.dartCount → Fin R.dartCount :=
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  fun d => (((B.transportIso (Fintype.equivFin _)).symm.toEquiv d)).1

private theorem cutRRep_endpoints {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutRRep R hR).2.dartCount) :
    cutRRepVertexMap R hR (dartTailVertex (cutRRep R hR).2.B.map d) =
        dartTailVertex R.B.map (cutRRepDartMap R hR d) ∧
      cutRRepVertexMap R hR (dartHeadVertex (cutRRep R hR).2.B.map d) =
        dartHeadVertex R.B.map (cutRRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  constructor
  · exact (congrArg (pathCutRightHalfVertexMap R.B P)
      (I.vertexEquiv_dartTailVertex d)).trans
        (pathCutRightHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))
  · exact (congrArg (pathCutRightHalfVertexMap R.B P)
      (I.vertexEquiv_dartHeadVertex d)).trans
        (pathCutRightHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every geometric dart in the right ancestor restriction maps into the original
ancestor restriction, preserving both endpoints, including darts against orientation. -/
theorem cutRRep_selectedDarts_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutRRep R hR).2.B.map)
    (d : Fin (cutRRep R hR).2.dartCount)
    (hd : d ∈ selectedDarts (presentation (cutRRep R hR).2 .right t)) :
    cutRRepDartMap R hR d ∈
      selectedDarts (presentation R .right (cutRRepVertexMap R hR t)) := by
  constructor
  · exact (cutRRep_endpoints R hR d).1 ▸
      cutRRep_ancestors_map R hR _ t hd.1
  · exact (cutRRep_endpoints R hR d).2 ▸
      cutRRep_ancestors_map R hR _ t hd.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual relabelled left-half dart embedding preserves edge pairing and tail
orientation and induces its vertex rotation by first return in the original map. -/
theorem cutLRep_embedding_fields {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    Function.Injective (cutLRepDartMap R hR) ∧
      Function.Injective (cutLRepVertexMap R hR) ∧
      (∀ d, cutLRepDartMap R hR ((cutLRep R hR).2.B.map.edgeInv d) =
        R.B.map.edgeInv (cutLRepDartMap R hR d)) ∧
      (∀ d, (cutLRep R hR).2.B.map.tail d ↔
        R.B.map.tail (cutLRepDartMap R hR d)) ∧
      (∀ d, ∃ k : ℕ, 0 < k ∧
        (R.B.map.rot : _ → _)^[k] (cutLRepDartMap R hR d) =
          cutLRepDartMap R hR ((cutLRep R hR).2.B.map.rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          (R.B.map.rot : _ → _)^[j] (cutLRepDartMap R hR d) ∉
            Set.range (cutLRepDartMap R hR)) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hf := pathCutLeftHalf_embedding_fields R.B P
  refine ⟨Subtype.val_injective.comp I.toEquiv.injective,
    (pathCutLeftHalfVertexMap_injective R.B P).comp I.vertexEquiv.injective,
    ?_, ?_, ?_⟩
  · intro d
    exact (congrArg Subtype.val (I.edgeInv_comm d)).trans (hf.2.1 (I.toEquiv d))
  · intro d
    exact (I.tail_iff d).symm.trans (hf.2.2.1 (I.toEquiv d))
  · intro d
    obtain ⟨k, hk, he, hgap⟩ := hf.2.2.2 (I.toEquiv d)
    refine ⟨k, hk, he.trans (congrArg Subtype.val (I.rot_comm d)).symm, ?_⟩
    intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    exact hgap j hj hjk ⟨I.toEquiv e, he⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual relabelled right-half dart embedding preserves edge pairing and tail
orientation and induces its vertex rotation by first return in the original map. -/
theorem cutRRep_embedding_fields {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    Function.Injective (cutRRepDartMap R hR) ∧
      Function.Injective (cutRRepVertexMap R hR) ∧
      (∀ d, cutRRepDartMap R hR ((cutRRep R hR).2.B.map.edgeInv d) =
        R.B.map.edgeInv (cutRRepDartMap R hR d)) ∧
      (∀ d, (cutRRep R hR).2.B.map.tail d ↔
        R.B.map.tail (cutRRepDartMap R hR d)) ∧
      (∀ d, ∃ k : ℕ, 0 < k ∧
        (R.B.map.rot : _ → _)^[k] (cutRRepDartMap R hR d) =
          cutRRepDartMap R hR ((cutRRep R hR).2.B.map.rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          (R.B.map.rot : _ → _)^[j] (cutRRepDartMap R hR d) ∉
            Set.range (cutRRepDartMap R hR)) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hf := pathCutRightHalf_embedding_fields R.B P
  refine ⟨Subtype.val_injective.comp I.toEquiv.injective,
    (pathCutRightHalfVertexMap_injective R.B P).comp I.vertexEquiv.injective,
    ?_, ?_, ?_⟩
  · intro d
    exact (congrArg Subtype.val (I.edgeInv_comm d)).trans (hf.2.1 (I.toEquiv d))
  · intro d
    exact (I.tail_iff d).symm.trans (hf.2.2.1 (I.toEquiv d))
  · intro d
    obtain ⟨k, hk, he, hgap⟩ := hf.2.2.2 (I.toEquiv d)
    refine ⟨k, hk, he.trans (congrArg Subtype.val (I.rot_comm d)).symm, ?_⟩
    intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    exact hgap j hj hjk ⟨I.toEquiv e, he⟩

private theorem cut_rotation_first_return_forward
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : Equiv.Perm A) (τ : Equiv.Perm B) (f : A → B) (hf : Function.Injective f)
    (hn : ∀ d, ∃ k : ℕ, 0 < k ∧ (τ : B → B)^[k] (f d) = f (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (τ : B → B)^[j] (f d) ∉ Set.range f)
    (U : Set A) (d e : U) (k : ℕ) (hk : 0 < k)
    (he : (σ : A → A)^[k] d.1 = e.1)
    (hgap : ∀ j : ℕ, 0 < j → j < k → (σ : A → A)^[j] d.1 ∉ U) :
    ∃ m : ℕ, 0 < m ∧ (τ : B → B)^[m] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U := by
  have hex : ∀ n, n ≤ k → ∃ m : ℕ, n ≤ m ∧ (n = 0 → m = 0) ∧
      (τ : B → B)^[m] (f d.1) = f ((σ : A → A)^[n] d.1) ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨0, le_rfl, fun _ => rfl, rfl, fun j hj hjm => by omega⟩
    | succ n ih =>
        intro hnk
        obtain ⟨m, hnm, hm0, hm, havoid⟩ := ih (by omega)
        obtain ⟨l, hl, hlstep, hlavoid⟩ := hn ((σ : A → A)^[n] d.1)
        refine ⟨m + l, by omega, by omega, ?_, ?_⟩
        · rw [Nat.add_comm m l, Function.iterate_add_apply, hm, hlstep]
          rw [Function.iterate_succ_apply']
        · intro j hj hjml hmem
          by_cases hjm : j < m
          · exact havoid j hj hjm hmem
          · by_cases hjme : j = m
            · subst j
              obtain ⟨a, ha, hea⟩ := hmem
              have hnpos : 0 < n := by
                by_contra h
                have hn0 : n = 0 := by omega
                have := hm0 hn0
                omega
              apply hgap n hnpos (by omega)
              exact (hf (hea.trans hm)).symm ▸ ha
            · have hjpos : 0 < j - m := by omega
              have hjlt : j - m < l := by omega
              apply hlavoid (j - m) hjpos hjlt
              obtain ⟨a, _, hea⟩ := hmem
              refine ⟨a, ?_⟩
              have hjdecomp : j - m + m = j := by omega
              have hh := Function.iterate_add_apply (τ : B → B) (j - m) m (f d.1)
              rw [hjdecomp, hm] at hh
              exact hea.trans hh
  obtain ⟨m, hkm, _, hm, havoid⟩ := hex k le_rfl
  exact ⟨m, by omega, hm.trans (congrArg f he), havoid⟩

private theorem cut_rotation_first_return_image_iff
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (σ : Equiv.Perm A) (τ : Equiv.Perm B) (f : A → B) (hf : Function.Injective f)
    (hn : ∀ d, ∃ k : ℕ, 0 < k ∧ (τ : B → B)^[k] (f d) = f (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (τ : B → B)^[j] (f d) ∉ Set.range f)
    (U : Set A) (d e : U) :
    (∃ k : ℕ, 0 < k ∧ (σ : A → A)^[k] d.1 = e.1 ∧
      ∀ j : ℕ, 0 < j → j < k → (σ : A → A)^[j] d.1 ∉ U) ↔
    (∃ m : ℕ, 0 < m ∧ (τ : B → B)^[m] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U) := by
  classical
  constructor
  · rintro ⟨k, hk, he, hgap⟩
    exact cut_rotation_first_return_forward σ τ f hf hn U d e k hk he hgap
  · rintro ⟨l, hl, hlend, hlgap⟩
    let k := firstReturnTime σ U d
    let z := firstReturn σ U d
    have hs := firstReturnTime_spec σ U d
    have hc := firstReturn_characterization σ U d
    obtain ⟨m, hm, he, hgap⟩ :=
      cut_rotation_first_return_forward σ τ f hf hn U d z k hs.1 hc.1 hc.2
    have hml : m = l := by
      apply Nat.le_antisymm
      · by_contra h
        exact hgap l hl (by omega) ⟨e.1, e.2, hlend.symm⟩
      · by_contra h
        exact hlgap m hm (by omega) ⟨z.1, z.2, he.symm⟩
    rw [hml] at he
    have hz : z.1 = e.1 := hf (he.symm.trans hlend)
    exact ⟨k, hs.1, hc.1.trans hz, hc.2⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The induced left ancestor rotation is exactly first return of the original
rotation to the image of its selected darts, in both directions. -/
theorem cutLRep_truncation_rotation_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (d e : selectedDarts (presentation (cutLRep R hR).2 .left v)) :
    truncationRelation (presentation (cutLRep R hR).2 .left v)
      .rotation (.inr d) (.inr e) ↔
    ∃ k : ℕ, 0 < k ∧
      (R.B.map.rot : _ → _)^[k] (cutLRepDartMap R hR d.1) =
        cutLRepDartMap R hR e.1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        (R.B.map.rot : _ → _)^[j] (cutLRepDartMap R hR d.1) ∉
          cutLRepDartMap R hR '' selectedDarts (presentation (cutLRep R hR).2 .left v) := by
  exact cut_rotation_first_return_image_iff _ _ _ (cutLRep_embedding_fields R hR).1
    (cutLRep_embedding_fields R hR).2.2.2.2 _ d e

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The induced right ancestor rotation is exactly first return of the original
rotation to the image of its selected darts, in both directions. -/
theorem cutRRep_truncation_rotation_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (d e : selectedDarts (presentation (cutRRep R hR).2 .right v)) :
    truncationRelation (presentation (cutRRep R hR).2 .right v)
      .rotation (.inr d) (.inr e) ↔
    ∃ k : ℕ, 0 < k ∧
      (R.B.map.rot : _ → _)^[k] (cutRRepDartMap R hR d.1) =
        cutRRepDartMap R hR e.1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        (R.B.map.rot : _ → _)^[j] (cutRRepDartMap R hR d.1) ∉
          cutRRepDartMap R hR '' selectedDarts (presentation (cutRRep R hR).2 .right v) := by
  exact cut_rotation_first_return_image_iff _ _ _ (cutRRep_embedding_fields R hR).1
    (cutRRep_embedding_fields R hR).2.2.2.2 _ d e

private theorem cut_rotation_first_return_later_stage
    {A D : Type*} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (σ : Equiv.Perm A) (M : DirectedMapWithMissing D)
    (f : A → D) (hf : Function.Injective f)
    (hn : ∀ d, ∃ k : ℕ, 0 < k ∧ (M.rot : D → D)^[k] (f d) = f (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (M.rot : D → D)^[j] (f d) ∉ Set.range f)
    {w : ℕ → Fin 3} {t N : ℕ}
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w t)) (htN : t ≤ N)
    (U : Set A) (d e : U) :
    let g := outerSucc_castDart (kmswStage_nextEdge_mono w htN) ∘ I.toEquiv ∘ f
    (∃ k : ℕ, 0 < k ∧ (σ : A → A)^[k] d.1 = e.1 ∧
      ∀ j : ℕ, 0 < j → j < k → (σ : A → A)^[j] d.1 ∉ U) ↔
    (∃ k : ℕ, 0 < k ∧ (stageRot w N : _ → _)^[k] (g d.1) = g e.1 ∧
      ∀ j : ℕ, 0 < j → j < k → (stageRot w N : _ → _)^[j] (g d.1) ∉ g '' U) := by
  let c := outerSucc_castDart (kmswStage_nextEdge_mono w htN)
  have hc : Function.Injective c := by
    intro d e h
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z => z.1.val) h)
    · exact congrArg (fun z : StageDart (kmswStage w N).nextEdge => z.2) h
  have hi : ∀ d, ∃ k : ℕ, 0 < k ∧
      (stageRot w t : _ → _)^[k] (I.toEquiv d) = I.toEquiv (M.rot d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (stageRot w t : _ → _)^[j] (I.toEquiv d) ∉ Set.range I.toEquiv := by
    intro d
    exact ⟨1, by omega, (I.rot_comm d).symm, fun j hj hjk => by omega⟩
  have hfi := hatExit_induced_rotation_comp σ M.rot (stageRot w t)
    f I.toEquiv I.toEquiv.injective hn hi
  have hg := hatExit_induced_rotation_comp σ (stageRot w t) (stageRot w N)
    (I.toEquiv ∘ f) c hc hfi (hatExit_ambient_rotation_induced w t N htN)
  exact cut_rotation_first_return_image_iff σ (stageRot w N)
    (c ∘ I.toEquiv ∘ f) (hc.comp (I.toEquiv.injective.comp hf)) hg U d e

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left ancestor rotation is first return in any later ambient KMSW stage,
with every geometric dart embedded by its unchanged edge ID and side. -/
theorem cutLRep_truncation_rotation_later_stage {x : XDP} {ℓ r n m t N : ℕ}
    {w : ℕ → Fin 3} (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t)) (htN : t ≤ N)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (d e : selectedDarts (presentation (cutLRep R hR).2 .left v)) :
    let f := outerSucc_castDart (kmswStage_nextEdge_mono w htN) ∘
      I.toEquiv ∘ cutLRepDartMap R hR
    truncationRelation (presentation (cutLRep R hR).2 .left v)
      .rotation (.inr d) (.inr e) ↔
    ∃ k : ℕ, 0 < k ∧ (stageRot w N : _ → _)^[k] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < k → (stageRot w N : _ → _)^[j] (f d.1) ∉
        f '' selectedDarts (presentation (cutLRep R hR).2 .left v) := by
  exact cut_rotation_first_return_later_stage _ _ _ (cutLRep_embedding_fields R hR).1
    (cutLRep_embedding_fields R hR).2.2.2.2 I htN _ d e

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right ancestor rotation is first return in any later ambient KMSW stage,
with every geometric dart embedded by its unchanged edge ID and side. -/
theorem cutRRep_truncation_rotation_later_stage {x : XDP} {ℓ r n m t N : ℕ}
    {w : ℕ → Fin 3} (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t)) (htN : t ≤ N)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (d e : selectedDarts (presentation (cutRRep R hR).2 .right v)) :
    let f := outerSucc_castDart (kmswStage_nextEdge_mono w htN) ∘
      I.toEquiv ∘ cutRRepDartMap R hR
    truncationRelation (presentation (cutRRep R hR).2 .right v)
      .rotation (.inr d) (.inr e) ↔
    ∃ k : ℕ, 0 < k ∧ (stageRot w N : _ → _)^[k] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < k → (stageRot w N : _ → _)^[j] (f d.1) ∉
        f '' selectedDarts (presentation (cutRRep R hR).2 .right v) := by
  exact cut_rotation_first_return_later_stage _ _ _ (cutRRep_embedding_fields R hR).1
    (cutRRep_embedding_fields R hR).2.2.2.2 I htN _ d e

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The relabelled left half preserves every outer-boundary and seam dart index;
its seam is exactly the selected source-to-sink geodesic. -/
theorem cutLRep_boundaryDarts_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    (boundaryDarts (cutLRep R hR).2.B .left).map (cutLRepDartMap R hR) =
        R.B.leftPath.darts ∧
      (boundaryDarts (cutLRep R hR).2.B .right).map (cutLRepDartMap R hR) =
        (selectedGeodesicOfLen R.B x hR).darts := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  constructor
  · change ((B.transport (Fintype.equivFin _)).leftPath.darts.map
      (Subtype.val ∘ I.toEquiv)) = _
    rw [← List.map_map, I.leftDarts]
    exact pathCutLeftHalfBase_leftPath_darts_unattach R.B P
  · change ((B.transport (Fintype.equivFin _)).rightPath.darts.map
      (Subtype.val ∘ I.toEquiv)) = _
    rw [← List.map_map, I.rightDarts]
    exact pathCutLeftHalfBase_rightPath_darts_unattach R.B P

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The relabelled right half preserves every outer-boundary and seam dart index;
its seam is exactly the selected source-to-sink geodesic. -/
theorem cutRRep_boundaryDarts_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    (boundaryDarts (cutRRep R hR).2.B .right).map (cutRRepDartMap R hR) =
        R.B.rightPath.darts ∧
      (boundaryDarts (cutRRep R hR).2.B .left).map (cutRRepDartMap R hR) =
        (selectedGeodesicOfLen R.B x hR).darts := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  constructor
  · change ((B.transport (Fintype.equivFin _)).rightPath.darts.map
      (Subtype.val ∘ I.toEquiv)) = _
    rw [← List.map_map, I.rightDarts]
    exact pathCutRightHalfBase_rightPath_darts_unattach R.B P
  · change ((B.transport (Fintype.equivFin _)).leftPath.darts.map
      (Subtype.val ∘ I.toEquiv)) = _
    rw [← List.map_map, I.leftDarts]
    exact pathCutRightHalfBase_leftPath_darts_unattach R.B P

private theorem cut_baseIso_faceCycle_map {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) {d e : D}
    (h : Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d e) :
    Equiv.Perm.SameCycle C.map.toCombinatorialMap.faceSucc
      (I.toEquiv d) (I.toEquiv e) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hi := Function.Semiconj.iterate_right
    (show Function.Semiconj I.toEquiv B.map.toCombinatorialMap.faceSucc
      C.map.toCombinatorialMap.faceSucc from I.faceSucc_comm) k d
  rw [perm_iterate_eq_pow, perm_iterate_eq_pow] at hi
  exact ⟨k, hi.symm.trans (congrArg I.toEquiv hk)⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every retained inner face in the relabelled left ancestor restriction is the
same retained inner face in the original finite base, with ancestral vertices. -/
theorem cutLRep_retainedFace_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutLRep R hR).2.B.map)
    (d : Fin (cutLRep R hR).2.dartCount)
    (hd : retainedFace (presentation (cutLRep R hR).2 .left t) d) :
    retainedFace (presentation R .left (cutLRepVertexMap R hR t))
      (cutLRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hb : (I.toEquiv d).1 ∉ pathCutLeftHalfBoundaryDarts R.B P := by
    intro h
    exact hd.1 ((I.outer_iff d).mp
      ((pathCutLeftHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  have hf := pathCutLeftHalf_inner_face_contained R.B P (I.toEquiv d).2 hb
  refine ⟨hf.1, ?_⟩
  intro e he
  let f : {z // z ∈ pathCutLeftHalfDarts R.B P} := ⟨e, (hf.2 e he).1⟩
  let c := I.toEquiv.symm f
  have hc : Equiv.Perm.SameCycle (cutLRep R hR).2.B.map.toCombinatorialMap.faceSucc
      d c := by
    have hh := cut_baseIso_faceCycle_map I.symm
      ((pathCutLeftHalf_inner_faceOrbit_iff R.B P (I.toEquiv d) hb f).mpr he)
    change Equiv.Perm.SameCycle (cutLRep R hR).2.B.map.toCombinatorialMap.faceSucc
      (I.toEquiv.symm (I.toEquiv d)) c at hh
    exact (I.toEquiv.symm_apply_apply d) ▸ hh
  have ha := cutLRep_ancestors_map R hR _ t (hd.2 c hc)
  have heq : cutLRepDartMap R hR c = e := by
    change (I.toEquiv (I.toEquiv.symm f)).1 = e
    rw [Equiv.apply_symm_apply]
  exact heq ▸ ((cutLRep_endpoints R hR c).1 ▸ ha)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every retained inner face in the relabelled right ancestor restriction is the
same retained inner face in the original finite base, with ancestral vertices. -/
theorem cutRRep_retainedFace_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutRRep R hR).2.B.map)
    (d : Fin (cutRRep R hR).2.dartCount)
    (hd : retainedFace (presentation (cutRRep R hR).2 .right t) d) :
    retainedFace (presentation R .right (cutRRepVertexMap R hR t))
      (cutRRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hb : (I.toEquiv d).1 ∉ pathCutRightHalfBoundaryDarts R.B P := by
    intro h
    exact hd.1 ((I.outer_iff d).mp
      ((pathCutRightHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  have hf := pathCutRightHalf_inner_face_contained R.B P (I.toEquiv d).2 hb
  refine ⟨hf.1, ?_⟩
  intro e he
  let f : {z // z ∈ pathCutRightHalfDarts R.B P} := ⟨e, (hf.2 e he).1⟩
  let c := I.toEquiv.symm f
  have hc : Equiv.Perm.SameCycle (cutRRep R hR).2.B.map.toCombinatorialMap.faceSucc
      d c := by
    have hh := cut_baseIso_faceCycle_map I.symm
      ((pathCutRightHalf_inner_faceOrbit_iff R.B P (I.toEquiv d) hb f).mpr he)
    change Equiv.Perm.SameCycle (cutRRep R hR).2.B.map.toCombinatorialMap.faceSucc
      (I.toEquiv.symm (I.toEquiv d)) c at hh
    exact (I.toEquiv.symm_apply_apply d) ▸ hh
  have ha := cutRRep_ancestors_map R hR _ t (hd.2 c hc)
  have heq : cutRRepDartMap R hR c = e := by
    change (I.toEquiv (I.toEquiv.symm f)).1 = e
    rw [Equiv.apply_symm_apply]
  exact heq ▸ ((cutRRep_endpoints R hR c).1 ▸ ha)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left-half embedding preserves the successor of every retained inner face. -/
theorem cutLRep_retainedFace_faceSucc_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutLRep R hR).2.B.map)
    (d : Fin (cutLRep R hR).2.dartCount)
    (hd : retainedFace (presentation (cutLRep R hR).2 .left t) d) :
    cutLRepDartMap R hR ((cutLRep R hR).2.B.map.toCombinatorialMap.faceSucc d) =
      R.B.map.toCombinatorialMap.faceSucc (cutLRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hb : (I.toEquiv d).1 ∉ pathCutLeftHalfBoundaryDarts R.B P := by
    intro h
    exact hd.1 ((I.outer_iff d).mp
      ((pathCutLeftHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  have hf := pathCutLeftHalf_inner_face_contained R.B P (I.toEquiv d).2 hb
  have hnext := (hf.2 _ (Equiv.Perm.SameCycle.refl _ _).apply_right).1
  exact (congrArg Subtype.val (I.faceSucc_comm d)).trans
    (pathCutLeftHalf_faceSucc_eq_base_of_mem R.B P (I.toEquiv d).2 hnext)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right-half embedding preserves the successor of every retained inner face. -/
theorem cutRRep_retainedFace_faceSucc_map {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutRRep R hR).2.B.map)
    (d : Fin (cutRRep R hR).2.dartCount)
    (hd : retainedFace (presentation (cutRRep R hR).2 .right t) d) :
    cutRRepDartMap R hR ((cutRRep R hR).2.B.map.toCombinatorialMap.faceSucc d) =
      R.B.map.toCombinatorialMap.faceSucc (cutRRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hb : (I.toEquiv d).1 ∉ pathCutRightHalfBoundaryDarts R.B P := by
    intro h
    exact hd.1 ((I.outer_iff d).mp
      ((pathCutRightHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  have hf := pathCutRightHalf_inner_face_contained R.B P (I.toEquiv d).2 hb
  have hnext := (hf.2 _ (Equiv.Perm.SameCycle.refl _ _).apply_right).1
  exact (congrArg Subtype.val (I.faceSucc_comm d)).trans
    (pathCutRightHalf_faceSucc_eq_base_of_mem R.B P (I.toEquiv d).2 hnext)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The two quotient cut outputs are cuts of one actual representative, with no
assumed identification of that representative with a stage restriction. -/
theorem firstHitPastAllCuts_representative (x : XDP) {ℓ r : ℕ}
    (m : BoltzmannSpace ℓ r) :
    ∃ (R : KMSWMapRep ℓ r m.1) (hR : xdpLengthBase R.B x = xdpLen x m),
      KMSWMapIsoClass.mk R = m.2 ∧
      firstHitPastAllCuts x r (some ⟨ℓ, m⟩) =
        (some ⟨xdpLen x m, ⟨ℓ, ⟨(cutLRep R hR).1,
          KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨xdpLen x m, ⟨(cutRRep R hR).1,
          KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩) := by
  let R : KMSWMapRep ℓ r m.1 := Quotient.out m.2
  have hout : KMSWMapIsoClass.mk R = m.2 := Quotient.out_eq m.2
  have hR : xdpLengthBase R.B x = xdpLen x m := by
    change xdpLengthBase R.B x = xdpLenClass x m.2
    rw [← hout, xdpLenClass_mk]
  refine ⟨R, hR, hout, ?_⟩
  rfl

private noncomputable def cut_baseIso_mapIso {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) : DirectedMapWithMissingIso B.map C.map where
  toEquiv := I.toEquiv
  rot_comm := I.rot_comm
  edgeInv_comm := I.edgeInv_comm
  missing_iff := I.missing_iff
  tail_iff := I.tail_iff
  outer_iff := I.outer_iff

private theorem cut_mapIso_cycle {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) {d e : D}
    (h : Equiv.Perm.SameCycle M.rot d e) :
    Equiv.Perm.SameCycle N.rot (I.toEquiv d) (I.toEquiv e) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hi := Function.Semiconj.iterate_right
    (show Function.Semiconj I.toEquiv M.rot N.rot from I.rot_comm) k d
  rw [perm_iterate_eq_pow, perm_iterate_eq_pow] at hi
  exact ⟨k, hi.symm.trans (congrArg I.toEquiv hk)⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The vertex equivalence induced by a directed planar map isomorphism. -/
@[expose] noncomputable def cutMapIsoVertexEquiv {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) : MapVertex M ≃ MapVertex N :=
  Quotient.congr I.toEquiv (by
    intro d e
    change Equiv.Perm.SameCycle M.rot d e ↔
      Equiv.Perm.SameCycle N.rot (I.toEquiv d) (I.toEquiv e)
    constructor
    · exact cut_mapIso_cycle I
    · intro h
      have hh := cut_mapIso_cycle I.symm h
      change Equiv.Perm.SameCycle M.rot
        (I.toEquiv.symm (I.toEquiv d)) (I.toEquiv.symm (I.toEquiv e)) at hh
      simpa only [Equiv.symm_apply_apply] using hh)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The induced vertex equivalence preserves both endpoints of every geometric dart. -/
theorem cutMapIsoVertexEquiv_endpoints {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) (d : D) :
    cutMapIsoVertexEquiv I (dartTailVertex M d) = dartTailVertex N (I.toEquiv d) ∧
      cutMapIsoVertexEquiv I (dartHeadVertex M d) = dartHeadVertex N (I.toEquiv d) := by
  constructor
  · rfl
  · change dartTailVertex N (I.toEquiv (M.edgeInv d)) =
      dartTailVertex N (N.edgeInv (I.toEquiv d))
    rw [I.edgeInv_comm]

private theorem cut_mapIso_step_map {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) {u v : MapVertex M}
    (h : M.directedStep u v) :
    N.directedStep (cutMapIsoVertexEquiv I u) (cutMapIsoVertexEquiv I v) := by
  obtain ⟨d, hd, ht, hu, hv⟩ := h
  refine ⟨I.toEquiv d, fun hh => hd ((I.missing_iff d).mp hh),
    (I.tail_iff d).mpr ht, ?_, ?_⟩
  · exact (cutMapIsoVertexEquiv_endpoints I d).1.symm.trans
      (congrArg (cutMapIsoVertexEquiv I) hu)
  · exact (cutMapIsoVertexEquiv_endpoints I d).2.symm.trans
      (congrArg (cutMapIsoVertexEquiv I) hv)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The induced vertex equivalence preserves ancestor reachability in both directions. -/
theorem cutMapIsoVertexEquiv_reachable_iff {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) (u v : MapVertex M) :
    Relation.ReflTransGen M.directedStep u v ↔
      Relation.ReflTransGen N.directedStep
        (cutMapIsoVertexEquiv I u) (cutMapIsoVertexEquiv I v) := by
  constructor
  · exact Relation.ReflTransGen.lift (cutMapIsoVertexEquiv I)
      (fun _ _ h => cut_mapIso_step_map I h) u v
  · intro h
    have hh := Relation.ReflTransGen.lift (cutMapIsoVertexEquiv I.symm)
      (fun _ _ h => cut_mapIso_step_map I.symm h) _ _ h
    have hinv (z : MapVertex M) :
        cutMapIsoVertexEquiv I.symm (cutMapIsoVertexEquiv I z) = z := by
      refine Quotient.inductionOn z ?_
      intro d
      change dartTailVertex M (I.toEquiv.symm (I.toEquiv d)) = dartTailVertex M d
      rw [Equiv.symm_apply_apply]
    dsimp only [Function.onFun] at hh
    rw [hinv, hinv] at hh
    exact hh

private theorem cut_stageLR_head_zero (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).LR.head? = some 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (kmswStepOfStep (kmswStage w t) (kmswCodeStep (w t))).LR.head? = _
    cases kmswCodeStep (w t) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w t).LR ++ [(kmswStage w t).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w t)] using ih

private theorem cut_boundaryTarget_stage_map {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (w : ℕ → Fin 3) (t : ℕ)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (hb : ∀ a : ThinMapSide, (boundaryDarts R.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w t).UL
          | .right => (kmswStage w t).LR).map (fun e => (e, false)))
    (a : ThinMapSide) (s : ℕ) :
    (boundaryTarget R.B a s).map
        (fun v => (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id) =
      match s with
      | 0 => some 0
      | i + 1 => ((match a with
          | .left => (kmswStage w t).UL
          | .right => (kmswStage w t).LR)[i]?).map (kmswStage w t).east := by
  have hend (d : Fin R.dartCount) :
      (stageMapVertex w t (cutMapIsoVertexEquiv I (dartHeadVertex R.B.map d))).id =
        stageEndpoint (kmswStage w t)
          ((kmswStageDirectedMap w t).edgeInv (I.toEquiv d)) := by
    rw [(cutMapIsoVertexEquiv_endpoints I d).2]
    rfl
  cases s with
  | zero =>
    let d := R.B.rightPath.firstDart (Nat.zero_lt_of_lt R.B.right_length_pos)
    have hpos : 0 < R.B.rightPath.darts.length := by
      rw [R.B.rightPath.darts_length]
      exact Nat.zero_lt_of_lt R.B.right_length_pos
    have hd : R.B.rightPath.darts[0]? = some d := List.getElem?_eq_getElem hpos
    have hLR : (kmswStage w t).LR[0]? = some 0 := by
      simpa only [List.head?_eq_getElem?] using cut_stageLR_head_zero w t
    have h := congrArg (fun ds => ds[0]?) (hb .right)
    simp only [boundaryDarts, List.getElem?_map, hd, hLR, Option.map_some,
      Option.some.injEq] at h
    have he : (I.toEquiv d).1.val = 0 := congrArg Prod.fst h
    have hs : (I.toEquiv d).2 = false := congrArg Prod.snd h
    have hsource : R.B.source = dartTailVertex R.B.map d :=
      R.B.rightPath.start_vertex.symm.trans
        (R.B.rightPath.edge_step ⟨0, hpos⟩).2.2.1
    simp only [boundaryTarget, Option.map_some, Option.some.injEq]
    rw [hsource, (cutMapIsoVertexEquiv_endpoints I d).1, stageMapVertex_tail]
    change (if (I.toEquiv d).2 then (kmswStage w t).east (I.toEquiv d).1.val
      else (kmswStage w t).west (I.toEquiv d).1.val) = 0
    rw [hs, he]
    exact (initial_edge_endpoints w t).1
  | succ i =>
    have h := congrArg (fun ds => (ds[i]?).map
      (fun p : ℕ × Bool => if p.2 then (kmswStage w t).west p.1
        else (kmswStage w t).east p.1)) (hb a)
    simp only [List.getElem?_map, Option.map_map, Function.comp_def,
      Bool.false_eq_true, ↓reduceIte] at h
    simp only [boundaryTarget, Option.map_map]
    rw [← h]
    apply congrArg (fun f => ((boundaryDarts R.B a)[i]?).map f)
    funext d
    dsimp only [Function.comp_def]
    rw [hend]
    change (if !(I.toEquiv d).2 then (kmswStage w t).east (I.toEquiv d).1.val
      else (kmswStage w t).west (I.toEquiv d).1.val) = _
    cases (I.toEquiv d).2 <;> rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical stage isomorphism preserves both ordered boundary edge lists and -/
theorem cut_walkClassRep_boundary_stage {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) (a : ThinMapSide) :
    (boundaryDarts (kmswWalkClassRep hn c).B a).map
        (fun d => let e := (kmswWalkClassRep_mapIso hn c).toEquiv d
          (e.1.val, e.2)) =
      (match a with
        | .left => (kmswStage (codeExtend c) (n - 1)).UL
        | .right => (kmswStage (codeExtend c) (n - 1)).LR).map
          (fun e => (e, false)) := by
  classical
  let B := kmswWalkClassBase hn c
  have hleft : B.leftPath.darts = kmswStageULDartRun (codeExtend c) (n - 1) := by
    exact (Classical.choose_spec (Classical.choose_spec
      (kmswWalkClassBase_paths hn c))).1
  have hlmap : (kmswWalkClassRep hn c).B.leftPath.darts.map
      (kmswWalkClassRep_mapIso hn c).toEquiv = B.leftPath.darts := by
    let e := Fintype.equivFin
      (StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge)
    change (B.transport e).leftPath.darts.map e.symm = B.leftPath.darts
    rw [← (B.transportIso e).leftDarts]
    simp only [List.map_map]
    simp [BipolarTriangulationWithBoundaryBase.transportIso]
  cases a with
  | left =>
    simp only [boundaryDarts]
    have hh := congrArg (List.map (fun e => (e.1.val, e.2))) hlmap
    calc
      _ = B.leftPath.darts.map (fun e => (e.1.val, e.2)) := by
        simpa only [List.map_map, Function.comp_def] using hh
      _ = _ := by
        rw [hleft]
        simpa only [kmswStageULDartRun] using
          (stageDarts_val (kmswStage (codeExtend c) (n - 1))
            (kmswStage (codeExtend c) (n - 1)).UL false
            (fun e he => stageRun_edge_bound (codeExtend c) (n - 1) e
              (Or.inl (Or.inl (Or.inl he)))))
  | right =>
    simp only [boundaryDarts]
    have hh := congrArg (List.map (fun e => (e.1.val, e.2)))
      (kmswWalkClassRep_rightPath_darts_map hn c)
    calc
      _ = (kmswWalkClassBase hn c).rightPath.darts.map
          (fun e => (e.1.val, e.2)) := by
        simpa only [List.map_map, Function.comp_def] using hh
      _ = _ := by
        rw [kmswWalkClassBase_rightPath_darts]
        exact stageDarts_val _ _ _ _

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A representative of the stopped outputs admits a stage isomorphism carrying both
indexed boundary lists to the original stream's boundary runs, with tail sides. -/
theorem firstHitPastAllCuts_representative_boundary_stageIso
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) (ω : ℕ → Fin 3)
    (hE : ω ∈ boltzmannEvent r) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    ∃ (R : KMSWMapRep (L w t).toNat r t) (d : ℕ)
      (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1))),
      (∀ a : ThinMapSide, (boundaryDarts R.B a).map
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
          (match a with
            | .left => (kmswStage w (t - 1)).UL
            | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) ∧
      firstHitPastAllCuts x r (stoppedMap r hr ω) =
        (some ⟨d, ⟨(L w t).toNat, ⟨(cutLRep R hR).1,
          KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩) := by
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
    exact dite_eq_left ht
  let m : BoltzmannSpace (L w t).toNat r :=
    ⟨t, KMSWMapIsoClass.mk (kmswWalkClassRep ht c)⟩
  obtain ⟨R, hR, hout, hc⟩ := firstHitPastAllCuts_representative x m
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff R (kmswWalkClassRep ht c)).mp hout
  have hp : ∀ i < t - 1, codeExtend c i = w i := by
    intro i hi
    exact (codeExtend_of_lt c i hi).trans (show c.val ⟨i, hi⟩ = w i from rfl)
  let J := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hp
  let K := (cut_baseIso_mapIso I).trans ((kmswWalkClassRep_mapIso ht c).trans J)
  refine ⟨R, xdpLen x m, hR, K, ?_, ?_⟩
  · intro a
    have hb : (boundaryDarts R.B a).map I.toEquiv =
        boundaryDarts (kmswWalkClassRep ht c).B a := by
      cases a with
      | left => exact I.leftDarts
      | right => exact I.rightDarts
    have hj : ∀ d, ((J.toEquiv d).1.val, (J.toEquiv d).2) = (d.1.val, d.2) := by
      intro d
      exact Prod.ext (kmswStageDirectedMapIsoOfPrefix_val _ _ _ hp d).1
        (kmswStageDirectedMapIsoOfPrefix_val _ _ _ hp d).2
    have hstage := kmswStage_eq_of_prefix (codeExtend c) w (t - 1) hp
    calc
      _ = (boundaryDarts R.B a).map
          (fun d => let e := (kmswWalkClassRep_mapIso ht c).toEquiv (I.toEquiv d)
            (e.1.val, e.2)) := by
        apply List.map_congr_left
        intro d _
        exact hj _
      _ = (boundaryDarts (kmswWalkClassRep ht c).B a).map
          (fun d => let e := (kmswWalkClassRep_mapIso ht c).toEquiv d
            (e.1.val, e.2)) := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map (fun d =>
            let e := (kmswWalkClassRep_mapIso ht c).toEquiv d
            (e.1.val, e.2))) hb
      _ = _ := by
        rw [cut_walkClassRep_boundary_stage ht c a, hstage]
  · rw [hmap]
    exact hc

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual representative used by both stopped quotient cuts is isomorphic to
the original stream's past stage, with its full rotation, pairing, orientation,
missing status and outer face. The stage index is the stopping time minus one. -/
theorem firstHitPastAllCuts_representative_stageIso (x : XDP) (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    ∃ (R : KMSWMapRep (L w t).toNat r t) (d : ℕ)
      (hR : xdpLengthBase R.B x = d),
      Nonempty (DirectedMapWithMissingIso R.B.map
        (kmswStageDirectedMap w (t - 1))) ∧
      firstHitPastAllCuts x r (stoppedMap r hr ω) =
        (some ⟨d, ⟨(L w t).toNat, ⟨(cutLRep R hR).1,
          KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩) := by
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
    exact dite_eq_left ht
  let m : BoltzmannSpace (L w t).toNat r :=
    ⟨t, KMSWMapIsoClass.mk (kmswWalkClassRep ht c)⟩
  obtain ⟨R, hR, hout, hc⟩ := firstHitPastAllCuts_representative x m
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff R (kmswWalkClassRep ht c)).mp hout
  let J := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1)
    (fun i hi => (codeExtend_of_lt c i hi).trans (show c.val ⟨i, hi⟩ = w i from rfl))
  refine ⟨R, xdpLen x m, hR,
    ⟨(cut_baseIso_mapIso I).trans ((kmswWalkClassRep_mapIso ht c).trans J)⟩, ?_⟩
  rw [hmap]
  exact hc

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both finite cut outputs retain exactly their original outer-boundary lengths
as the range of existing ancestor targets. -/
theorem firstHitPastAllCuts_halfTruncate_isSome (x : XDP) {ℓ r : ℕ}
    (m : BoltzmannSpace ℓ r) (s : ℕ) :
    ((halfTruncate .left s (firstHitPastAllCuts x r (some ⟨ℓ, m⟩)).1).isSome = true ↔
      s ≤ ℓ) ∧
    ((halfTruncate .right s
      (firstHitPositiveCutEmbedding r (firstHitPastAllCuts x r (some ⟨ℓ, m⟩))).2).isSome =
      true ↔ s ≤ r) := by
  obtain ⟨R, hR, _, hc⟩ := firstHitPastAllCuts_representative x m
  rw [hc]
  constructor
  · exact halfTruncate_isSome_iff _ .left s
  · exact halfTruncate_isSome_iff _ .right s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At a future horizontal minimum, every upper-left record strictly before the cut -/
theorem cut_left_records_eq (w : ℕ → Fin 3) (t : ℕ)
    (hB : ∀ j, t ≤ j → L w t ≤ L w j) :
    ((List.range t).filter
      (fun m => decide (∀ j, m < j → j ≤ t → L w m + 1 ≤ L w j))) =
    ((List.range t).filter
      (fun m => decide (∀ j, m < j → L w m + 1 ≤ L w j))) := by
  classical
  apply List.filter_congr
  intro m hm
  have hmt := List.mem_range.mp hm
  apply decide_eq_decide.mpr
  constructor
  · intro h j hj
    by_cases hjt : j ≤ t
    · exact h j hj hjt
    · exact (h t hmt le_rfl).trans (hB j (by omega))
  · intro h j hj _
    exact h j hj

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The original threshold bounds the activation index of the permanent left boundary -/
theorem cut_leftBoundary_index_before (w : ℕ → Fin 3) (t s : ℕ)
    (hB : ∀ j, t ≤ j → L w t ≤ L w j)
    (hs : (s : ℤ) + 1 ≤ L w t) :
    natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) s < t ∧
      (kmswStage w t).UL[s]? = some (kmswLeftBoundaryEdge w s) := by
  classical
  let p := fun m => decide (∀ j, m < j → j ≤ t → L w m + 1 ≤ L w j)
  let q := fun m => decide (∀ j, m < j → L w m + 1 ≤ L w j)
  have heq : (List.range t).filter p = (List.range t).filter q :=
    cut_left_records_eq w t hB
  have hu : (kmswStage w t).UL = ((List.range t).filter p).map (act w) ++
      [act w t] := by
    rw [kmswStage_UL_eq, List.range_succ, List.filter_append, List.map_append]
    have ht : ∀ j, t < j → j ≤ t → L w t + 1 ≤ L w j := by
      intro j hj hjt
      omega
    simp only [List.filter_cons, List.filter_nil, decide_eq_true ht,
      ite_true, List.map_cons, List.map_nil]
    rfl
  have hlen := congrArg List.length hu
  simp only [List.length_append, List.length_map, List.length_singleton] at hlen
  have hmin := runningMin_le (L w) t 0 (Nat.zero_le t)
  have hzero : L w 0 = 0 := rfl
  change minL w t ≤ L w 0 at hmin
  rw [hzero] at hmin
  have hUL := kmswStage_UL_length w t
  have hsi : s < ((List.range t).filter p).length := by omega
  have hsq : s < ((List.range t).filter q).length := by rwa [← heq]
  have hget := filter_range_getElem?_eq q t s hsq
  have hmem := List.mem_of_getElem? hget
  have hbefore := List.mem_range.mp (List.mem_filter.mp hmem).1
  refine ⟨hbefore, ?_⟩
  rw [hu, List.getElem?_append_left (by simpa only [List.length_map] using hsi),
    List.getElem?_map, heq, hget]
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The original threshold bounds the activation index of the permanent right boundary -/
theorem cut_rightBoundary_index_before (w : ℕ → Fin 3) (t s : ℕ)
    (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hs : (s : ℤ) + 1 ≤ -R w t) :
    natSelect (fun m => ∀ j, j < m → R w m < R w j) s < t ∧
      (kmswStage w t).LR[s]? = some (kmswRightBoundaryEdge w s) := by
  classical
  let p := fun m => decide (∀ j, j < m → R w m < R w j)
  have ht : ∀ j, j < t → R w t < R w j := by
    intro j hj
    have := hA j hj
    omega
  have hr : (kmswStage w t).LR = ((List.range t).filter p).map (act w) ++
      [act w t] := by
    rw [kmswStage_LR_eq, List.range_succ, List.filter_append, List.map_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true ht,
      ite_true, List.map_cons, List.map_nil]
    rfl
  have hlen := congrArg List.length hr
  simp only [List.length_append, List.length_map, List.length_singleton] at hlen
  have hmin := runningMin_le (R w) t t le_rfl
  change minR w t ≤ R w t at hmin
  have hLR := kmswStage_LR_length w t
  have hsi : s < ((List.range t).filter p).length := by omega
  have hget := filter_range_getElem?_eq p t s hsi
  have hmem := List.mem_of_getElem? hget
  have hbefore := List.mem_range.mp (List.mem_filter.mp hmem).1
  refine ⟨hbefore, ?_⟩
  rw [hr, List.getElem?_append_left (by simpa only [List.length_map] using hsi),
    List.getElem?_map, hget]
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The successor-indexed left target is a single limit vertex, with an activation
time strictly before any cut satisfying the original threshold. -/
theorem cut_leftBoundary_target_record (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (t i : ℕ) (hB : ∀ j, t ≤ j → L w t ≤ L w j)
    (hi : ((i + 1 : ℕ) : ℤ) + 1 ≤ L w t) :
    let u := natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) (i + 1)
    u < t ∧ (⟨edgeEast w (kmswLeftBoundaryEdge w i)⟩ : PresentVertex w) =
      recordVertex w u := by
  dsimp only
  refine ⟨(cut_leftBoundary_index_before w t (i + 1) hB hi).1, ?_⟩
  apply congrArg PresentVertex.mk
  rw [(kmswLeftBoundary_infinite_present_path w htrans hL hR).2.1 i]
  exact (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl _))).1.symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The successor-indexed right target is a single limit vertex, with an activation
time strictly before any cut satisfying the original threshold. -/
theorem cut_rightBoundary_target_record (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (t i : ℕ) (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hi : ((i + 1 : ℕ) : ℤ) + 1 ≤ -R w t) :
    let u := natSelect (fun m => ∀ j, j < m → R w m < R w j) (i + 1)
    u < t ∧ (⟨edgeEast w (kmswRightBoundaryEdge w i)⟩ : PresentVertex w) =
      recordVertex w u := by
  dsimp only
  refine ⟨(cut_rightBoundary_index_before w t (i + 1) hA hi).1, ?_⟩
  apply congrArg PresentVertex.mk
  rw [(kmswRightBoundary_infinite_present_path w hL hR).2.1 i]
  exact (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl _))).1.symm

private theorem selectedCut_success_of_threshold
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, DirectedDistances.RandomWalk.IsPositiveSuccessTime
      (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    literalSuccessGraph q.1 (selectedCutTime T (k + 1) q.1).toNat := by
  open DirectedDistances.RandomWalk in
  obtain ⟨_, hl, hf, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let r := selectedCutRank T (k + 1) q.1
  have hz : T 0 q.1 = 0 :=
    (DirectedDistances.RandomWalk.isPositiveSuccessTime_zero_iff _ _).mp (hT q.1 0)
  have hs : selectedCutTime T (k + 1) q.1 = T r q.1 := by
    rw [selectedCutTime, dite_eq_left (hf (k + 1))]
  have hle : T r q.1 ≤ conditionedSecondCoordinateFirstHit (k + 1) q.1 := by
    dsimp only [r, selectedCutRank]
    apply Nat.findGreatest_spec (m := 0)
      (P := fun m => T m q.1 ≤ conditionedSecondCoordinateFirstHit (k + 1) q.1)
    · exact Nat.zero_le _
    · rw [hz]
      exact bot_le
  have hfin : T r q.1 < ⊤ := hle.trans_lt (hf (k + 1))
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    have ht0 : selectedCutTime T (k + 1) q.1 = 0 := by rw [hs, hr0, hz]
    rw [ht0] at hk
    have hright := (le_min_iff.mp hk).2
    change (s : ℤ) + 1 ≤ -(q.1 0).2 at hright
    rw [hl.1] at hright
    change (s : ℤ) + 1 ≤ 0 at hright
    omega
  have hc : T r q.1 = ((T r q.1).toNat : ℕ∞) :=
    (ENat.natCast_toNat hfin.ne).symm
  have hspec := hT q.1 r
  rw [hc] at hspec
  rw [hs]
  exact ((DirectedDistances.RandomWalk.isPositiveSuccessTime_natCast_iff _ hr _).mp
    hspec).2.1

private theorem selectedCut_stoppedMap_boundaries
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let r := (-(selectedCutFuture T (k + 1) q.1 0).2).toNat
    ∃ (hr : 1 ≤ r) (m : AllBoltzmannSpace r),
      stoppedMap r hr (pathCode q.1) = some m ∧ s + 1 ≤ m.1 ∧ s + 1 ≤ r := by
  obtain ⟨_, hl, hf, _, hwp, _, _, _, hL, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  let t := (selectedCutTime T (k + 1) q.1).toNat
  let r := (-(q.1 t).2).toNat
  have hs := selectedCut_success_of_threshold x T hT q k s hk
  have hrz : 0 ≤ -(q.1 t).2 := by
    have h := (le_min_iff.mp hk).2
    dsimp only [t, r] at *
    omega
  have hrcast : (r : ℤ) = -(q.1 t).2 := Int.toNat_of_nonneg hrz
  have hr : s + 1 ≤ r := by
    have h := (le_min_iff.mp hk).2
    dsimp only [t, r] at *
    omega
  have hrpos : 1 ≤ r := by omega
  have hhit : (q.1 t).2 = -(r : ℤ) := by omega
  have hfirst : conditionedSecondCoordinateFirstHit r q.1 = (t : ℕ∞) := by
    have hex : ∃ n, (q.1 n).2 = -(r : ℤ) := ⟨t, hhit⟩
    rw [conditionedSecondCoordinateFirstHit, dite_eq_left hex]
    congr 1
    apply (Nat.find_eq_iff hex).mpr
    refine ⟨hhit, ?_⟩
    intro j hj heq
    have h := hs.1 j hj
    dsimp only [t, r] at *
    omega
  have hconv := firstHit_stoppedCode_conventions r q.1 hl.1 hl.2
    (hfirst ▸ ENat.natCast_lt_top t)
  have htau : boltzmannTau r (pathCode q.1) = t := by
    rw [hconv.2.2.1, hfirst, ENat.toNat_natCast]
  have hw : codeWalk (pathCode q.1) = q.1 := by
    funext j
    rw [codeWalk_pathCode q.1 hl.2 j, hl.1]
    exact sub_zero _
  have hE : pathCode q.1 ∈ boltzmannEvent r := by
    refine ⟨t, ?_, ?_⟩
    · rw [hw]
      exact hhit
    · intro j _
      rw [hw]
      have h := hL j
      rwa [kmsw_L_eq, hwp] at h
  have hpos := (boltzmann_boundary_observable r hrpos (pathCode q.1) hE).1
  let ell := (L (boltzmannKMSWStream (pathCode q.1))
    (boltzmannTau r (pathCode q.1))).toNat
  let c : KMSWWalkClass ell r (boltzmannTau r (pathCode q.1)) :=
    ⟨stoppedWord r (pathCode q.1), (stoppedWord_admissible r hrpos (pathCode q.1) hE).1⟩
  let m : AllBoltzmannSpace r :=
    stoppedWalkMap ⟨⟨boltzmannTau r (pathCode q.1), ell, c⟩, hpos⟩
  have hmap : stoppedMap r hrpos (pathCode q.1) = some m := by
    unfold stoppedMap stoppedIndex
    rw [dite_eq_left hE]
    change stoppedWalkMapOption r
      ⟨boltzmannTau r (pathCode q.1), ell, c⟩ = some m
    exact dite_eq_left hpos
  have hell : s + 1 ≤ m.1 := by
    change s + 1 ≤ ell
    dsimp only [ell]
    rw [htau, kmsw_L_eq, hwp]
    have h := (le_min_iff.mp hk).1
    dsimp only [t, r] at *
    omega
  simpa only [selectedCutFuture, conditionedVectorShift, Nat.add_zero] using
    (show ∃ (h : 1 ≤ r) (m : AllBoltzmannSpace r),
      stoppedMap r h (pathCode q.1) = some m ∧ s + 1 ≤ m.1 ∧ s + 1 ≤ r from
        ⟨hrpos, m, hmap, hell, hr⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected good cut is exactly the positive right-coordinate first hit used
by the stopped-map procedure, on its stopping event. The threshold is `s + 1`. -/
theorem selectedCut_stopped_time
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    s + 1 ≤ r ∧ boltzmannTau r (pathCode q.1) = t ∧
      pathCode q.1 ∈ boltzmannEvent r := by
  obtain ⟨_, hl, _, _, hwp, _, _, _, hL, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  let t := (selectedCutTime T (k + 1) q.1).toNat
  let r := (-(q.1 t).2).toNat
  have hs := selectedCut_success_of_threshold x T hT q k s hk
  have hright := (le_min_iff.mp hk).2
  have hrz : 0 ≤ -(q.1 t).2 := by
    dsimp only [t] at *
    omega
  have hrcast : (r : ℤ) = -(q.1 t).2 := Int.toNat_of_nonneg hrz
  have hr : s + 1 ≤ r := by
    dsimp only [t] at *
    omega
  have hhit : (q.1 t).2 = -(r : ℤ) := by omega
  have hfirst : conditionedSecondCoordinateFirstHit r q.1 = (t : ℕ∞) := by
    have hex : ∃ n, (q.1 n).2 = -(r : ℤ) := ⟨t, hhit⟩
    rw [conditionedSecondCoordinateFirstHit, dite_eq_left hex]
    congr 1
    apply (Nat.find_eq_iff hex).mpr
    refine ⟨hhit, ?_⟩
    intro j hj heq
    have h := hs.1 j hj
    dsimp only [t] at *
    omega
  have htau : boltzmannTau r (pathCode q.1) = t := by
    rw [(firstHit_stoppedCode_conventions r q.1 hl.1 hl.2
      (hfirst ▸ ENat.natCast_lt_top t)).2.2.1, hfirst, ENat.toNat_natCast]
  have hw : codeWalk (pathCode q.1) = q.1 := by
    funext j
    rw [codeWalk_pathCode q.1 hl.2 j, hl.1]
    exact sub_zero _
  refine ⟨hr, htau, t, ?_, ?_⟩
  · rw [hw]
    exact hhit
  · intro j _
    rw [hw]
    have h := hL j
    rwa [kmsw_L_eq, hwp] at h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both actual selected outputs are cuts of one representative isomorphic, as a
directed planar map, to the actual past stage at the selected time minus one.
Both outer-boundary lengths still exceed level `s` at the original threshold. -/
theorem selectedCutPastCuts_representatives_stageIso
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      Nonempty (DirectedMapWithMissingIso R.B.map
        (kmswStageDirectedMap w (t - 1))) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T (k + 1) q.1).toNat
  let r := (-(q.1 t).2).toNat
  obtain ⟨hr, htau, hE⟩ := selectedCut_stopped_time x T hT q k s hk
  have hr' : s + 1 ≤ r := hr
  have hrpos : 1 ≤ r := by omega
  have hc := firstHitPastAllCuts_representative_stageIso x r hrpos (pathCode q.1) hE
  dsimp only at hc
  rw [htau] at hc
  obtain ⟨R, d, hR, hI, hc⟩ := hc
  have hell : s + 1 ≤ (L w t).toNat := by
    obtain ⟨_, _, _, _, hwp, _⟩ := selectedCutCoherentDomain_spec x T hT q
    have hleft := (le_min_iff.mp hk).1
    rw [kmsw_L_eq, hwp]
    dsimp only [t] at *
    omega
  refine ⟨(L w t).toNat, d, R, hR, hell, hr, hI, ?_⟩
  change (if h : 1 ≤ r then firstHitPositiveCutEmbedding r
    (firstHitPastAllCuts x r (stoppedMap r h (pathCode q.1))) else (none, none)) = _
  rw [dite_eq_left hrpos, hc]
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected outputs have a common representative with an isomorphism to their
actual past stage that preserves both indexed boundary lists and dart sides. -/
theorem selectedCutPastCuts_representatives_boundary_stageIso
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1))),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      (∀ a : ThinMapSide, (boundaryDarts R.B a).map
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
          (match a with
            | .left => (kmswStage w (t - 1)).UL
            | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) ∧
      (∀ a i, (boundaryTarget R.B a i).map
          (fun v => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I v)).id) =
        match i with
        | 0 => some 0
        | j + 1 => ((match a with
            | .left => (kmswStage w (t - 1)).UL
            | .right => (kmswStage w (t - 1)).LR)[j]?).map
              (kmswStage w (t - 1)).east) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T (k + 1) q.1).toNat
  let r := (-(q.1 t).2).toNat
  obtain ⟨hr, htau, hE⟩ := selectedCut_stopped_time x T hT q k s hk
  have hr' : s + 1 ≤ r := hr
  have hrpos : 1 ≤ r := by omega
  have hc := firstHitPastAllCuts_representative_boundary_stageIso
    x r hrpos (pathCode q.1) hE
  dsimp only at hc
  rw [htau] at hc
  obtain ⟨R, d, hR, I, hb, hc⟩ := hc
  have hell : s + 1 ≤ (L w t).toNat := by
    obtain ⟨_, _, _, _, hwp, _⟩ := selectedCutCoherentDomain_spec x T hT q
    have hleft := (le_min_iff.mp hk).1
    rw [kmsw_L_eq, hwp]
    dsimp only [t] at *
    omega
  refine ⟨(L w t).toNat, d, R, hR, I, hell, hr, hb,
    cut_boundaryTarget_stage_map R w (t - 1) I hb, ?_⟩
  change (if h : 1 ≤ r then firstHitPositiveCutEmbedding r
    (firstHitPastAllCuts x r (stoppedMap r h (pathCode q.1))) else (none, none)) = _
  rw [dite_eq_left hrpos, hc]
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Under the original threshold, both actual selected outputs are the concrete cuts
of one representative whose two outer boundaries extend strictly beyond level `s`.
This identifies the quotient representatives, without claiming a stage embedding. -/
theorem selectedCutPastCuts_representatives
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    ∃ (ℓ r n d : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = d),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  obtain ⟨hr, ⟨ell, m⟩, hm, hell, hright⟩ :=
    selectedCut_stoppedMap_boundaries x T hT q k s hk
  obtain ⟨R, hR, _, hc⟩ := firstHitPastAllCuts_representative x m
  refine ⟨ell, _, m.1, xdpLen x m, R, hR, hell, hright, ?_⟩
  dsimp only [selectedCutPastCuts]
  rw [dite_eq_left hr, hm, hc]
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At the original threshold both actual selected quotient halves have a truncation.
This proves existence of their finite ancestor targets, not compatibility of classes. -/
theorem selectedCutPastCuts_halfTruncate_isSome
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    (halfTruncate .left s (selectedCutPastCuts x T (k + 1) q.1).1).isSome = true ∧
      (halfTruncate .right s (selectedCutPastCuts x T (k + 1) q.1).2).isSome = true := by
  obtain ⟨hr, m, hm, hell, hright⟩ := selectedCut_stoppedMap_boundaries x T hT q k s hk
  have hc := firstHitPastAllCuts_halfTruncate_isSome x m.2 s
  have hleft := hc.1.mpr (by omega)
  have hright' := hc.2.mpr (by omega)
  dsimp only [selectedCutPastCuts]
  rw [dite_eq_left hr, hm]
  exact ⟨hleft, hright'⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At a good selected cut, both permanent boundary record indices for level `s`
are strictly earlier than the cut, with threshold exactly `s + 1`. -/
theorem selectedCut_boundary_indices_before
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, DirectedDistances.RandomWalk.IsPositiveSuccessTime
      (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    (natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) s < t ∧
      (kmswStage w t).UL[s]? = some (kmswLeftBoundaryEdge w s)) ∧
    (natSelect (fun m => ∀ j, j < m → R w m < R w j) s < t ∧
      (kmswStage w t).LR[s]? = some (kmswRightBoundaryEdge w s)) := by
  obtain ⟨_, _, _, _, hwp, _⟩ := selectedCutCoherentDomain_spec x T hT q
  have hs := selectedCut_success_of_threshold x T hT q k s hk
  have hleft := (le_min_iff.mp hk).1
  have hright := (le_min_iff.mp hk).2
  dsimp only
  constructor
  · apply cut_leftBoundary_index_before
    · intro j hj
      simpa only [kmsw_L_eq, hwp] using hs.2 j hj
    · simpa only [kmsw_L_eq, hwp] using hleft
  · apply cut_rightBoundary_index_before
    · intro j hj
      simpa only [kmsw_R_eq, hwp] using hs.1 j hj
    · simpa only [kmsw_R_eq, hwp] using hright

private theorem boundary_vertices_reach {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M x y n) (i d : ℕ) (hid : i + d ≤ n) :
    Relation.ReflTransGen M.directedStep
      (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
      (P.vertices.get ⟨i + d, by rw [P.vertices_length]; omega⟩) := by
  induction d with
  | zero => exact Relation.ReflTransGen.refl
  | succ d ih =>
      have hs := P.edge_step ⟨i + d, by rw [P.darts_length]; omega⟩
      apply (ih (by omega)).tail
      exact ⟨P.darts.get ⟨i + d, by rw [P.darts_length]; omega⟩,
        hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An ancestor boundary vertex cannot have a larger boundary index than its target.
The path is indexed from its source at zero, as in `halfTruncate`. -/
theorem boundary_ancestor_index_le {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} (hacyclic : M.IsAcyclic)
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n)
    (i j : Fin (n + 1))
    (hji : Relation.ReflTransGen M.directedStep
      (P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩)
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩)) :
    j.val ≤ i.val := by
  by_contra h
  have hij : i.val < j.val := by omega
  have hf := boundary_vertices_reach P i.val (j.val - i.val) (by omega)
  have heq : i.val + (j.val - i.val) = j.val := by omega
  have hf' : Relation.ReflTransGen M.directedStep
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩)
      (P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩) := by
    simpa only [heq] using hf
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hf' with hv | hp
  · have hi := P.vertices_nodup.get_inj_iff.mp hv
    have hval := congrArg Fin.val hi
    change j.val = i.val at hval
    omega
  · exact hacyclic _ (hp.trans_left hji)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A truncation target strictly before the terminal boundary index has no sink among
its ancestors. In particular the natural threshold `s + 1 ≤ n` gives the strict
inequality required for index `s`; it does not require `s + 2` in this convention. -/
theorem boundary_ancestor_ne_sink {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} (hacyclic : M.IsAcyclic)
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n)
    (s : ℕ) (hs : s + 1 ≤ n) (v : MapVertex M)
    (hv : Relation.ReflTransGen M.directedStep v
      (P.vertices.get ⟨s, by rw [P.vertices_length]; omega⟩)) :
    v ≠ y := by
  intro h
  subst v
  have hidx := boundary_ancestor_index_le hacyclic P
    ⟨s, by omega⟩ ⟨n, by omega⟩ (by simpa only [P.end_vertex] using hv)
  change n ≤ s at hidx
  omega

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both endpoints of a boundary dart are ancestors of boundary vertex `s` exactly
when its dart index is strictly below `s`. -/
theorem boundary_ancestor_dart_index_iff {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} (hacyclic : M.IsAcyclic)
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n)
    (s : Fin (n + 1)) (i : Fin P.darts.length) :
    (Relation.ReflTransGen M.directedStep (dartTailVertex M (P.darts.get i))
        (P.vertices.get ⟨s.val, by rw [P.vertices_length]; exact s.isLt⟩) ∧
      Relation.ReflTransGen M.directedStep (dartHeadVertex M (P.darts.get i))
        (P.vertices.get ⟨s.val, by rw [P.vertices_length]; exact s.isLt⟩)) ↔
      i.val < s.val := by
  have hi : i.val < n := by simpa only [P.darts_length] using i.isLt
  have he := P.edge_step i
  rw [← he.2.2.1, ← he.2.2.2]
  constructor
  · intro h
    have hidx := boundary_ancestor_index_le hacyclic P s ⟨i.val + 1, by omega⟩ h.2
    change i.val + 1 ≤ s.val at hidx
    omega
  · intro h
    constructor
    · have hr := boundary_vertices_reach P i.val (s.val - i.val) (by omega)
      simpa only [Nat.add_sub_of_le (by omega : i.val ≤ s.val)] using hr
    · have hr := boundary_vertices_reach P (i.val + 1) (s.val - (i.val + 1))
        (by omega)
      simpa only [Nat.add_sub_of_le (by omega : i.val + 1 ≤ s.val)] using hr

private def cut_path_boundaryTarget {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M x y n) : ℕ → Option (MapVertex M)
  | 0 => some x
  | i + 1 => (P.darts[i]?).map (dartHeadVertex M)

private theorem cut_path_target {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M x y n) (s : ℕ) (hs : s ≤ n) :
    cut_path_boundaryTarget P s =
      some (P.vertices.get ⟨s, by rw [P.vertices_length]; omega⟩) := by
  cases s with
  | zero =>
    change some x = some (P.vertices.get ⟨0, _⟩)
    rw [P.start_vertex]
  | succ i =>
    have hi : i < P.darts.length := by rw [P.darts_length]; omega
    change (P.darts[i]?).map (dartHeadVertex M) = _
    rw [List.getElem?_eq_getElem hi, Option.map_some]
    exact congrArg some (P.edge_step ⟨i, hi⟩).2.2.2.symm

private theorem cut_path_selected_index {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) {N : ℕ}
    (P : SimpleDirectedDartPath R.B.map R.B.source R.B.sink N)
    (s i : ℕ) (t : MapVertex R.B.map) (d : Fin R.dartCount)
    (ht : cut_path_boundaryTarget P s = some t)
    (hd : P.darts[i]? = some d) :
    d ∈ selectedDarts (presentation R a t) ↔ i < s := by
  have hs : s ≤ N := by
    cases s with
    | zero => exact Nat.zero_le _
    | succ j =>
      change (P.darts[j]?).map (dartHeadVertex R.B.map) = some t at ht
      obtain ⟨c, hc, _⟩ := Option.map_eq_some_iff.mp ht
      have hj := (List.getElem?_eq_some_iff.mp hc).1
      rw [P.darts_length] at hj
      omega
  have ht' := cut_path_target P s hs
  rw [ht] at ht'
  have heq := Option.some.inj ht'
  rw [heq]
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hd
  rw [← he]
  exact boundary_ancestor_dart_index_iff R.B.acyclic P ⟨s, by omega⟩ ⟨i, hi⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every existing outer-boundary dart survives the ancestor restriction exactly at -/
theorem boundary_selectedDart_index_iff {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s i : ℕ) (t : MapVertex R.B.map) (d : Fin R.dartCount)
    (ht : boundaryTarget R.B a s = some t)
    (hd : (boundaryDarts R.B a)[i]? = some d) :
    d ∈ selectedDarts (presentation R a t) ↔ i < s := by
  cases a with
  | left => exact cut_path_selected_index R .left R.B.leftPath s i t d ht hd
  | right => exact cut_path_selected_index R .right R.B.rightPath s i t d ht hd

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The surviving outer-boundary marks are exactly the first `s` indices, including -/
theorem boundary_selectedDart_exists_iff {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s i : ℕ) (t : MapVertex R.B.map)
    (ht : boundaryTarget R.B a s = some t) :
    (∃ d : selectedDarts (presentation R a t),
      (boundaryDarts R.B a)[i]? = some d.1) ↔ i < s := by
  constructor
  · rintro ⟨d, hd⟩
    exact (boundary_selectedDart_index_iff R a s i t d.1 ht hd).mp d.2
  · intro hi
    have hsome : (halfTruncate a s
        (some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩)).isSome = true := by
      rw [halfTruncate_some_mk_boundaryTarget, ht]
      rfl
    have hs := (halfTruncate_isSome_iff (KMSWMapIsoClass.mk R) a s).mp hsome
    have hlen : i < (boundaryDarts R.B a).length := by
      cases a with
      | left => simpa only [boundaryDarts, R.B.leftPath.darts_length] using hi.trans_le hs
      | right => simpa only [boundaryDarts, R.B.rightPath.darts_length] using hi.trans_le hs
    let d := (boundaryDarts R.B a)[i]'hlen
    have hd : (boundaryDarts R.B a)[i]? = some d := List.getElem?_eq_getElem hlen
    exact ⟨⟨d, (boundary_selectedDart_index_iff R a s i t d ht hd).mpr hi⟩, hd⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The image of the surviving left outer-boundary marks is exactly the original
boundary before level `s`, with every indexed dart retained. -/
theorem cutLRep_selected_boundary_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) (s i : ℕ)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (hv : boundaryTarget (cutLRep R hR).2.B .left s = some v)
    (e : Fin R.dartCount) :
    (∃ d : selectedDarts (presentation (cutLRep R hR).2 .left v),
      (boundaryDarts (cutLRep R hR).2.B .left)[i]? = some d.1 ∧
        cutLRepDartMap R hR d.1 = e) ↔
      i < s ∧ (boundaryDarts R.B .left)[i]? = some e := by
  have hm := congrArg (fun ds => ds[i]?) (cutLRep_boundaryDarts_map R hR).1
  rw [List.getElem?_map] at hm
  constructor
  · rintro ⟨d, hd, he⟩
    refine ⟨(boundary_selectedDart_index_iff _ .left s i v d.1 hv hd).mp d.2, ?_⟩
    change R.B.leftPath.darts[i]? = some e
    rw [← hm, hd, Option.map_some, he]
  · rintro ⟨hi, he⟩
    change R.B.leftPath.darts[i]? = some e at he
    rw [← hm] at he
    obtain ⟨d, hd, hde⟩ := Option.map_eq_some_iff.mp he
    exact ⟨⟨d, (boundary_selectedDart_index_iff _ .left s i v d hv hd).mpr hi⟩,
      hd, hde⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The image of the surviving right outer-boundary marks is exactly the original
boundary before level `s`, with every indexed dart retained. -/
theorem cutRRep_selected_boundary_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) (s i : ℕ)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (hv : boundaryTarget (cutRRep R hR).2.B .right s = some v)
    (e : Fin R.dartCount) :
    (∃ d : selectedDarts (presentation (cutRRep R hR).2 .right v),
      (boundaryDarts (cutRRep R hR).2.B .right)[i]? = some d.1 ∧
        cutRRepDartMap R hR d.1 = e) ↔
      i < s ∧ (boundaryDarts R.B .right)[i]? = some e := by
  have hm := congrArg (fun ds => ds[i]?) (cutRRep_boundaryDarts_map R hR).1
  rw [List.getElem?_map] at hm
  constructor
  · rintro ⟨d, hd, he⟩
    refine ⟨(boundary_selectedDart_index_iff _ .right s i v d.1 hv hd).mp d.2, ?_⟩
    change R.B.rightPath.darts[i]? = some e
    rw [← hm, hd, Option.map_some, he]
  · rintro ⟨hi, he⟩
    change R.B.rightPath.darts[i]? = some e at he
    rw [← hm] at he
    obtain ⟨d, hd, hde⟩ := Option.map_eq_some_iff.mp he
    exact ⟨⟨d, (boundary_selectedDart_index_iff _ .right s i v d hv hd).mpr hi⟩,
      hd, hde⟩

private theorem cut_path_ancestor_ne_sink {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    {N : ℕ} (P : SimpleDirectedDartPath R.B.map R.B.source R.B.sink N)
    (s : ℕ) (hs : s + 1 ≤ N) (t v : MapVertex R.B.map)
    (ht : cut_path_boundaryTarget P s = some t)
    (hv : Relation.ReflTransGen R.B.map.directedStep v t) : v ≠ R.B.sink := by
  have ht' := cut_path_target P s (by omega)
  rw [ht] at ht'
  have heq := Option.some.inj ht'
  apply boundary_ancestor_ne_sink R.B.acyclic P s hs v
  rwa [← heq]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The unchanged threshold excludes the sink from every ancestor restriction at the -/
theorem boundaryTarget_ancestor_ne_sink {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) (t v : MapVertex R.B.map)
    (hs : s + 1 ≤ (match a with | .left => ℓ | .right => r))
    (ht : boundaryTarget R.B a s = some t)
    (hv : v ∈ ancestors (presentation R a t)) : v ≠ R.B.sink := by
  cases a with
  | left => exact cut_path_ancestor_ne_sink R R.B.leftPath s hs t v ht hv
  | right => exact cut_path_ancestor_ne_sink R R.B.rightPath s hs t v ht hv

private theorem ancestorPath_lift {w : ℕ → Fin 3} {t : ℕ}
    {a b : PresentVertex w} (p : Path a b)
    (hp : ∀ e ∈ pathEdgeList p, e < (kmswStage w t).nextEdge ∧
      (kmswStage w t).present e = true) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w t) ⟨b.id⟩,
      (stageToLimit w t).mapPath q = p := by
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons a b p e ih =>
      have hp' : ∀ f ∈ pathEdgeList p, f < (kmswStage w t).nextEdge ∧
          (kmswStage w t).present f = true := by
        intro f hf
        exact hp f (List.mem_append_left _ hf)
      obtain ⟨q, hq⟩ := ih hp'
      obtain ⟨he, hpres⟩ := hp e.val
        (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      let f : (⟨a.id⟩ : StagePresentVertex w t) ⟶ ⟨b.id⟩ :=
        ⟨e.val, he, hpres,
          (edge_endpoints_eq w he).1.trans e.property.2.1,
          (edge_endpoints_eq w he).2.trans e.property.2.2⟩
      refine ⟨q.cons f, ?_⟩
      rw [Prefunctor.mapPath_cons, hq]
      have hf : (stageToLimit w t).map f = e := Subtype.ext rfl
      exact congrArg (Path.cons p) hf

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ancestor-path confinement: every directed path to the vertex active at `u` already
lies in every stage `t ≥ u`, retaining its edge IDs and entire arrow-valued path.
This graph statement does not identify finite cut halves or their faces. -/
theorem ancestorPath_to_record_lifts_later {w : ℕ → Fin 3} {u t : ℕ}
    (hut : u ≤ t) {a : PresentVertex w} (p : Path a (recordVertex w u)) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w t) ⟨(recordVertex w u).id⟩,
      (stageToLimit w t).mapPath q = p := by
  apply ancestorPath_lift p
  intro e he
  obtain ⟨halloc, hpres⟩ := presentPath_to_record_stage_edges p e he
  exact present_mono w halloc hpres t hut

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The two stage embeddings identify the same ancestor vertices of an earlier active
vertex. This compares directed graphs only, without asserting a marked submap isomorphism. -/
theorem record_ancestor_stages_compatible (w : ℕ → Fin 3) (u t T : ℕ)
    (hut : u ≤ t) (huT : u ≤ T) (a : ℕ) :
    Reachable (⟨a⟩ : StagePresentVertex w t) ⟨(recordVertex w u).id⟩ ↔
      Reachable (⟨a⟩ : StagePresentVertex w T) ⟨(recordVertex w u).id⟩ := by
  constructor
  · intro h
    obtain ⟨p⟩ := stageToLimit_reachable w t h
    obtain ⟨q, _⟩ := ancestorPath_to_record_lifts_later huT p
    exact ⟨q⟩
  · intro h
    obtain ⟨p⟩ := stageToLimit_reachable w T h
    obtain ⟨q, _⟩ := ancestorPath_to_record_lifts_later hut p
    exact ⟨q⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every present edge entering an ancestor of the target is already allocated and
present at the target's record time. Thus edge IDs, as well as ancestor vertices,
are available in every subsequent stage. -/
theorem record_ancestor_incoming_edge_in_stage (w : ℕ → Fin 3) (u t e : ℕ)
    (hut : u ≤ t) (he : EdgePresent w e)
    (hv : Reachable (⟨edgeEast w e⟩ : PresentVertex w) (recordVertex w u)) :
    e < (kmswStage w t).nextEdge ∧ (kmswStage w t).present e = true := by
  obtain ⟨p⟩ := hv
  let f : (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨edgeEast w e⟩ :=
    ⟨e, he, rfl, rfl⟩
  have hm : e ∈ pathEdgeList (f.toPath.comp p) := by
    rw [pathEdgeList_comp]
    apply List.mem_append_left
    exact List.mem_singleton.mpr rfl
  obtain ⟨ha, hp⟩ := presentPath_to_record_stage_edges (f.toPath.comp p) e hm
  exact present_mono w ha hp t hut

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The stage-to-limit embedding identifies the entire ancestor vertex carrier of
an earlier record target in both directions. -/
theorem record_ancestor_reachable_iff_stage (w : ℕ → Fin 3) (u t z : ℕ)
    (hut : u ≤ t) :
    Reachable (⟨z⟩ : StagePresentVertex w t) ⟨(recordVertex w u).id⟩ ↔
      Reachable (⟨z⟩ : PresentVertex w) (recordVertex w u) := by
  constructor
  · exact stageToLimit_reachable w t
  · rintro ⟨p⟩
    obtain ⟨q, _⟩ := ancestorPath_to_record_lifts_later hut p
    exact ⟨q⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An edge whose head is ancestral to the target is already allocated and present
in every later stage. This includes both geometric darts of that edge and does
not require a presence premise: presence follows from the coherent carrier bounds. -/
theorem record_ancestor_geometric_edge_in_stage (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (u t e : ℕ) (hut : u ≤ t)
    (hv : Reachable (⟨edgeEast w e⟩ : PresentVertex w) (recordVertex w u)) :
    e < (kmswStage w t).nextEdge ∧ (kmswStage w t).present e = true := by
  obtain ⟨N, hN⟩ := eventually_present_of_nonneg_of_unbounded w hL hR e
  exact record_ancestor_incoming_edge_in_stage w u t e hut ⟨N, hN N le_rfl⟩ hv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The two raw past-stage ancestor dart carriers are equivalent by unchanged edge
identity and endpoint side. Every inverse dart is available already at the
target's record time. This identifies geometric carriers, before cutting by a seam. -/
@[expose] noncomputable def recordAncestorStageDartEquiv (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (u t T : ℕ) (hut : u ≤ t) (huT : u ≤ T) :
    {d : StageDart (kmswStage w t).nextEdge //
      Reachable (⟨edgeWest w d.1.val⟩ : PresentVertex w) (recordVertex w u) ∧
      Reachable (⟨edgeEast w d.1.val⟩ : PresentVertex w) (recordVertex w u)} ≃
    {d : StageDart (kmswStage w T).nextEdge //
      Reachable (⟨edgeWest w d.1.val⟩ : PresentVertex w) (recordVertex w u) ∧
      Reachable (⟨edgeEast w d.1.val⟩ : PresentVertex w) (recordVertex w u)} where
  toFun d := ⟨(⟨d.1.1.val,
    (record_ancestor_geometric_edge_in_stage w hL hR u T d.1.1.val huT d.2.2).1⟩,
      d.1.2), d.2⟩
  invFun d := ⟨(⟨d.1.1.val,
    (record_ancestor_geometric_edge_in_stage w hL hR u t d.1.1.val hut d.2.2).1⟩,
      d.1.2), d.2⟩
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The ancestor carrier equivalence preserves the geometric edge ID, dart side and
the present flag, including the reverse dart with no tail orientation. -/
theorem recordAncestorStageDartEquiv_fields (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (u t T : ℕ) (hut : u ≤ t) (huT : u ≤ T)
    (d : {d : StageDart (kmswStage w t).nextEdge //
      Reachable (⟨edgeWest w d.1.val⟩ : PresentVertex w) (recordVertex w u) ∧
      Reachable (⟨edgeEast w d.1.val⟩ : PresentVertex w) (recordVertex w u)}) :
    let e := recordAncestorStageDartEquiv w hL hR u t T hut huT
    (e d).1.1.val = d.1.1.val ∧ (e d).1.2 = d.1.2 ∧
      ((kmswStageDirectedMap w T).tail (e d).1 ↔
        (kmswStageDirectedMap w t).tail d.1) := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  have ht := (record_ancestor_geometric_edge_in_stage w hL hR u t d.1.1.val
    hut d.2.2).2
  have hT := (record_ancestor_geometric_edge_in_stage w hL hR u T d.1.1.val
    huT d.2.2).2
  change ((kmswStage w T).present d.1.1.val = true ∧ d.1.2 = false) ↔
    ((kmswStage w t).present d.1.1.val = true ∧ d.1.2 = false)
  simp only [ht, hT, true_and]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both selected-cut boundary targets have one record representative independent of
the cut index, activated strictly before the cut. The target is written as the
tail of edge `s`, agreeing with the head of edge `s - 1` at positive levels. -/
theorem selectedCut_boundary_target_record
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (a : ThinMapSide) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let u := match a with
      | .left => natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) s
      | .right => natSelect (fun m => ∀ j, j < m → R w m < R w j) s
    u < (selectedCutTime T (k + 1) q.1).toNat ∧
      recordVertex w u = (⟨edgeWest w (match a with
        | .left => kmswLeftBoundaryEdge w s
        | .right => kmswRightBoundaryEdge w s)⟩ : PresentVertex w) := by
  have hb := selectedCut_boundary_indices_before x T hT q k s hk
  dsimp only
  cases a with
  | left =>
    refine ⟨hb.1.1, ?_⟩
    apply congrArg PresentVertex.mk
    exact (edge_endpoints_eq _ (act_lt_nextEdge _ (Nat.le_refl _))).1
  | right =>
    refine ⟨hb.2.1, ?_⟩
    apply congrArg PresentVertex.mk
    exact (edge_endpoints_eq _ (act_lt_nextEdge _ (Nat.le_refl _))).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical outer-boundary tail convention includes the source at level zero
and the preceding edge's head at every successor level. -/
theorem boundary_target_tail_eq (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (a : ThinMapSide) (s : ℕ) :
    edgeWest w (match a with
      | .left => kmswLeftBoundaryEdge w s
      | .right => kmswRightBoundaryEdge w s) =
    match s with
    | 0 => 0
    | i + 1 => edgeEast w (match a with
      | .left => kmswLeftBoundaryEdge w i
      | .right => kmswRightBoundaryEdge w i) := by
  cases a with
  | left =>
    cases s with
    | zero => exact (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.1
    | succ i => exact ((kmswLeftBoundary_infinite_present_path w htrans hL hR).2.1 i).symm
  | right =>
    cases s with
    | zero => exact (kmswRightBoundary_infinite_present_path w hL hR).2.2.1
    | succ i => exact ((kmswRightBoundary_infinite_present_path w hL hR).2.1 i).symm

private theorem cut_predecessor_boundary_prefix (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n + 1, R w (n + 1) ≤ R w j - 1) :
    (∃ d, (kmswStage w (n + 1)).UL = (kmswStage w n).UL ++ [d]) ∧
      (∃ ds, ds.length ≤ 1 ∧
        (kmswStage w (n + 1)).LR = (kmswStage w n).LR ++ ds) := by
  have hc : R w (n + 1) = R w n +
      (lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  have hn := hA n (by omega)
  have hw : w n = 2 := by
    have hh : w n = 0 ∨ w n = 1 ∨ w n = 2 := by
      have := (w n).isLt
      omega
    rcases hh with h | h | h
    · rw [h, lazyTwoDimensionalStep_zero] at hc
      dsimp only at hc
      omega
    · rw [h, lazyTwoDimensionalStep_one] at hc
      dsimp only at hc
      omega
    · exact h
  simp only [kmswStage, kmswStep, hw, kmswCodeStep,
    show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
  cases hu : (kmswStage w n).UR with
  | nil =>
      simp only [kmswStepOfStep, hu]
      exact ⟨⟨_, rfl⟩, ⟨[(kmswStage w n).nextEdge], le_rfl, rfl⟩⟩
  | cons d ds =>
      simp only [kmswStepOfStep, hu]
      exact ⟨⟨d, rfl⟩, ⟨[], by decide, (List.append_nil _).symm⟩⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every boundary dart before the target level in the actual past stage is the
permanent boundary dart, at the unchanged threshold `s + 1`. -/
theorem selectedCut_past_boundary_dart_record
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (a : ThinMapSide) (k s i : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (hi : i < s) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    (match a with
      | .left => (kmswStage w (t - 1)).UL
      | .right => (kmswStage w (t - 1)).LR)[i]? =
        some (match a with
          | .left => kmswLeftBoundaryEdge w i
          | .right => kmswRightBoundaryEdge w i) := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T (k + 1) q.1).toNat
  obtain ⟨_, _, _, _, hwp, _⟩ := selectedCutCoherentDomain_spec x T hT q
  have hb := selectedCut_boundary_indices_before x T hT q k s hk
  have ht : 0 < t := by
    have h : _ < t := hb.1.1
    omega
  have hsucc : t - 1 + 1 = t := by omega
  have hs := selectedCut_success_of_threshold x T hT q k s hk
  have hA : ∀ j < t - 1 + 1, R w (t - 1 + 1) ≤ R w j - 1 := by
    intro j hj
    rw [hsucc]
    dsimp only [w, t]
    simpa only [kmsw_R_eq, hwp] using hs.1 j (by simpa only [hsucc] using hj)
  have hp := cut_predecessor_boundary_prefix w (t - 1) hA
  rw [hsucc] at hp
  have hki : (i : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) := by omega
  have hb' := selectedCut_boundary_indices_before x T hT q k i hki
  cases a with
  | left =>
      obtain ⟨d, hd⟩ := hp.1
      have hidx := (List.getElem?_eq_some_iff.mp hb.1.2).1
      change s < (kmswStage w t).UL.length at hidx
      rw [hd, List.length_append, List.length_singleton] at hidx
      have hh := hb'.1.2
      change (kmswStage w t).UL[i]? = _ at hh
      rwa [hd, List.getElem?_append_left (by omega)] at hh
  | right =>
      obtain ⟨ds, hds, hd⟩ := hp.2
      have hidx := (List.getElem?_eq_some_iff.mp hb.2.2).1
      change s < (kmswStage w t).LR.length at hidx
      rw [hd, List.length_append] at hidx
      have hh := hb'.2.2
      change (kmswStage w t).LR[i]? = _ at hh
      rwa [hd, List.getElem?_append_left (by omega)] at hh




theorem selectedCut_past_boundary_target_record
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (a : ThinMapSide) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    (match s with
      | 0 => some 0
      | i + 1 => ((match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR)[i]?).map
            (kmswStage w (t - 1)).east) =
      some (edgeWest w (match a with
        | .left => kmswLeftBoundaryEdge w s
        | .right => kmswRightBoundaryEdge w s)) := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T (k + 1) q.1).toNat
  obtain ⟨_, _, _, _, hwp, _, htrans, hR, hL, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  have ht : 0 < t := by
    have h := (selectedCut_boundary_indices_before x T hT q k s hk).1.1
    change _ < t at h
    omega
  have hsucc : t - 1 + 1 = t := by omega
  have hs := selectedCut_success_of_threshold x T hT q k s hk
  have hA : ∀ j < t - 1 + 1, R w (t - 1 + 1) ≤ R w j - 1 := by
    intro j hj
    rw [hsucc]
    dsimp only [w, t]
    simpa only [kmsw_R_eq, hwp] using hs.1 j (by simpa only [hsucc] using hj)
  have hp := cut_predecessor_boundary_prefix w (t - 1) hA
  rw [hsucc] at hp
  have hb := selectedCut_boundary_indices_before x T hT q k s hk
  have htail := boundary_target_tail_eq w htrans hL hR a s
  change (s : ℤ) + 1 ≤ min ((q.1 t).1) (-(q.1 t).2) at hk
  dsimp only
  rw [htail]
  cases s with
  | zero => rfl
  | succ i =>
      dsimp only
      have he : ((match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR)[i]?) =
          some (match a with
            | .left => kmswLeftBoundaryEdge w i
            | .right => kmswRightBoundaryEdge w i) := by
        have hi : (i : ℤ) + 1 ≤
            min ((q.1 t).1) (-(q.1 t).2) := by
          change ((i + 1 : ℕ) : ℤ) + 1 ≤ _ at hk
          omega
        have hb' := selectedCut_boundary_indices_before x T hT q k i hi
        cases a with
        | left =>
            obtain ⟨d, hd⟩ := hp.1
            have hidx := (List.getElem?_eq_some_iff.mp hb.1.2).1
            change i + 1 < (kmswStage w t).UL.length at hidx
            rw [hd, List.length_append, List.length_singleton] at hidx
            have hh := hb'.1.2
            change (kmswStage w t).UL[i]? = _ at hh
            rwa [hd, List.getElem?_append_left (by omega)] at hh
        | right =>
            obtain ⟨ds, hds, hd⟩ := hp.2
            have hidx := (List.getElem?_eq_some_iff.mp hb.2.2).1
            change i + 1 < (kmswStage w t).LR.length at hidx
            rw [hd, List.length_append] at hidx
            have hh := hb'.2.2
            change (kmswStage w t).LR[i]? = _ at hh
            rwa [hd, List.getElem?_append_left (by omega)] at hh
      dsimp only at he
      change (((match a with
        | .left => (kmswStage w (t - 1)).UL
        | .right => (kmswStage w (t - 1)).LR)[i]?).map
          (kmswStage w (t - 1)).east) = _
      rw [he, Option.map_some]
      congr 1
      have hm := List.mem_of_getElem? he
      cases a with
      | left =>
          exact (edge_endpoints_eq w
            ((kmswStage_boundary_ids_lt_nextEdge w (t - 1)).2 _
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm))))).2
      | right =>
          exact (edge_endpoints_eq w
            ((kmswStage_boundary_ids_lt_nextEdge w (t - 1)).2 _
              (List.mem_append_right _ hm))).2

private theorem cut_stage_reachable_iff (w : ℕ → Fin 3) (n : ℕ)
    (u v : MapVertex (kmswStageDirectedMap w n)) :
    Relation.ReflTransGen (kmswStageDirectedMap w n).directedStep u v ↔
      Reachable (stageMapVertex w n u) (stageMapVertex w n v) := by
  constructor
  · intro h
    induction h with
    | refl => exact Reachable.rfl
    | tail _ hstep ih =>
        obtain ⟨e⟩ := (stageMap_directedStep_iff w n _ _).mp hstep
        exact ih.trans e.reachable
  · rintro ⟨p⟩
    obtain ⟨P⟩ := (stageMap_path_iff w n p.length u v).mpr ⟨p, rfl⟩
    have h := boundary_vertices_reach P 0 p.length (by omega)
    simpa only [Nat.zero_add, P.start_vertex, P.end_vertex] using h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual selected halves have a common finite base whose indexed level target
maps to the permanent boundary vertex, with bidirectional ambient ancestor
reachability. Both full boundary lists remain aligned. -/
theorem selectedCutPastCuts_representatives_record_stageIso
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1))),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      (∀ a : ThinMapSide, (boundaryDarts R.B a).map
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
          (match a with
            | .left => (kmswStage w (t - 1)).UL
            | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) ∧
      (∀ a : ThinMapSide, ∃ v : MapVertex R.B.map,
        boundaryTarget R.B a s = some v ∧
        (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I v)).id =
          edgeWest w (match a with
            | .left => kmswLeftBoundaryEdge w s
            | .right => kmswRightBoundaryEdge w s) ∧
        ∀ z : MapVertex R.B.map,
          z ∈ ancestors (presentation R a v) ↔
            Reachable (⟨(stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I z)).id⟩ :
              PresentVertex w) ⟨edgeWest w (match a with
                | .left => kmswLeftBoundaryEdge w s
                | .right => kmswRightBoundaryEdge w s)⟩) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, R, hR, I, hℓ, hr, hb, ht, hc⟩ :=
    selectedCutPastCuts_representatives_boundary_stageIso x T hT q k s hk
  refine ⟨ℓ, d, R, hR, I, hℓ, hr, hb, ?_, hc⟩
  intro a
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T (k + 1) q.1).toNat
  let b := edgeWest w (match a with
    | .left => kmswLeftBoundaryEdge w s
    | .right => kmswRightBoundaryEdge w s)
  have htarget : (boundaryTarget R.B a s).map
      (fun v => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I v)).id) =
        some b := by
    have hp := selectedCut_past_boundary_target_record x T hT q a k s hk
    cases s <;> exact (ht a _).trans hp
  obtain ⟨v, hv, hvid⟩ := Option.map_eq_some_iff.mp htarget
  refine ⟨v, hv, hvid, ?_⟩
  intro z
  change Relation.ReflTransGen R.B.map.directedStep z v ↔ _
  rw [cutMapIsoVertexEquiv_reachable_iff I, cut_stage_reachable_iff]
  have hvobj : stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I v) = ⟨b⟩ :=
    congrArg StagePresentVertex.mk hvid
  rw [hvobj]
  let u := match a with
    | .left => natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) s
    | .right => natSelect (fun m => ∀ j, j < m → KMSW.R w m < KMSW.R w j) s
  have hb := selectedCut_boundary_target_record x T hT q a k s hk
  have hut : u ≤ t - 1 := by
    have hh : u < t := hb.1
    omega
  have hh := record_ancestor_reachable_iff_stage w u (t - 1)
    (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I z)).id hut
  have hu : recordVertex w u = (⟨b⟩ : PresentVertex w) := hb.2
  rw [hu] at hh
  exact hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both actual selected half targets map to their permanent boundary vertices.
Every half ancestor maps to a limit ancestor of that same target. This is the
forward inclusion only; it does not identify the two cuts' selected half-carriers. -/
theorem selectedCutPastCuts_representatives_half_ancestors
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
      (vL : MapVertex (cutLRep R hR).2.B.map)
      (vR : MapVertex (cutRRep R hR).2.B.map),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      boundaryTarget (cutLRep R hR).2.B .left s = some vL ∧
      boundaryTarget (cutRRep R hR).2.B .right s = some vR ∧
      (stageMapVertex w (t - 1)
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR vL))).id =
          edgeWest w (kmswLeftBoundaryEdge w s) ∧
      (stageMapVertex w (t - 1)
        (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR vR))).id =
          edgeWest w (kmswRightBoundaryEdge w s) ∧
      (∀ z : MapVertex (cutLRep R hR).2.B.map,
        z ∈ ancestors (presentation (cutLRep R hR).2 .left vL) →
          Reachable (⟨(stageMapVertex w (t - 1)
            (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR z))).id⟩ : PresentVertex w)
              ⟨edgeWest w (kmswLeftBoundaryEdge w s)⟩) ∧
      (∀ z : MapVertex (cutRRep R hR).2.B.map,
        z ∈ ancestors (presentation (cutRRep R hR).2 .right vR) →
          Reachable (⟨(stageMapVertex w (t - 1)
            (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z))).id⟩ : PresentVertex w)
              ⟨edgeWest w (kmswRightBoundaryEdge w s)⟩) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, R, hR, I, hℓ, hr, _, ht, hc⟩ :=
    selectedCutPastCuts_representatives_record_stageIso x T hT q k s hk
  obtain ⟨bL, hbL, hidL, hancL⟩ := ht .left
  obtain ⟨bR, hbR, hidR, hancR⟩ := ht .right
  have hL := cutLRep_boundaryTarget_map R hR s
  have hR' := cutRRep_boundaryTarget_map R hR s
  rw [hbL] at hL
  rw [hbR] at hR'
  obtain ⟨vL, hvL, heL⟩ := Option.map_eq_some_iff.mp hL
  obtain ⟨vR, hvR, heR⟩ := Option.map_eq_some_iff.mp hR'
  refine ⟨ℓ, d, R, hR, I, vL, vR, hℓ, hr, hvL, hvR, ?_, ?_, ?_, ?_, hc⟩
  · rw [heL]
    exact hidL
  · rw [heR]
    exact hidR
  · intro z hz
    apply (hancL _).mp
    have hh := cutLRep_ancestors_map R hR z vL hz
    rwa [heL] at hh
  · intro z hz
    apply (hancR _).mp
    have hh := cutRRep_ancestors_map R hR z vR hz
    rwa [heR] at hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ancestor reachability to the common indexed boundary target agrees in the actual
past stages of any two good selected cuts. This is a graph statement, not yet an
isomorphism of marked half-map restrictions. -/
theorem selectedCut_boundary_ancestor_stages_compatible
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (a : ThinMapSide) (s k K z : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (hK : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let b := edgeWest w (match a with
      | .left => kmswLeftBoundaryEdge w s
      | .right => kmswRightBoundaryEdge w s)
    Reachable (⟨z⟩ : StagePresentVertex w
      ((selectedCutTime T (k + 1) q.1).toNat - 1)) ⟨b⟩ ↔
    Reachable (⟨z⟩ : StagePresentVertex w
      ((selectedCutTime T (K + 1) q.1).toNat - 1)) ⟨b⟩ := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let u := match a with
    | .left => natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) s
    | .right => natSelect (fun m => ∀ j, j < m → R w m < R w j) s
  have hk' := selectedCut_boundary_target_record x T hT q a k s hk
  have hK' := selectedCut_boundary_target_record x T hT q a K s hK
  have hv := congrArg PresentVertex.id hk'.2
  have huk : u ≤ (selectedCutTime T (k + 1) q.1).toNat - 1 := by
    have h : u < (selectedCutTime T (k + 1) q.1).toNat := hk'.1
    omega
  have huK : u ≤ (selectedCutTime T (K + 1) q.1).toNat - 1 := by
    have h : u < (selectedCutTime T (K + 1) q.1).toNat := hK'.1
    omega
  have hc := record_ancestor_stages_compatible w u
    ((selectedCutTime T (k + 1) q.1).toNat - 1)
    ((selectedCutTime T (K + 1) q.1).toNat - 1) huk huK z
  cases a <;> simpa only [u, w, hv] using hc

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric ancestor dart carriers in the actual past stages of two good cuts
are equivalent, preserving edge IDs, endpoint sides and orientations in both
directions. This compares the uncut stages, before selecting a half of the seam. -/
theorem selectedCut_boundary_ancestor_stage_darts_compatible
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (a : ThinMapSide) (s k K : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (hK : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let b := edgeWest w (match a with
      | .left => kmswLeftBoundaryEdge w s
      | .right => kmswRightBoundaryEdge w s)
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    let t' := (selectedCutTime T (K + 1) q.1).toNat - 1
    ∃ e : {d : StageDart (kmswStage w t).nextEdge //
        Reachable (⟨edgeWest w d.1.val⟩ : PresentVertex w) ⟨b⟩ ∧
        Reachable (⟨edgeEast w d.1.val⟩ : PresentVertex w) ⟨b⟩} ≃
      {d : StageDart (kmswStage w t').nextEdge //
        Reachable (⟨edgeWest w d.1.val⟩ : PresentVertex w) ⟨b⟩ ∧
        Reachable (⟨edgeEast w d.1.val⟩ : PresentVertex w) ⟨b⟩},
      ∀ d, (e d).1.1.val = d.1.1.val ∧ (e d).1.2 = d.1.2 ∧
        ((kmswStageDirectedMap w t').tail (e d).1 ↔
          (kmswStageDirectedMap w t).tail d.1) := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let u := match a with
    | .left => natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) s
    | .right => natSelect (fun m => ∀ j, j < m → R w m < R w j) s
  have hb := selectedCut_boundary_target_record x T hT q a k s hk
  have hB := selectedCut_boundary_target_record x T hT q a K s hK
  have hut : u ≤ (selectedCutTime T (k + 1) q.1).toNat - 1 := by
    have h : u < (selectedCutTime T (k + 1) q.1).toNat := hb.1
    omega
  have huT : u ≤ (selectedCutTime T (K + 1) q.1).toNat - 1 := by
    have h : u < (selectedCutTime T (K + 1) q.1).toNat := hB.1
    omega
  obtain ⟨_, _, _, _, _, _, _, hR, hL, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  dsimp only
  rw [← hb.2]
  exact ⟨recordAncestorStageDartEquiv w hL hR u _ _ hut huT,
    recordAncestorStageDartEquiv_fields w hL hR u _ _ hut huT⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual selected half representatives preserve every surviving outer-boundary
index as the permanent edge ID and its dart side. This is boundary transport,
not equality of the full ancestor carriers or marked restrictions. -/
theorem selectedCutPastCuts_representatives_half_boundary_darts
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1))),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      (∀ i < s,
        ((boundaryDarts (cutLRep R hR).2.B .left)[i]?).map
          (fun e => ((I.toEquiv (cutLRepDartMap R hR e)).1.val,
            (I.toEquiv (cutLRepDartMap R hR e)).2)) =
              some (kmswLeftBoundaryEdge w i, false)) ∧
      (∀ i < s,
        ((boundaryDarts (cutRRep R hR).2.B .right)[i]?).map
          (fun e => ((I.toEquiv (cutRRepDartMap R hR e)).1.val,
            (I.toEquiv (cutRRepDartMap R hR e)).2)) =
              some (kmswRightBoundaryEdge w i, false)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, R, hR, I, hℓ, hr, hb, _, hc⟩ :=
    selectedCutPastCuts_representatives_boundary_stageIso x T hT q k s hk
  refine ⟨ℓ, d, R, hR, I, hℓ, hr, ?_, ?_, hc⟩
  · intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q .left k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb .left)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (cutLRep_boundaryDarts_map R hR).1
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    exact hm.trans hs
  · intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q .right k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb .right)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (cutRRep_boundaryDarts_map R hR).1
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    exact hm.trans hs

private theorem cut_boundaryTarget_exists {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ)
    (hs : s ≤ (match a with | .left => ℓ | .right => r)) :
    ∃ v, boundaryTarget R.B a s = some v := by
  cases a with
  | left => exact ⟨_, cut_path_target R.B.leftPath s hs⟩
  | right => exact ⟨_, cut_path_target R.B.rightPath s hs⟩

private theorem cut_boundary_marked_image {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) (v : MapVertex R.B.map)
    (hv : boundaryTarget R.B a s = some v) {A : Type*} (f : Fin R.dartCount → A)
    (b : ℕ → A) (hp : ∀ i < s, ((boundaryDarts R.B a)[i]?).map f = some (b i))
    (i : ℕ) (z : A) :
    (∃ d : selectedDarts (presentation R a v),
      (boundaryDarts R.B a)[i]? = some d.1 ∧ f d.1 = z) ↔
        i < s ∧ z = b i := by
  constructor
  · rintro ⟨d, hd, hz⟩
    have hi := (boundary_selectedDart_index_iff R a s i v d.1 hv hd).mp d.2
    have hh := hp i hi
    rw [hd, Option.map_some] at hh
    exact ⟨hi, hz.symm.trans (Option.some.inj hh)⟩
  · rintro ⟨hi, hz⟩
    obtain ⟨d, hd⟩ := (boundary_selectedDart_exists_iff R a s i v hv).mpr hi
    have hh := hp i hi
    rw [hd, Option.map_some] at hh
    exact ⟨d, hd, (Option.some.inj hh).trans hz.symm⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The two actual selected half restrictions have exactly the permanent marked
boundary-dart images at indices `i < s`, in both directions and for every index.
This identifies the boundary portion of each carrier, not its interior or seam. -/
theorem selectedCutPastCuts_representatives_half_boundary_images
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
      (vL : MapVertex (cutLRep R hR).2.B.map)
      (vR : MapVertex (cutRRep R hR).2.B.map),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      boundaryTarget (cutLRep R hR).2.B .left s = some vL ∧
      boundaryTarget (cutRRep R hR).2.B .right s = some vR ∧
      (∀ (i : ℕ) (z : ℕ × Bool),
        (∃ e : selectedDarts (presentation (cutLRep R hR).2 .left vL),
          (boundaryDarts (cutLRep R hR).2.B .left)[i]? = some e.1 ∧
            ((I.toEquiv (cutLRepDartMap R hR e.1)).1.val,
              (I.toEquiv (cutLRepDartMap R hR e.1)).2) = z) ↔
          i < s ∧ z = (kmswLeftBoundaryEdge w i, false)) ∧
      (∀ (i : ℕ) (z : ℕ × Bool),
        (∃ e : selectedDarts (presentation (cutRRep R hR).2 .right vR),
          (boundaryDarts (cutRRep R hR).2.B .right)[i]? = some e.1 ∧
            ((I.toEquiv (cutRRepDartMap R hR e.1)).1.val,
              (I.toEquiv (cutRRepDartMap R hR e.1)).2) = z) ↔
          i < s ∧ z = (kmswRightBoundaryEdge w i, false)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, R, hR, I, hℓ, hr, hL, hR', hc⟩ :=
    selectedCutPastCuts_representatives_half_boundary_darts x T hT q k s hk
  obtain ⟨vL, hvL⟩ := cut_boundaryTarget_exists (cutLRep R hR).2 .left s
    (by dsimp only; omega)
  obtain ⟨vR, hvR⟩ := cut_boundaryTarget_exists (cutRRep R hR).2 .right s
    (by dsimp only; omega)
  refine ⟨ℓ, d, R, hR, I, vL, vR, hℓ, hr, hvL, hvR, ?_, ?_, hc⟩
  · exact cut_boundary_marked_image _ .left s vL hvL _ _ hL
  · exact cut_boundary_marked_image _ .right s vR hvR _ _ hR'



theorem halfTruncate_cut_eq_zero
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (k K : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (1 : ℤ) ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (hK : (1 : ℤ) ≤
      min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2)) :
    halfTruncate a 0 (match a with
      | .left => (selectedCutPastCuts x T (k + 1) q.1).1
      | .right => (selectedCutPastCuts x T (k + 1) q.1).2) =
    halfTruncate a 0 (match a with
      | .left => (selectedCutPastCuts x T (K + 1) q.1).1
      | .right => (selectedCutPastCuts x T (K + 1) q.1).2) := by
  obtain ⟨ℓ, r, n, d, R, hR, _, _, hc⟩ :=
    selectedCutPastCuts_representatives x T hT q k 0 hk
  obtain ⟨ℓ', r', n', d', S, hS, _, _, hc'⟩ :=
    selectedCutPastCuts_representatives x T hT q K 0 hK
  rw [hc, hc']
  cases a with
  | left =>
    rw [halfTruncate_some_mk, halfTruncate_some_mk]
    exact congrArg some (finiteThinMapOfAncestors_source_eq _ _ .left .left)
  | right =>
    rw [halfTruncate_some_mk, halfTruncate_some_mk]
    exact congrArg some (finiteThinMapOfAncestors_source_eq _ _ .right .right)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every good cut follows the canonical least good cut in cut index. -/
theorem leastGoodCut_le
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    leastGoodCut x T hT s q ≤ k := by
  exact Nat.find_min' (exists_selectedCut_goodEvent x T hT s q) hk

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical least good cut's past stage precedes every good cut's past stage.
The original threshold is unchanged, and no compatibility premise is used. -/
theorem leastGoodCut_past_time_le
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    (selectedCutTime T (leastGoodCut x T hT s q + 1) q.1).toNat - 1 ≤
      (selectedCutTime T (k + 1) q.1).toNat - 1 := by
  rcases (leastGoodCut_le x T hT s k q hk).lt_or_eq with hlt | heq
  · obtain ⟨o, _, ho⟩ := selectedCutTime_future_recovery x T hT
      (leastGoodCut x T hT s q) k hlt
    have ht := (ho q).1
    omega
  · rw [heq]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical least-good-cut decoder is an existing finite marked class at every
level; no compatibility with another cut is asserted. -/
theorem thinTruncationAt_isSome
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) :
    (thinTruncationAt x T hT a s q).isSome = true := by
  have h := selectedCutPastCuts_halfTruncate_isSome x T hT q
    (leastGoodCut x T hT s q) s (leastGoodCut_spec x T hT s q)
  cases a with
  | left => exact h.1
  | right => exact h.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical least good cut agrees with every good cut at level zero, with
threshold exactly one and no compatibility premise. -/
theorem halfTruncate_cut_eq_leastGood_zero
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (1 : ℤ) ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    halfTruncate a 0 (selectedCutSide x T a (leastGoodCut x T hT 0 q) q.1) =
      halfTruncate a 0 (selectedCutSide x T a k q.1) := by
  exact halfTruncate_cut_eq_zero x T hT a (leastGoodCut x T hT 0 q) k q
    (leastGoodCut_spec x T hT 0 q) hk

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual canonical decoder equals every good cut's truncation at level zero.
This is unconditional geometric compatibility at zero only. -/
theorem thinTruncationAt_decode_zero
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (1 : ℤ) ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    thinTruncationAt x T hT a 0 q =
      halfTruncate a 0 (selectedCutSide x T a k q.1) := by
  exact halfTruncate_cut_eq_leastGood_zero x T hT a k q hk

private theorem cut_path_selected_head_iff {ℓ r n N : ℕ}
    (R : KMSWMapRep ℓ r n) (a : ThinMapSide)
    (P : SimpleDirectedDartPath R.B.map R.B.source R.B.sink N)
    (t : MapVertex R.B.map) (i : ℕ) (d : Fin R.dartCount)
    (hd : P.darts[i]? = some d) :
    d ∈ selectedDarts (presentation R a t) ↔
      dartHeadVertex R.B.map d ∈ ancestors (presentation R a t) := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hd
  have hs := P.edge_step ⟨i, hi⟩
  have htail : R.B.map.tail d := he ▸ hs.2.1
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Relation.ReflTransGen.head
      ⟨d, R.B.noMissingDarts d, htail, rfl, rfl⟩ h, h⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A seam dart survives exactly when its head can reach the outer-boundary target.
This does not identify its seam index with the outer-boundary level. -/
theorem seam_selectedDart_head_iff {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (t : MapVertex R.B.map) (i : ℕ) (d : Fin R.dartCount)
    (hd : (boundaryDarts R.B (oppositeSide a))[i]? = some d) :
    d ∈ selectedDarts (presentation R a t) ↔
      dartHeadVertex R.B.map d ∈ ancestors (presentation R a t) := by
  cases a with
  | left => exact cut_path_selected_head_iff R .left R.B.rightPath t i d hd
  | right => exact cut_path_selected_head_iff R .right R.B.leftPath t i d hd

private theorem cut_path_selected_prefix {ℓ r n N : ℕ}
    (R : KMSWMapRep ℓ r n) (a : ThinMapSide)
    (P : SimpleDirectedDartPath R.B.map R.B.source R.B.sink N)
    (t : MapVertex R.B.map) (i j : ℕ) (hij : i ≤ j)
    (d e : Fin R.dartCount) (hd : P.darts[i]? = some d)
    (he : P.darts[j]? = some e)
    (he' : e ∈ selectedDarts (presentation R a t)) :
    d ∈ selectedDarts (presentation R a t) := by
  apply (cut_path_selected_head_iff R a P t i d hd).mpr
  obtain ⟨hi, hid⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.mp he
  have hjN : j < N := by simpa only [P.darts_length] using hj
  have hreach := boundary_vertices_reach P (i + 1) (j - i) (by omega)
  have heq : i + 1 + (j - i) = j + 1 := by omega
  have hreach' : Relation.ReflTransGen R.B.map.directedStep
      (P.vertices.get ⟨i + 1, by rw [P.vertices_length]; omega⟩)
      (P.vertices.get ⟨j + 1, by rw [P.vertices_length]; omega⟩) := by
    simpa only [heq] using hreach
  have hid' : P.darts.get ⟨i, hi⟩ = d := hid
  have hje' : P.darts.get ⟨j, hj⟩ = e := hje
  have hdi := (P.edge_step ⟨i, hi⟩).2.2.2.trans
    (congrArg (dartHeadVertex R.B.map) hid')
  have hej := (P.edge_step ⟨j, hj⟩).2.2.2.trans
    (congrArg (dartHeadVertex R.B.map) hje')
  rw [hdi, hej] at hreach'
  exact hreach'.trans he'.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every earlier seam dart survives whenever a later seam dart survives. -/
theorem seam_selectedDart_prefix {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (t : MapVertex R.B.map) (i j : ℕ) (hij : i ≤ j)
    (he : ∃ e : selectedDarts (presentation R a t),
      (boundaryDarts R.B (oppositeSide a))[j]? = some e.1) :
    ∃ d : selectedDarts (presentation R a t),
      (boundaryDarts R.B (oppositeSide a))[i]? = some d.1 := by
  obtain ⟨e, he⟩ := he
  have hj := (List.getElem?_eq_some_iff.mp he).1
  have hi : i < (boundaryDarts R.B (oppositeSide a)).length := by omega
  let d := (boundaryDarts R.B (oppositeSide a))[i]'hi
  have hd : (boundaryDarts R.B (oppositeSide a))[i]? = some d :=
    List.getElem?_eq_getElem hi
  refine ⟨⟨d, ?_⟩, hd⟩
  cases a with
  | left => exact cut_path_selected_prefix R .left R.B.rightPath t i j hij d e.1 hd he e.2
  | right => exact cut_path_selected_prefix R .right R.B.leftPath t i j hij d e.1 hd he e.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The retained seam indices form an initial segment strictly shorter than the seam
when the outer-boundary target is strictly before the sink. Its length is not
asserted to equal the outer-boundary level `s`. -/
theorem seam_selectedDart_initial_segment {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) (t : MapVertex R.B.map)
    (hs : s + 1 ≤ (match a with | .left => ℓ | .right => r))
    (ht : boundaryTarget R.B a s = some t) :
    ∃ c < (boundaryDarts R.B (oppositeSide a)).length, ∀ i : ℕ,
      (∃ d : selectedDarts (presentation R a t),
        (boundaryDarts R.B (oppositeSide a))[i]? = some d.1) ↔ i < c := by
  let E := fun i : ℕ => ∃ d : selectedDarts (presentation R a t),
    (boundaryDarts R.B (oppositeSide a))[i]? = some d.1
  let N := (boundaryDarts R.B (oppositeSide a)).length
  have hmissing : ∃ i, ¬ E i := by
    refine ⟨N, ?_⟩
    rintro ⟨d, hd⟩
    have hnone : (boundaryDarts R.B (oppositeSide a))[N]? = none :=
      List.getElem?_eq_none (le_refl _)
    rw [hnone] at hd
    contradiction
  let c := Nat.find hmissing
  have hc : ¬ E c := Nat.find_spec hmissing
  have hiff (i : ℕ) : E i ↔ i < c := by
    constructor
    · intro hi
      by_contra h
      exact hc (seam_selectedDart_prefix R a t c i (by omega) hi)
    · intro hi
      by_contra h
      exact Nat.find_min hmissing hi h
  have hN : 0 < N := by
    cases a with
    | left =>
      simpa only [N, boundaryDarts, oppositeSide, R.B.rightPath.darts_length]
        using (Nat.lt_of_lt_of_le Nat.zero_lt_one R.B.right_length_pos)
    | right =>
      simpa only [N, boundaryDarts, oppositeSide, R.B.leftPath.darts_length]
        using (Nat.lt_of_lt_of_le Nat.zero_lt_one R.B.left_length_pos)
  have hlast : ¬ E (N - 1) := by
    rintro ⟨d, hd⟩
    have hhead : dartHeadVertex R.B.map d.1 = R.B.sink := by
      cases a with
      | left =>
        obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hd
        change R.B.rightPath.darts.get ⟨N - 1, hi⟩ = d.1 at he
        have hh := (R.B.rightPath.edge_step ⟨N - 1, hi⟩).2.2.2.trans
          (congrArg (dartHeadVertex R.B.map) he)
        have hidx : N - 1 + 1 = r := by
          dsimp only [N, boundaryDarts, oppositeSide] at hN ⊢
          rw [R.B.rightPath.darts_length] at hN ⊢
          omega
        have hend : R.B.rightPath.vertices.get
            ⟨N - 1 + 1, by rw [R.B.rightPath.vertices_length]; omega⟩ = R.B.sink := by
          simpa only [hidx] using R.B.rightPath.end_vertex
        exact hh.symm.trans hend
      | right =>
        obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hd
        change R.B.leftPath.darts.get ⟨N - 1, hi⟩ = d.1 at he
        have hh := (R.B.leftPath.edge_step ⟨N - 1, hi⟩).2.2.2.trans
          (congrArg (dartHeadVertex R.B.map) he)
        have hidx : N - 1 + 1 = ℓ := by
          dsimp only [N, boundaryDarts, oppositeSide] at hN ⊢
          rw [R.B.leftPath.darts_length] at hN ⊢
          omega
        have hend : R.B.leftPath.vertices.get
            ⟨N - 1 + 1, by rw [R.B.leftPath.vertices_length]; omega⟩ = R.B.sink := by
          simpa only [hidx] using R.B.leftPath.end_vertex
        exact hh.symm.trans hend
    exact boundaryTarget_ancestor_ne_sink R a s t _ hs ht d.2.2 hhead
  have hcN : c < N := by
    have hle : c ≤ N - 1 := Nat.find_min' hmissing hlast
    omega
  exact ⟨c, hcN, hiff⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The retained left-half seam marks are an initial segment of the selected geodesic,
preserving their actual geodesic indices and original darts. -/
theorem cutLRep_selected_seam_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) (s : ℕ)
    (v : MapVertex (cutLRep R hR).2.B.map) (hs : s + 1 ≤ ℓ)
    (hv : boundaryTarget (cutLRep R hR).2.B .left s = some v) :
    ∃ c < m, ∀ (i : ℕ) (e : Fin R.dartCount),
      (∃ d : selectedDarts (presentation (cutLRep R hR).2 .left v),
        (boundaryDarts (cutLRep R hR).2.B .right)[i]? = some d.1 ∧
          cutLRepDartMap R hR d.1 = e) ↔
      i < c ∧ (selectedGeodesicOfLen R.B x hR).darts[i]? = some e := by
  obtain ⟨c, hc, hindices⟩ :=
    seam_selectedDart_initial_segment (cutLRep R hR).2 .left s v hs hv
  have hcm : c < m := by
    simpa only [oppositeSide, boundaryDarts,
      (cutLRep R hR).2.B.rightPath.darts_length] using hc
  refine ⟨c, hcm, ?_⟩
  intro i e
  have hm := congrArg (fun ds => ds[i]?) (cutLRep_boundaryDarts_map R hR).2
  rw [List.getElem?_map] at hm
  constructor
  · rintro ⟨d, hd, he⟩
    refine ⟨(hindices i).mp ⟨d, hd⟩, ?_⟩
    rw [← hm, hd, Option.map_some, he]
  · rintro ⟨hi, he⟩
    rw [← hm] at he
    obtain ⟨d, hd, hde⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨z, hz⟩ := (hindices i).mpr hi
    have hzd : z.1 = d := Option.some.inj (hz.symm.trans hd)
    exact ⟨z, hz, (congrArg (cutLRepDartMap R hR) hzd).trans hde⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The retained right-half seam marks are an initial segment of the selected geodesic,
preserving their actual geodesic indices and original darts. -/
theorem cutRRep_selected_seam_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) (s : ℕ)
    (v : MapVertex (cutRRep R hR).2.B.map) (hs : s + 1 ≤ r)
    (hv : boundaryTarget (cutRRep R hR).2.B .right s = some v) :
    ∃ c < m, ∀ (i : ℕ) (e : Fin R.dartCount),
      (∃ d : selectedDarts (presentation (cutRRep R hR).2 .right v),
        (boundaryDarts (cutRRep R hR).2.B .left)[i]? = some d.1 ∧
          cutRRepDartMap R hR d.1 = e) ↔
      i < c ∧ (selectedGeodesicOfLen R.B x hR).darts[i]? = some e := by
  obtain ⟨c, hc, hindices⟩ :=
    seam_selectedDart_initial_segment (cutRRep R hR).2 .right s v hs hv
  have hcm : c < m := by
    simpa only [oppositeSide, boundaryDarts,
      (cutRRep R hR).2.B.leftPath.darts_length] using hc
  refine ⟨c, hcm, ?_⟩
  intro i e
  have hm := congrArg (fun ds => ds[i]?) (cutRRep_boundaryDarts_map R hR).2
  rw [List.getElem?_map] at hm
  constructor
  · rintro ⟨d, hd, he⟩
    refine ⟨(hindices i).mp ⟨d, hd⟩, ?_⟩
    rw [← hm, hd, Option.map_some, he]
  · rintro ⟨hi, he⟩
    rw [← hm] at he
    obtain ⟨d, hd, hde⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨z, hz⟩ := (hindices i).mpr hi
    have hzd : z.1 = d := Option.some.inj (hz.symm.trans hd)
    exact ⟨z, hz, (congrArg (cutRRepDartMap R hR) hzd).trans hde⟩

private theorem cut_face_tail_head {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.toCombinatorialMap.faceSucc d) = dartHeadVertex M d := by
  apply Quotient.sound
  change Equiv.Perm.SameCycle M.toCombinatorialMap.rot
    (M.toCombinatorialMap.rot.symm (M.toCombinatorialMap.edgeInv d))
    (M.toCombinatorialMap.edgeInv d)
  exact ⟨1, by simp⟩

private theorem cut_retainedFace_selected (R : HalfTruncationRep)
    (d e : Fin R.rep.dartCount) (hd : retainedFace R d)
    (he : Equiv.Perm.SameCycle R.rep.B.map.toCombinatorialMap.faceSucc d e) :
    e ∈ selectedDarts R := by
  refine ⟨hd.2 e he, ?_⟩
  rw [← cut_face_tail_head]
  exact hd.2 _ he.apply_right

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A left-half inner face is retained exactly when its entire original face orbit
lies in the selected half-dart image. Both directions are proved within this cut. -/
theorem cutLRep_retainedFace_iff_selected_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutLRep R hR).2.B.map)
    (d : Fin (cutLRep R hR).2.dartCount) :
    retainedFace (presentation (cutLRep R hR).2 .left t) d ↔
      ¬ (cutLRep R hR).2.B.map.IsOuter d ∧
        ∀ e : Fin R.dartCount,
          Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
            (cutLRepDartMap R hR d) e →
          ∃ c : selectedDarts (presentation (cutLRep R hR).2 .left t),
            cutLRepDartMap R hR c.1 = e := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hboundary (ho : ¬ (cutLRep R hR).2.B.map.IsOuter d) :
      (I.toEquiv d).1 ∉ pathCutLeftHalfBoundaryDarts R.B P := by
    intro h
    exact ho ((I.outer_iff d).mp
      ((pathCutLeftHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  constructor
  · intro hd
    have hb := hboundary hd.1
    have hf := pathCutLeftHalf_inner_face_contained R.B P (I.toEquiv d).2 hb
    refine ⟨hd.1, ?_⟩
    intro e he
    let f : {z // z ∈ pathCutLeftHalfDarts R.B P} := ⟨e, (hf.2 e he).1⟩
    let c := I.toEquiv.symm f
    have hc : Equiv.Perm.SameCycle
        (cutLRep R hR).2.B.map.toCombinatorialMap.faceSucc d c := by
      have hh := cut_baseIso_faceCycle_map I.symm
        ((pathCutLeftHalf_inner_faceOrbit_iff R.B P (I.toEquiv d) hb f).mpr he)
      change Equiv.Perm.SameCycle (cutLRep R hR).2.B.map.toCombinatorialMap.faceSucc
        (I.toEquiv.symm (I.toEquiv d)) c at hh
      exact (I.toEquiv.symm_apply_apply d) ▸ hh
    have hsel : c ∈ selectedDarts (presentation (cutLRep R hR).2 .left t) :=
      cut_retainedFace_selected (presentation (cutLRep R hR).2 .left t) d c hd hc
    refine ⟨⟨c, hsel⟩, ?_⟩
    change (I.toEquiv (I.toEquiv.symm f)).1 = e
    rw [Equiv.apply_symm_apply]
  · rintro ⟨ho, hf⟩
    have hb := hboundary ho
    refine ⟨ho, ?_⟩
    intro e he
    have hc := (pathCutLeftHalf_inner_faceOrbit_iff R.B P
      (I.toEquiv d) hb (I.toEquiv e)).mp (cut_baseIso_faceCycle_map I he)
    obtain ⟨c, hce⟩ := hf (cutLRepDartMap R hR e) hc
    have heq : c.1 = e := (cutLRep_embedding_fields R hR).1 hce
    exact heq ▸ c.2.1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A right-half inner face is retained exactly when its entire original face orbit
lies in the selected half-dart image. Both directions are proved within this cut. -/
theorem cutRRep_retainedFace_iff_selected_image {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (t : MapVertex (cutRRep R hR).2.B.map)
    (d : Fin (cutRRep R hR).2.dartCount) :
    retainedFace (presentation (cutRRep R hR).2 .right t) d ↔
      ¬ (cutRRep R hR).2.B.map.IsOuter d ∧
        ∀ e : Fin R.dartCount,
          Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
            (cutRRepDartMap R hR d) e →
          ∃ c : selectedDarts (presentation (cutRRep R hR).2 .right t),
            cutRRepDartMap R hR c.1 = e := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hboundary (ho : ¬ (cutRRep R hR).2.B.map.IsOuter d) :
      (I.toEquiv d).1 ∉ pathCutRightHalfBoundaryDarts R.B P := by
    intro h
    exact ho ((I.outer_iff d).mp
      ((pathCutRightHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  constructor
  · intro hd
    have hb := hboundary hd.1
    have hf := pathCutRightHalf_inner_face_contained R.B P (I.toEquiv d).2 hb
    refine ⟨hd.1, ?_⟩
    intro e he
    let f : {z // z ∈ pathCutRightHalfDarts R.B P} := ⟨e, (hf.2 e he).1⟩
    let c := I.toEquiv.symm f
    have hc : Equiv.Perm.SameCycle
        (cutRRep R hR).2.B.map.toCombinatorialMap.faceSucc d c := by
      have hh := cut_baseIso_faceCycle_map I.symm
        ((pathCutRightHalf_inner_faceOrbit_iff R.B P (I.toEquiv d) hb f).mpr he)
      change Equiv.Perm.SameCycle (cutRRep R hR).2.B.map.toCombinatorialMap.faceSucc
        (I.toEquiv.symm (I.toEquiv d)) c at hh
      exact (I.toEquiv.symm_apply_apply d) ▸ hh
    have hsel : c ∈ selectedDarts (presentation (cutRRep R hR).2 .right t) :=
      cut_retainedFace_selected (presentation (cutRRep R hR).2 .right t) d c hd hc
    refine ⟨⟨c, hsel⟩, ?_⟩
    change (I.toEquiv (I.toEquiv.symm f)).1 = e
    rw [Equiv.apply_symm_apply]
  · rintro ⟨ho, hf⟩
    have hb := hboundary ho
    refine ⟨ho, ?_⟩
    intro e he
    have hc := (pathCutRightHalf_inner_faceOrbit_iff R.B P
      (I.toEquiv d) hb (I.toEquiv e)).mp (cut_baseIso_faceCycle_map I he)
    obtain ⟨c, hce⟩ := hf (cutRRepDartMap R hR e) hc
    have heq : c.1 = e := (cutRRep_embedding_fields R hR).1 hce
    exact heq ▸ c.2.1





































































































































































































































































































end DirectedDistances.PaperProofs.Section4
