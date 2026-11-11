module

public import DirectedDistances.KMSW.Beta0BoundarySuccessor
public import DirectedDistances.KMSW.HatLimitRotation
public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.PrimedLimitRotation
public import DirectedDistances.KMSW.PrimedMissingEdgeImages
public import DirectedDistances.PaperProofs.Section5.FlowLineTimes

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

This file isolates the remaining ordered hatted boundary bridge and records
the proved primed edge-ID correspondence. The primed edge ID is not a code-time
index; C13 supplies the primed replacement,
positive-time counting convention (code index m vs S'_{m+1}, applied in the counted Lemma 5.14) is not used by
the statements in this file.
C18 retains the marked missing root. -/

public section
namespace DirectedDistances.KMSW

/- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

assumed by any declaration here. Ordered endpoint identities follow from
`hatLimitEdgeMap_endpoint_alignment`. -/
@[expose] def HattedLeftBoundaryBeta0EdgeCorrespondence (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) : Prop :=
  ∀ i, hatLimitEdgeMap w h (kmswLeftBoundaryEdge (hatCodes w h) i) =
    (kmswBeta0Stream w hfin hb i).1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The hatted limit maps preserve the ordered endpoints of every compressed edge.
This is the endpoint part needed after the ordered boundary edge identity. -/
theorem hatLimitEdgeMap_endpoint_alignment (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) :
    edgeWest w (hatLimitEdgeMap w h e) =
        hatLimitVertexMap w h (edgeWest (hatCodes w h) e) ∧
      edgeEast w (hatLimitEdgeMap w h e) =
        hatLimitVertexMap w h (edgeEast (hatCodes w h) e) := by
  exact hatExplicitEdgeEquiv_incidence w h
    ⟨e, hatCodes_edge_present w h e⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The β₀ stream starts at the image of `lambda_0^-`, the ambient root vertex. -/
theorem beta0_stream_starts_at_root (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) :
    edgeWest w (kmswBeta0Stream w hfin hb 0).1 = 0 :=
  kmswBeta0Stream_start w hfin hb

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The hatted vertex limit fixes the source root `lambda_0^-`. -/
theorem hatLimitVertexMap_root (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    hatLimitVertexMap w h 0 = 0 := by
  have hv : 0 < (kmswStage (hatCodes w h) 0).nextVertex := by
    change 0 < 2
    omega
  rw [hatLimitVertexMap_eq_stage w h 0 0 hv]
  exact hatAllVertexMap_root w h 0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The hatted root vertex agrees with the starting vertex of β₀. -/
theorem hatRoot_matches_beta0_start (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) :
    hatLimitVertexMap w h 0 = edgeWest w (kmswBeta0Stream w hfin hb 0).1 := by
  rw [hatLimitVertexMap_root, beta0_stream_starts_at_root]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The primed root keeps its geometric edge ID and is tagged missing (C18). -/
theorem primedRootRetainedMissing (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedLimitDartMap w h (0, false) =
        (kmswLLCreatedEdge w (walkNL w h 0), false) ∧
      primedLimitSideFlip w h 0 = false ∧
      primeMissingEdge w hfin hb (primedLimitEdgeMap w h 0) := by
  exact ⟨primedLimitDartMap_root w h, primedLimitSideFlip_zero w h,
    primedLimitRoot_primeMissingEdge w h hfin hb⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The primed root vertex is matched to the west endpoint of the retained C18 root edge. -/
theorem primedRootVertex_matches_rootEdge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    primedLimitVertexMap w h 0 = edgeWest w (primedLimitEdgeMap w h 0) := by
  have hf := primedLimitSideFlip_zero w h
  change decide (primedLimitVertexMap w h
      (edgeWest (primedCode (primedSimInput w) h) 0) ≠
        edgeWest w (primedLimitEdgeMap w h 0)) = false at hf
  have hnot := of_decide_eq_false hf
  have heq : primedLimitVertexMap w h
      (edgeWest (primedCode (primedSimInput w) h) 0) =
        edgeWest w (primedLimitEdgeMap w h 0) := by
    simpa only [ne_eq, not_not] using hnot
  change primedLimitVertexMap w h 0 = _ at heq
  exact heq

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

Each β₀ edge has a primed geometric edge-ID preimage by the proved missing-edge
image theorem. -/
theorem primedBeta0Image_exists (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) (i : ℕ) :
    ∃ a, primedLimitEdgeMap w h a = (kmswBeta0Stream w hrawfin hb i).1 := by
  exact primedBeta0MissingEdgeImage w hfin hb h _
    (beta0_westBoundary_stream w hrawfin hb i)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

This is the least primed edge ID mapping to the `i`th β₀ edge. It is an edge-ID
correspondence, not an identification of boundary index with code-time index. -/
@[expose] noncomputable def primedBeta0EdgeIndex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) (i : ℕ) : ℕ :=
  Nat.find (primedBeta0Image_exists w h hfin hb hrawfin i)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The exact edge-ID correspondence is unique because the primed limit edge map
is injective. -/
theorem primedBeta0EdgeIndex_maps_to_stream (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) (i : ℕ) :
    primedLimitEdgeMap w h (primedBeta0EdgeIndex w h hfin hb hrawfin i) =
      (kmswBeta0Stream w hrawfin hb i).1 :=
    by simpa only [primedBeta0EdgeIndex] using
      Nat.find_spec (primedBeta0Image_exists w h hfin hb hrawfin i)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The primed edge ID selected for each β₀ edge is the unique preimage. -/
theorem primedBeta0EdgeIndex_unique (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) (i a : ℕ)
    (ha : primedLimitEdgeMap w h a = (kmswBeta0Stream w hrawfin hb i).1) :
    a = primedBeta0EdgeIndex w h hfin hb hrawfin i := by
  apply primedLimitEdgeMap_injective w h
  exact ha.trans (primedBeta0EdgeIndex_maps_to_stream w h hfin hb hrawfin i).symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The selected primed preimage is tagged missing, with the C18 root convention
retained by the primed geometric map. -/
theorem primedBeta0EdgeIndex_missing (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) (i : ℕ) :
    ¬ PrimedEdgePresent w h
      (primedBeta0EdgeIndex w h hfin hb hrawfin i) := by
  let a := primedBeta0EdgeIndex w h hfin hb hrawfin i
  have hbeta : primeBetaEdge w hfin hb
      (primedLimitEdgeMap w h a) := by
    rw [primedBeta0EdgeIndex_maps_to_stream w h hfin hb hrawfin i]
    exact (primeBetaEdge_iff_MhatWestBoundaryEdge w hfin hb _).mpr
      (beta0_westBoundary_stream w hrawfin hb i)
  exact primedLimitEdgeMap_beta_missing w h hfin hb a hbeta

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The endpoints of the selected primed edge agree with the compressed endpoints
up to the proved geometric endpoint order, including missing edges. -/
theorem primedBeta0EdgeIndex_endpoint_order (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) (i : ℕ) :
    let e := primedBeta0EdgeIndex w h hfin hb hrawfin i
    let u := primedCode (primedSimInput w) h
    (edgeWest w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeWest u e) ∧
      edgeEast w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeEast u e)) ∨
    (edgeWest w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeEast u e) ∧
      edgeEast w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeWest u e)) := by
  exact primedLimitEdgeMap_endpoint_orders w h _

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The ordered endpoints of each primed edge follow its explicit
`primedLimitSideFlip`, also when the edge is missing. -/
theorem primedLimitEdgeMap_endpoint_sideflip (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) :
    let u := primedCode (primedSimInput w) h
    let a := primedLimitVertexMap w h (edgeWest u e)
    let b := primedLimitVertexMap w h (edgeEast u e)
    let x := edgeWest w (primedLimitEdgeMap w h e)
    let y := edgeEast w (primedLimitEdgeMap w h e)
    (primedLimitSideFlip w h e = false ∧ x = a ∧ y = b) ∨
      (primedLimitSideFlip w h e = true ∧ x = b ∧ y = a) := by
  dsimp only
  let u := primedCode (primedSimInput w) h
  let a := primedLimitVertexMap w h (edgeWest u e)
  let b := primedLimitVertexMap w h (edgeEast u e)
  let x := edgeWest w (primedLimitEdgeMap w h e)
  let y := edgeEast w (primedLimitEdgeMap w h e)
  have hord := primedLimitEdgeMap_endpoint_orders w h e
  change (x = a ∧ y = b) ∨ (x = b ∧ y = a) at hord
  change (primedLimitSideFlip w h e = false ∧ x = a ∧ y = b) ∨
    (primedLimitSideFlip w h e = true ∧ x = b ∧ y = a)
  rcases hord with hsame | hrev
  · left
    have hf : primedLimitSideFlip w h e = false := by
      change decide (a ≠ x) = false
      rw [hsame.1]
      simp
    exact ⟨hf, hsame⟩
  · by_cases hab : a = b
    · left
      have hf : primedLimitSideFlip w h e = false := by
        change decide (a ≠ x) = false
        rw [hrev.1]
        simp [hab]
      refine ⟨hf, ?_, ?_⟩
      · exact hrev.1.trans hab.symm
      · exact hrev.2.trans hab
    · right
      have hf : primedLimitSideFlip w h e = true := by
        change decide (a ≠ x) = true
        rw [hrev.1]
        simp [hab]
      exact ⟨hf, hrev⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

The selected edge-ID preimage has the same endpoint correspondence, using the
primed geometric side flip. -/
theorem primedBeta0EdgeIndex_endpoint_sideflip (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) (i : ℕ) :
    let e := primedBeta0EdgeIndex w h hfin hb hrawfin i
    let u := primedCode (primedSimInput w) h
    (primedLimitSideFlip w h e = false ∧
      edgeWest w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeWest u e) ∧
      edgeEast w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeEast u e)) ∨
    (primedLimitSideFlip w h e = true ∧
      edgeWest w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeEast u e) ∧
      edgeEast w (primedLimitEdgeMap w h e) =
        primedLimitVertexMap w h (edgeWest u e)) := by
  exact primedLimitEdgeMap_endpoint_sideflip w h _

/- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

assumed by any declaration here. Its target edge ID is already uniquely
specified by `primedBeta0EdgeIndex`.
positive-time counting convention (code index m vs S'_{m+1}, applied in the counted Lemma 5.14) is not used by
the statements in this file.
FALSE as stated: refuted by primedRightBoundaryBeta0IndexCorrespondence_false
in KMSW/GluingBoundaryOrder.lean, which proves the corrected ordering on the
stage boundary list UR. -/
@[expose] def PrimedRightBoundaryBeta0IndexCorrespondence (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨
          (kmswStage w n).east e = v)}.Finite) : Prop :=
  ∀ i, ∃ j,
    kmswRightBoundaryEdge (primedCode (primedSimInput w) h) j =
      primedBeta0EdgeIndex w h hfin hb hrawfin i

end DirectedDistances.KMSW
