module

public import DirectedDistances.Recursive.BusemannLeftSeamDecoderSdp
public import DirectedDistances.Recursive.SdpLeftDecodersExist
public import DirectedDistances.KMSW.GluingBoundaryOrder

/-! Supporting lemmas for paper labels `lem-geo-infty`, `lem-geo-infty-ind` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "D" =>
  selectedCutCoherentDomain XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "P" q => sourceAncestorPath
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "LB" => fun (q : D) (i : ℕ) =>
  thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.left i
local notation "SE" => fun (q : D) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left
local notation "AE" => fun (q : D) (s : ℕ) =>
  sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left s
local notation "AV" => fun (q : D) (s : ℕ) =>
  sourceAncestorVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left s
local notation "TC" => thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
private theorem sdpSeamVertex_inj (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatLimitVertexMap w h) := by
  intro a b he
  exact vertex_inj (hatLimitExplicitInput w h)
    (kmswVertexAllocated_all _ ⟨a⟩) (kmswVertexAllocated_all _ ⟨b⟩) he

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
private theorem sdpSeamLift_aux (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (a : PresentVertex (W q))
    {y : PresentVertex w}
    (p : Path ((alongSdpHatFunctor w h q hw).obj a) y)
    (hp : ∀ e ∈ pathEdgeList p, e ∈ hatLimitEdgeMap w h '' SE q) :
    ∃ b : PresentVertex (W q), ∃ r : Path a b,
      (alongSdpHatFunctor w h q hw).obj b = y ∧ r.length = p.length ∧
      ∀ e ∈ pathEdgeList r, e ∈ SE q := by
  induction p with
  | nil => exact ⟨a, .nil, rfl, rfl, fun _ he => False.elim (List.not_mem_nil he)⟩
  | @cons x y p e ih =>
    obtain ⟨b, r, hb, hr, hre⟩ := ih (fun f hf =>
      hp f (List.mem_append.mpr (Or.inl hf)))
    obtain ⟨j, hj, hje⟩ := hp e.val
      (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
    have hi := hatLimitEdgeMap_endpoint_alignment w h j
    rw [← hw] at hi
    have hs : edgeWest (W q) j = b.id := by
      apply sdpSeamVertex_inj w h
      rw [← hi.1, hje, e.property.2.1]
      exact congrArg PresentVertex.id hb.symm
    have hjp : EdgePresent (W q) j := by
      rw [hw]
      exact hatCodes_edge_present w h j
    let c : PresentVertex (W q) := ⟨edgeEast (W q) j⟩
    let f : b ⟶ c := ⟨j, hjp, hs, rfl⟩
    refine ⟨c, r.cons f, ?_, ?_, ?_⟩
    · exact congrArg PresentVertex.mk
        (hi.2.symm.trans ((congrArg (edgeEast w) hje).trans e.property.2.2))
    · simp only [Path.length_cons, hr]
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hre d hd
      · exact List.mem_singleton.mp hd ▸ hj



private theorem sdpSeamPath_ancestors (q : D) (s : ℕ)
    {a b : PresentVertex (W q)} (p : Path a b)
    (hp : ∀ e ∈ pathEdgeList p, e ∈ SE q) (hb : b.id ∈ AV q s) :
    ∀ e ∈ pathEdgeList p, e ∈ AE q s := by
  induction p with
  | nil => exact fun _ he => False.elim (List.not_mem_nil he)
  | @cons y z p e ih =>
    have he := hp e.val
      (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
    have hend := sideEdges_endpoints
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left he
    have hy : y.id ∈ AV q s := ⟨e.property.2.1 ▸ hend.1,
      hb.2.head ⟨e.val, he, e.property⟩⟩
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih (fun d hd => hp d (List.mem_append.mpr (Or.inl hd))) hy f hf
    · exact List.mem_singleton.mp hf ▸
        ⟨he, e.property.2.1.symm ▸ hy, e.property.2.2.symm ▸ hb⟩



private theorem sdpSeamLevel (q : D) (t : ℕ) : ∃ s, (P q).edge t ∈ AE q s := by
  have hc : {v : ℕ | mapCutVertex (W q) (HF q) v}.Infinite := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := selectedCutCoherentDomain_spec
      XDP.sdp renewalTime renewalTime_positiveSuccessTime q
    exact hc
  exact seamEdge_mem_sourceAncestorEdges_some
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) hc .left t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
theorem leftSeamSdpRawPathLift_proved : LeftSeamSdpRawPathLift := by
  intro w h q hw i t n p hn hp
  obtain ⟨b, r, hb, hr, hre⟩ := sdpSeamLift_aux w h q hw ⟨LB q i⟩ p hp
  have hb' : b = (⟨((P q).initial t).1.id⟩ : PresentVertex (W q)) :=
    congrArg PresentVertex.mk (sdpSeamVertex_inj w h (congrArg PresentVertex.id hb))
  subst b
  obtain ⟨s, hs⟩ := sdpSeamLevel q t
  let S := max i s
  have hs' : (P q).edge t ∈ AE q S := sourceAncestorEdges_mono
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left (Nat.le_max_right _ _) hs
  refine ⟨S, Nat.le_max_left _ _, hs', r, hr.trans hn, ?_⟩
  apply sdpSeamPath_ancestors q S r hre
  exact ((P q).edge_outgoing_at_initial (W q) t).2 ▸ hs'.2.1


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
All sufficiently large SDP truncations contain exactly the raw lengths. -/
private theorem leftSeamSdpLengths_eventually (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) :
    ∀ᶠ s in atTop, leftSeamSdpLengths q i t s = leftSeamSdpRawPathLengths w h q i t := by
  obtain ⟨S, hS⟩ := sdpSeamLevel q t
  refine eventually_atTop.mpr ⟨max i S, fun s hs => ?_⟩
  have hi : i ≤ s := (Nat.le_max_left _ _).trans hs
  have ht : (P q).edge t ∈ AE q s := sourceAncestorEdges_mono
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left
    ((Nat.le_max_right _ _).trans hs) hS
  ext n
  constructor
  · rintro ⟨_, _, r, hr, hre⟩
    refine ⟨(alongSdpHatFunctor w h q hw).mapPath r,
      (alongSdpMap_length w h q hw r).trans hr, ?_⟩
    intro e he
    erw [alongSdpMap_edges] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact ⟨f, (hre f hf).1, rfl⟩
  · rintro ⟨p, hp, hpe⟩
    obtain ⟨b, r, hb, hr, hre⟩ := sdpSeamLift_aux w h q hw ⟨LB q i⟩ p hpe
    have hb' : b = (⟨((P q).initial t).1.id⟩ : PresentVertex (W q)) :=
      congrArg PresentVertex.mk (sdpSeamVertex_inj w h (congrArg PresentVertex.id hb))
    subst b
    refine ⟨hi, ht, r, hr.trans hp, sdpSeamPath_ancestors q s r hre ?_⟩
    exact ((P q).edge_outgoing_at_initial (W q) t).2 ▸ ht.2.1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The decoder preserves unreachable top and attained minima. -/
private theorem leftSeamSdpDecoder_raw (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) :
    leftSeamSdpDecoder (TC .left q.1) i t =
      leftSeamSdpTruncationValue (leftSeamSdpRawPathLengths w h q i t) := by
  apply eventualWithTopValue_eq
  filter_upwards [leftSeamSdpLengths_eventually w h q hw i t] with s hs
  rw [leftSeamSdpTruncationDecoder_eq, hs]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Boundary vertex k is the tail of edge k, including the root at k = 0. -/
private theorem hattedLeftBoundarySdp_beta0 (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (q : D) (hw : (W q) = hatCodes w h) (k : ℕ) :
    hatLimitVertexMap w h (LB q k) = kmswBeta0Vertices w hfin hb k := by
  unfold hatLimitFiniteIncidence at hfin
  change hatLimitVertexMap w h
    (thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) .left k) = _
  rw [ancestor_boundaryVertex_eq (W q) (HF q) (HL q) (HT q) (HR q) .left k, hw]
  rw [← (hatLimitEdgeMap_endpoint_alignment w h _).1,
    hattedLeftBoundaryBeta0EdgeCorrespondence_proved w h hfin hb k]
  cases k with
  | zero => exact kmswBeta0Stream_start w hfin hb
  | succ k => exact kmswBeta0Stream_chain w hfin hb k

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Edges of a root-reachable path are geometric hatted edges. -/
private theorem sdpSeamPath_geometric {w : ℕ → Fin 3} {a b : PresentVertex w}
    (ha : a ∈ leftHatVertices w) (p : Path a b) :
    ∀ e ∈ pathEdgeList p, MhatGeometricEdge w e := by
  induction p with
  | nil => exact fun _ he => False.elim (List.not_mem_nil he)
  | @cons y z p e ih =>
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih f hf
    · obtain rfl := List.mem_singleton.mp hf
      have hy := leftHatVertices_closed ha p
      have hz := leftHatVertices_closed hy e.toPath
      exact ⟨e.property.2.1.symm ▸ hy, e.property.2.2.symm ▸ hz⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Confinement removes precisely the non-hatted complement from the glued closed side. -/
private theorem leftSeamSdpRawPathLengths_eq_closed (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) :
    leftSeamSdpRawPathLengths w h q i t = leftHatClosedLengths w (closedLeftSdpEdges w h q)
      ⟨hatLimitVertexMap w h (LB q i)⟩
      ((leftAlongRawSdpGeodesic w h q hw).initial t).1 := by
  rw [leftAlongRawSdpGeodesic_vertex]
  have hx : (⟨hatLimitVertexMap w h (LB q i)⟩ : PresentVertex w) ∈
      leftHatVertices w := alloc_reachable (hatLimitExplicitInput w h)
        (kmswVertexAllocated_all _ ⟨LB q i⟩)
  ext n
  constructor
  · rintro ⟨p, hp, hpe⟩
    exact ⟨p, hp, leftHatVertices_path_closed hx p, fun e he => Or.inr (hpe e he)⟩
  · rintro ⟨p, hp, _, hpe⟩
    refine ⟨p, hp, fun e he => ?_⟩
    rcases hpe e he with he' | he'
    · exact False.elim (he' (sdpSeamPath_geometric hx p e he))
    · exact he'

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The truncation infimum equals the minimum, including top for empty sets. -/
private theorem sdpSeamValue_min (S : Set ℕ) :
    leftSeamSdpTruncationValue S = leftLengthMin S := by
  classical
  by_cases hn : S.Nonempty
  · rw [leftLengthMin, dite_eq_left hn]
    apply le_antisymm
    · exact sInf_le ⟨sInf S, Nat.sInf_mem hn, rfl⟩
    · apply le_sInf
      rintro x ⟨n, hmem, rfl⟩
      exact WithTop.coe_le_coe.mpr (Nat.sInf_le hmem)
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    subst S
    simp only [leftSeamSdpTruncationValue, Set.image_empty, sInf_empty,
      leftLengthMin, Set.not_nonempty_empty, dite_false]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw SDP identification holds simultaneously, with top for unreachable pairs. -/
theorem leftSeamSdpRawIdentification_proved : LeftSeamSdpRawIdentification := by
  filter_upwards [rightHatThinBoundarySdpIdentification_proved] with ω hc
  obtain ⟨h, q, hq, hw, _⟩ := hc
  refine ⟨h, q, hq, hw, fun i t => ?_⟩
  rw [← hq, leftSeamSdpDecoder_raw _ h q hw i t, sdpSeamValue_min]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted SDP decoder exists with the beta-to-outer-boundary correspondence.
The coherent code has an eventual value, so the unrealized-code default is unused. -/
theorem hattedLeftSeamSdpDecoderExists_proved : HattedLeftSeamSdpDecoderExists := by
  refine ⟨leftSeamSdpDecoder, measurable_leftSeamSdpDecoder_joint, ?_⟩
  filter_upwards [] with ω
  dsimp only
  intro h hfin hb q hw hq k t
  rw [← hq, leftSeamSdpDecoder_raw _ h q hw k t, sdpSeamValue_min,
    leftSeamSdpRawPathLengths_eq_closed _ h q hw k t,
    hattedLeftBoundarySdp_beta0 _ h hfin hb q hw k]

end DirectedDistances.Recursive
