module

public import DirectedDistances.Recursive.BusemannLeftSeamDecoder
public import DirectedDistances.Recursive.LeftLocalityAssembly
public import DirectedDistances.KMSW.GluingBoundaryOrder

/-! Supporting lemmas for paper labels `lem-geo-infty`, `lem-geo-infty-ind` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "D" =>
  selectedCutCoherentDomain XDP.ldp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "P" q => sourceAncestorPath
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "LB" => fun (q : D) (i : ℕ) =>
  thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.left i
local notation "SE" => fun (q : D) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left
local notation "AE" => fun (q : D) (s : ℕ) =>
  sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left s
local notation "AV" => fun (q : D) (s : ℕ) =>
  sourceAncestorVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left s
local notation "TC" => thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
private theorem seamVertex_inj (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatLimitVertexMap w h) := by
  intro a b he
  exact vertex_inj (hatLimitExplicitInput w h)
    (kmswVertexAllocated_all _ ⟨a⟩) (kmswVertexAllocated_all _ ⟨b⟩) he

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
private theorem seamLift_aux (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (a : PresentVertex (W q))
    {y : PresentVertex w}
    (p : Path ((alongHatFunctor w h q hw).obj a) y)
    (hp : ∀ e ∈ pathEdgeList p, e ∈ hatLimitEdgeMap w h '' SE q) :
    ∃ b : PresentVertex (W q), ∃ r : Path a b,
      (alongHatFunctor w h q hw).obj b = y ∧ r.length = p.length ∧
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
      apply seamVertex_inj w h
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



private theorem seamPath_ancestors (q : D) (s : ℕ)
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



private theorem seamLevel (q : D) (t : ℕ) : ∃ s, (P q).edge t ∈ AE q s := by
  have hc : {v : ℕ | mapCutVertex (W q) (HF q) v}.Infinite := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := selectedCutCoherentDomain_spec
      XDP.ldp renewalTime renewalTime_positiveSuccessTime q
    exact hc
  exact seamEdge_mem_sourceAncestorEdges_some
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) hc .left t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/
theorem leftSeamRawPathLift_proved : LeftSeamRawPathLift := by
  intro w h q hw i t n p hn hp
  obtain ⟨b, r, hb, hr, hre⟩ := seamLift_aux w h q hw ⟨LB q i⟩ p hp
  have hb' : b = (⟨((P q).initial t).1.id⟩ : PresentVertex (W q)) :=
    congrArg PresentVertex.mk (seamVertex_inj w h (congrArg PresentVertex.id hb))
  subst b
  obtain ⟨s, hs⟩ := seamLevel q t
  let S := max i s
  have hs' : (P q).edge t ∈ AE q S := sourceAncestorEdges_mono
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.left (Nat.le_max_right _ _) hs
  refine ⟨S, Nat.le_max_left _ _, hs', r, hr.trans hn, ?_⟩
  apply seamPath_ancestors q S r hre
  exact ((P q).edge_outgoing_at_initial (W q) t).2 ▸ hs'.2.1


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
All sufficiently large truncations contain exactly the raw lengths. -/
theorem leftSeamLdpLengths_eventually (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) :
    ∀ᶠ s in atTop, leftSeamLdpLengths q i t s = leftSeamRawPathLengths w h q i t := by
  obtain ⟨S, hS⟩ := seamLevel q t
  refine eventually_atTop.mpr ⟨max i S, fun s hs => ?_⟩
  have hi : i ≤ s := (Nat.le_max_left _ _).trans hs
  have ht : (P q).edge t ∈ AE q s := sourceAncestorEdges_mono
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left
    ((Nat.le_max_right _ _).trans hs) hS
  ext n
  constructor
  · rintro ⟨_, _, r, hr, hre⟩
    refine ⟨(alongHatFunctor w h q hw).mapPath r,
      (alongMap_length w h q hw r).trans hr, ?_⟩
    intro e he
    erw [alongMap_edges] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact ⟨f, (hre f hf).1, rfl⟩
  · rintro ⟨p, hp, hpe⟩
    obtain ⟨b, r, hb, hr, hre⟩ := seamLift_aux w h q hw ⟨LB q i⟩ p hpe
    have hb' : b = (⟨((P q).initial t).1.id⟩ : PresentVertex (W q)) :=
      congrArg PresentVertex.mk (seamVertex_inj w h (congrArg PresentVertex.id hb))
    subst b
    refine ⟨hi, ht, r, hr.trans hp, seamPath_ancestors q s r hre ?_⟩
    exact ((P q).edge_outgoing_at_initial (W q) t).2 ▸ ht.2.1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The decoder preserves the empty-set sentinel as well as attained maxima. -/
theorem leftSeamLdpDecoder_raw (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) :
    leftSeamLdpDecoder (TC .left q.1) i t =
      leftSeamLdpTruncationValue (leftSeamRawPathLengths w h q i t) := by
  apply eventualIntValue_eq
  filter_upwards [leftSeamLdpLengths_eventually w h q hw i t] with s hs
  rw [leftSeamLdpTruncationDecoder_eq, hs]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Boundary vertex k is the tail of edge k, including the root at k = 0. -/
theorem hattedLeftBoundary_beta0 (w : ℕ → Fin 3) (h : HasFlowLineHits w)
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
private theorem seamPath_geometric {w : ℕ → Fin 3} {a b : PresentVertex w}
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
theorem leftSeamRawPathLengths_eq_closed (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) :
    leftSeamRawPathLengths w h q i t = leftHatClosedLengths w (closedLeftEdges w h q)
      ⟨hatLimitVertexMap w h (LB q i)⟩
      ((leftAlongRawGeodesic w h q hw).initial t).1 := by
  rw [leftAlongRawGeodesic_vertex]
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
    · exact False.elim (he' (seamPath_geometric hx p e he))
    · exact he'

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Convert negative integer sentinels to unreachable bottom. -/
@[expose] def leftSeamLengthOfInt (z : ℤ) : WithBot ℕ :=
  if z < 0 then ⊥ else (z.toNat : WithBot ℕ)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integer encoding of a bounded set has the same bottom-valued supremum. -/
private theorem seamValue_sup (S : Set ℕ) (hS : BddAbove S) :
    leftSeamLengthOfInt (leftSeamLdpTruncationValue S) = leftLengthSup S := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨n, hn⟩ := hS.exists_isGreatest_of_nonempty hn
    have hv : leftSeamLdpTruncationValue S = (n : ℤ) := by
      rw [leftSeamLdpTruncationValue, dite_eq_left ⟨n, hn.1⟩, hn.csSup_eq]
    rw [hv]
    have hs : leftLengthSup S = (n : WithBot ℕ) := by
      apply IsGreatest.csSup_eq
      exact ⟨⟨n, hn.1, rfl⟩, fun _ ⟨m, hm, he⟩ => he ▸ WithBot.coe_le_coe.mpr (hn.2 hm)⟩
    rw [hs]
    simp only [leftSeamLengthOfInt, show ¬ (n : ℤ) < 0 from
      Int.not_lt.mpr (Int.natCast_nonneg n), ite_false, Int.toNat_natCast]
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    subst S
    simp only [leftSeamLdpTruncationValue, Set.not_nonempty_empty, ↓reduceDIte,
      leftSeamLengthOfInt, show (-1 : ℤ) < 0 by decide, ↓reduceIte,
      leftLengthSup, Set.image_empty, csSup_empty]


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw length set is bounded, without a reachability premise. -/
theorem leftSeamRawPathLengths_bddAbove (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) :
    BddAbove (leftSeamRawPathLengths w h q i t) := by
  apply (present_pathLengths_bddAbove (W q) (HF q)
    (⟨LB q i⟩ : PresentVertex (W q)) ⟨((P q).initial t).1.id⟩).mono
  rintro n ⟨p, hp, hpe⟩
  obtain ⟨_, _, _, r, hr, _⟩ := leftSeamRawPathLift_proved w h q hw i t n p hp hpe
  exact ⟨r, hr⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Corrected identification includes unreachable pairs by retaining the negative sentinel. -/
@[expose] def LeftSeamLdpRawIdentificationWithBottom : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : D),
      q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = hatCodes w h ∧
      ∀ i t, leftSeamLengthOfInt
        (leftSeamLdpDecoder (TC .left (integrateCodes (hatLawCodes ω))) i t) =
          leftLengthSup (leftSeamRawPathLengths w h q i t)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The bottom-valued raw identification holds simultaneously for all endpoint pairs. -/
theorem leftSeamLdpRawIdentificationWithBottom_proved :
    LeftSeamLdpRawIdentificationWithBottom := by
  filter_upwards [rightHatIntegratedCarrierIdentification_proved] with ω hc
  obtain ⟨h, q, _, hq, hw, _⟩ := hc
  refine ⟨h, q, hq, hw, fun i t => ?_⟩
  rw [← hq, leftSeamLdpDecoder_raw _ h q hw i t]
  exact seamValue_sup _ (leftSeamRawPathLengths_bddAbove _ h q hw i t)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The measurable decoder for hatted beta-to-seam lengths, with bottom for unreachable pairs. -/
@[expose] noncomputable def hattedLeftSeamDecoder
    (c : ℕ → Option FiniteThinMap) (k t : ℕ) : WithBot ℕ :=
  leftSeamLengthOfInt (leftSeamLdpDecoder c k t)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The full product-valued hatted decoder is measurable. -/
theorem measurable_hattedLeftSeamDecoder : Measurable hattedLeftSeamDecoder := by
  apply Measurable.of_eval
  intro k
  apply Measurable.of_eval
  intro t
  exact measurable_from_top.comp (measurable_leftSeamLdpDecoder k t)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted decoder required by the left-locality assembly exists. -/
theorem hattedLeftSeamDecoderExists_proved : HattedLeftSeamDecoderExists := by
  refine ⟨hattedLeftSeamDecoder, measurable_hattedLeftSeamDecoder, ?_⟩
  filter_upwards [] with ω
  dsimp only
  intro h hfin hb q hw hq k t
  change leftSeamLengthOfInt
    (leftSeamLdpDecoder (TC .left (integrateCodes (hatLawCodes ω))) k t) = _
  rw [← hq, leftSeamLdpDecoder_raw _ h q hw k t,
    seamValue_sup _ (leftSeamRawPathLengths_bddAbove _ h q hw k t),
    leftSeamRawPathLengths_eq_closed _ h q hw k t,
    hattedLeftBoundary_beta0 _ h hfin hb q hw k]


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A boundary vertex beyond the seam index cannot reach that seam vertex. -/
theorem leftSeamRawPathLengths_empty_of_lt (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (q : D) (hw : (W q) = hatCodes w h) (i t : ℕ) (hti : t < i) :
    leftSeamRawPathLengths w h q i t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro n hn
  rw [leftSeamRawPathLengths_eq_closed w h q hw i t,
    hattedLeftBoundary_beta0 w h hfin hb q hw i] at hn
  obtain ⟨p, _, _, _⟩ := hn
  have hi := leftBetaSeam_index_le w h hfin hb q hw i t p.reachable
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The original natural-maximum identification is false at i = 1, t = 0.
The bottom-valued identification above supplies the assembly without changing its statement. -/
theorem not_leftSeamLdpRawIdentification : ¬ LeftSeamLdpRawIdentification := by
  intro H
  have he : ∀ᵐ ω ∂iidCodeMeasure, False := by
    filter_upwards [H, iidCodes_ae_finite_incident_edges,
      iidCodes_ae_boundaryHitWitnesses] with ω hc hfin hb
    obtain ⟨h, q, _, hw, hlength⟩ := hc
    obtain ⟨n, hn, _⟩ := hlength 1 0
    have hempty := leftSeamRawPathLengths_empty_of_lt _ h hfin hb q hw 1 0 (by omega)
    rw [hempty] at hn
    exact hn.1
  obtain ⟨_, hf⟩ := he.exists
  exact hf

end DirectedDistances.Recursive
