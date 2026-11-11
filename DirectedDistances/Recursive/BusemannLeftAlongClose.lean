module

public import DirectedDistances.Recursive.BusemannLeftAlongGeodesic
public import DirectedDistances.KMSW.GluingBoundaryOrder
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.Recursive.OneStepTransport

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.

The beta interface is the image of the hatted left boundary. All transport retains
present arrows and individual edge identities. Finite incidence is the structural
condition needed to enumerate beta; coherent code equality identifies the carriers. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "RightDomain" =>
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
local notation "Q" q => sourceAncestorPath
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "SE" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a
local notation "SV" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every beta entry lifts to the hatted closed left side, through the ordered left boundary. -/
theorem leftAlongEntryLocalization_proved (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (q : RightDomain)
    (hw : (W q) = hatCodes w h) : LeftAlongEntryLocalization w h q := by
  intro v hv
  let hb := hatBoundaryHitWitnesses w h
  obtain ⟨i, hi⟩ := leftHatEntryOnBeta_proved w hfin hb v hv
  have htail : kmswBeta0Vertices w hfin hb i =
      edgeWest w (kmswBeta0Stream w hfin hb i).1 := by
    cases i with
    | zero => exact (kmswBeta0Stream_start w hfin hb).symm
    | succ i => exact (kmswBeta0Stream_chain w hfin hb i).symm
  let a := edgeWest (W q) (kmswLeftBoundaryEdge (W q) i)
  have ha : a ∈ SV q .left := by
    have hv := thinMapBoundaryVertex_mem_sourceAncestorVertices
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left i
    have haw : a = thinMapBoundaryVertex
        (W q) (HF q) (HL q) (HT q) (HR q) .left i := by
      dsimp [a]
      cases i with
      | zero => exact (kmswLeftBoundary_infinite_present_path
          (W q) (HT q) (HL q) (HR q)).2.2.1
      | succ i => exact ((kmswLeftBoundary_infinite_present_path
          (W q) (HT q) (HL q) (HR q)).2.1 i).symm
    exact haw ▸ hv.1
  refine ⟨a, ha, ?_⟩
  rw [hi, htail, ← hattedLeftBoundaryBeta0EdgeCorrespondence_proved w h hfin hb i,
    (hatLimitEdgeMap_endpoint_alignment w h _).1]
  dsimp [a]
  rw [hw]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Mapped path vertices are precisely images of the original visited vertices. -/
private theorem closeMap_vertices {V U : Type*} [Quiver V] [Quiver U]
    (F : Prefunctor V U) {a b : V} (p : Path a b) (z : U)
    (hz : z ∈ (F.mapPath p).vertices) : ∃ v ∈ p.vertices, F.obj v = z := by
  induction p with
  | nil =>
    have he : z = F.obj a := by
      simpa only [Prefunctor.mapPath_nil, Path.vertices_nil, List.mem_singleton] using hz
    exact ⟨a, Path.start_mem_vertices _, he.symm⟩
  | @cons b c p e ih =>
    rcases (Path.mem_vertices_cons (F.mapPath p) (F.map e)).mp hz with hz | hz
    · obtain ⟨v, hv, he⟩ := ih hz
      exact ⟨v, (Path.mem_vertices_cons p e).mpr (Or.inl hv), he⟩
    · exact ⟨c, Path.end_mem_vertices _, hz.symm⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Injectivity of the hatted vertex injection on the identified coherent carrier. -/
private theorem closeVertex_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatLimitVertexMap w h) := by
  intro a b hab
  exact vertex_inj (hatLimitExplicitInput w h)
    (kmswVertexAllocated_all _ ⟨a⟩) (kmswVertexAllocated_all _ ⟨b⟩) hab

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted exchange transports to raw endpoints; its suffix has no later seam visit. -/
private theorem closeHat_exchange (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h)
    (u v : PresentVertex (W q)) (hu : u.id ∈ SV q .left)
    (hv : v.id ∈ SV q .right)
    (p : Path (⟨hatLimitVertexMap w h u.id⟩ : PresentVertex w)
      ⟨hatLimitVertexMap w h v.id⟩) (hp : IsLongest p) :
    ∃ t, ∃ a : Path (⟨hatLimitVertexMap w h u.id⟩ : PresentVertex w)
        ((leftAlongRawGeodesic w h q hw).initial t).1,
      ∃ b : Path ((leftAlongRawGeodesic w h q hw).initial t).1
        ⟨hatLimitVertexMap w h v.id⟩,
      a.length + b.length = p.length ∧ IsLongest (a.comp b) ∧
      (∀ e ∈ pathEdgeList a, e ∈ closedLeftEdges w h q) ∧
      (∀ e ∈ pathEdgeList b, e ∈ closedRightEdges w h q) ∧
      ∀ s, ((leftAlongRawGeodesic w h q hw).initial s).1 ∈ b.vertices → s = t := by
  have hlift : ∃ r : Path u v, r.length = p.length := by
    have hh := rightHat_path_lift w h ⟨u.id⟩ ⟨v.id⟩ p
    erw [← hw] at hh
    exact hh
  obtain ⟨r, hr⟩ := hlift
  have hrl : IsLongest r := by
    intro s
    have hs := hp ((alongHatFunctor w h q hw).mapPath s)
    erw [alongMap_length w h q hw s, ← hr] at hs
    exact hs
  obtain ⟨t, a, b, hlen, _, ha, hb, ht⟩ :=
    leftAlongHat_geodesicExchange q u hu v hv r hrl
  have hvertex := leftAlongRawGeodesic_vertex w h q hw t
  refine ⟨t, ?_⟩
  erw [hvertex]
  let F := alongHatFunctor w h q hw
  refine ⟨F.mapPath a, F.mapPath b, ?_, ?_, ?_, ?_, ?_⟩
  · erw [alongMap_length w h q hw a, alongMap_length w h q hw b, hlen, hr]
  · apply hp.of_length_eq
    erw [Path.length_comp, alongMap_length w h q hw a,
      alongMap_length w h q hw b, hlen, hr]
  · intro e he
    erw [alongMap_edges] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact Or.inr ⟨f, ha f hf, rfl⟩
  · intro e he
    erw [alongMap_edges] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact ⟨f, hb f hf, rfl⟩
  · intro s hs
    obtain ⟨z, hz, heq⟩ := closeMap_vertices F b _ hs
    have hid := congrArg PresentVertex.id heq
    erw [leftAlongRawGeodesic_vertex] at hid
    have hzq : z = ((Q q).initial s).1 := congrArg PresentVertex.mk
      (closeVertex_injective w h hid)
    exact ht s (hzq ▸ hz)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
First entry and hatted exchange give the full raw single-seam exchange. -/
theorem leftAlongRawGeodesicExchange_proved (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (q : RightDomain)
    (hw : (W q) = hatCodes w h) : LeftAlongRawGeodesicExchange w h q hw := by
  intro x hx y hy p hp
  obtain ⟨v, hv, hvy⟩ := hy
  have hyEq : y = (⟨hatLimitVertexMap w h v⟩ : PresentVertex w) :=
    (congrArg PresentVertex.mk hvy).symm
  subst y
  rcases hx with hx | ⟨u, hu, hux⟩
  · have hyHat : (⟨hatLimitVertexMap w h v⟩ : PresentVertex w) ∈ leftHatVertices w :=
      alloc_reachable (hatLimitExplicitInput w h) (kmswVertexAllocated_all _ ⟨v⟩)
    obtain ⟨z, hz, c, d, hsplit, hc, _⟩ :=
      leftAlong_firstEntry_closedLeft w h q p hx hyHat
    obtain ⟨u, hu, huz⟩ := leftAlongEntryLocalization_proved w h hfin q hw z hz
    have hzEq : z = (⟨hatLimitVertexMap w h u⟩ : PresentVertex w) :=
      (congrArg PresentVertex.mk huz).symm
    subst z
    have hd : IsLongest d := by
      have hh : IsLongest (c.comp d) := hsplit ▸ hp
      exact hh.of_comp_right
    obtain ⟨t, a, b, hlen, _, ha, hb, ht⟩ :=
      closeHat_exchange w h q hw ⟨u⟩ ⟨v⟩ hu hv d hd
    refine ⟨t, c.comp a, b, ?_, ?_, ?_, hb, ht⟩
    · rw [Path.length_comp, hsplit, Path.length_comp]
      omega
    · apply hp.of_length_eq
      simp only [Path.length_comp]
      rw [hsplit, Path.length_comp]
      omega
    · intro e he
      rw [pathEdgeList_comp] at he
      exact (List.mem_append.mp he).elim (hc e) (ha e)
  · have hxEq : x = (⟨hatLimitVertexMap w h u⟩ : PresentVertex w) :=
      (congrArg PresentVertex.mk hux).symm
    subst x
    exact closeHat_exchange w h q hw ⟨u⟩ ⟨v⟩ hu hv p hp

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw seam has distinct vertices, since its finite root distances are their indices. -/
private theorem closeSeam_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) :
    Function.Injective (fun t => ((leftAlongRawGeodesic w h q hw).initial t).1) := by
  intro i j hij
  have hi := leftAlongRawGeodesic_root_distance w h q hw i
  have hj := leftAlongRawGeodesic_root_distance w h q hw j
  dsimp only at hij
  rw [hij, hj] at hi
  exact (ENat.natCast_inj.mp (WithBot.coe_inj.mp hi)).symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every reachable closed-left start has its full finite maximum inside the closed left side. -/
theorem leftAlongClosedLeft_greatest (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (q : RightDomain)
    (hw : (W q) = hatCodes w h) (x : PresentVertex w)
    (hx : x ∈ closedLeftVertices w h q) (t : ℕ)
    (hr : Reachable x ((leftAlongRawGeodesic w h q hw).initial t).1) :
    ∃ n : ℕ, IsGreatest (leftClosedSidePathLengths w (closedLeftEdges w h q)
      x ((leftAlongRawGeodesic w h q hw).initial t).1) n ∧
      n = presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin) hr := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove
    (present_pathLengths_bddAbove w hfin x _) hr
  have hyr : ((leftAlongRawGeodesic w h q hw).initial t).1 ∈
      closedRightVertices w h q := by
    rw [leftAlongRawGeodesic_vertex]
    exact ⟨_, seamVertex_mem_sideVertices
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right t, rfl⟩
  obtain ⟨i, a, b, hlen, _, ha, _, ht⟩ :=
    leftAlongRawGeodesicExchange_proved w h hfin q hw x hx _ hyr p hp
  have hti : t = i := ht t b.end_mem_vertices
  subst i
  have hb0 := presentVertex_acyclic w _ b
  have halen : a.length = p.length := by omega
  refine ⟨a.length, ⟨⟨a, rfl, ha⟩, ?_⟩, ?_⟩
  · rintro n ⟨r, rfl, _⟩
    rw [halen]
    exact hp r
  · rw [presentLdpFiniteNat_eq_length _ hr hp, halen]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every strictly negative boundary vertex is outside the root-reachable hatted map. -/
private theorem closeNegative_outside (w : ℕ → Fin 3) (hb : BoundaryHitWitnesses w)
    (j : ℕ) (hj : 1 ≤ j) :
    boundaryPresentVertex w hb (-(j : ℤ)) ∉ leftHatVertices w := by
  have hne : boundaryVertex w hb (-(j : ℤ)) ≠ 0 := by
    intro he
    have hh := boundaryVertex_injective w hb
      (he.trans (boundaryVertex_zero w hb).symm)
    omega
  have noReach (v : PresentVertex w) (hne : v.id ≠ 0)
      (hno : ∀ e, EdgePresent w e → edgeEast w e ≠ v.id) :
      ¬ Reachable (⟨0⟩ : PresentVertex w) v := by
    rintro ⟨p⟩
    cases p with
    | nil => exact hne rfl
    | cons p e => exact hno e.val e.property.1 e.property.2.2
  exact noReach _ hne (fun e he => boundaryVertex_nonpos_no_incoming w hb (by omega) e he)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite reachable distance transport used in the seam profile characterization. -/
private theorem closePath_in_late_stages {w : ℕ → Fin 3} {a b : PresentVertex w}
    (p : Path a b) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ q : Path (⟨a.id⟩ : StagePresentVertex w n) ⟨b.id⟩,
        q.length = p.length := by
  induction p with
  | nil => exact ⟨0, fun _ _ => ⟨Path.nil, rfl⟩⟩
  | @cons b c p e ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := e.property.1.eventually_present
    refine ⟨max N M, fun n hn => ?_⟩
    obtain ⟨q, hq⟩ := hN n ((Nat.le_max_left _ _).trans hn)
    obtain ⟨he, hp⟩ := hM n ((Nat.le_max_right _ _).trans hn)
    let en : (⟨b.id⟩ : StagePresentVertex w n) ⟶ ⟨c.id⟩ :=
      ⟨e.val, he, hp,
        (edge_endpoints_eq w he).1.trans e.property.2.1,
        (edge_endpoints_eq w he).2.trans e.property.2.2⟩
    exact ⟨q.cons en, by simp only [Path.length_cons, hq]⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite reachable distance transport used in the seam profile characterization. -/
private theorem closeStageLdpCode_eventually_eq (ω : ℕ → Fin 3)
    (hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)))
    {a b : PresentVertex (fun i => ω (i + 1))} (hr : Reachable a b) :
    ∀ᶠ n in atTop, busemannStageLdpCode ω n a.id b.id =
      (presentLdpFiniteNat hb hr : ℤ) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  obtain ⟨N, hN⟩ := closePath_in_late_stages p
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  obtain ⟨q, hq⟩ := hN n hn
  have heq : ldpSup (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b.id⟩ =
      (p.length : WithBot ℕ) := by
    apply IsGreatest.csSup_eq
    constructor
    · exact ⟨q.length, ⟨q, rfl⟩, by rw [hq]⟩
    · rintro z ⟨l, ⟨r, rfl⟩, rfl⟩
      have hh := hp ((stageToLimit (fun i => ω (i + 1)) n).mapPath r)
      have hlen := stageToLimit_length (fun i => ω (i + 1)) n r
      have hh' : r.length ≤ p.length := hlen ▸ hh
      change (r.length : WithBot ℕ) ≤ (p.length : WithBot ℕ)
      exact (WithBot.coe_le_coe (α := ℕ) (a := r.length) (b := p.length)).mpr hh'
  rw [presentLdpFiniteNat_eq_length hb hr hp]
  unfold busemannStageLdpCode
  rw [heq]
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite reachable distance transport used in the seam profile characterization. -/
private theorem closeBoundaryLdpDifference_eq (ω : ℕ → Fin 3)
    (hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)))
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) (j : ℕ)
    (hr0 : Reachable (boundaryPresentVertex _ h 0) (boundaryPresentVertex _ h (j : ℤ)))
    (hrk : Reachable (boundaryPresentVertex _ h k) (boundaryPresentVertex _ h (j : ℤ))) :
    boundaryLdpDifference ω k j =
      (presentLdpFiniteNat hb hrk : ℤ) - (presentLdpFiniteNat hb hr0 : ℤ) := by
  unfold boundaryLdpDifference
  simp only [rightHat_boundaryIdTotal_eq ω h]
  apply eventualIntValue_eq
  filter_upwards [closeStageLdpCode_eventually_eq ω hb hrk,
    closeStageLdpCode_eventually_eq ω hb hr0] with n hk h0
  exact congrArg₂ (· - ·) hk h0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite reachable distance transport used in the seam profile characterization. -/
private theorem closeReaches_boundary_tail (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : PresentVertex w)
    (hv : kmswVertexAllocated w v) :
    ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable v (boundaryPresentVertex w h l) := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨q, hqrec, hnq⟩ :=
    (right_record_infinite w h.R_unbounded_below).exists_gt n
  have hqpos : 0 < q := by omega
  have hrec : ∀ i < q, R w q < R w i := hqrec
  have hneg : R w q < 0 := by
    have hh := hrec 0 hqpos
    simpa only [R, Finset.sum_range_zero] using hh
  let b : ℤ := -R w q
  have hb : 1 ≤ b := by dsimp [b]; omega
  have htime : boundaryHitTime w h b = q := by
    have hle : boundaryHitTime w h b ≤ q := by
      rw [boundaryHitTime_right_eq_find w h hb]
      exact Nat.find_min' (h.rightHit b hb) (by dsimp [b]; omega)
    have hge : q ≤ boundaryHitTime w h b := by
      by_contra hnot
      have hh := hrec (boundaryHitTime w h b) (by omega)
      have hh' := boundaryHitTime_right_spec w h hb
      rw [hh'] at hh
      have hRb : R w q = -b := by dsimp [b]; omega
      omega
    omega
  have heq : recordVertex w q = boundaryPresentVertex w h b := by
    apply congrArg PresentVertex.mk
    have he := edge_endpoints_eq w (act_lt_nextEdge w (le_refl q))
    rw [boundaryVertex_eq_edgeWest_hit w h b, htime]
    exact he.1
  have hvq : v.id < (kmswStage w (q - 1)).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono w (by omega : n ≤ q - 1))
  have hr : Reachable v (boundaryPresentVertex w h b) := by
    have hh := allocated_vertex_reaches_strict_record w q
      (fun i hi => by have := hrec i hi; omega) hqpos v.id hvq
    have hvid : (⟨v.id⟩ : PresentVertex w) = v := by cases v; rfl
    rw [hvid, heq] at hh
    exact hh
  refine ⟨b.toNat, fun l hl => hr.trans ?_⟩
  exact boundaryVertex_nonneg_reachable w h (by omega) (by omega)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The measurable boundary differences stabilize to the characterized Busemann value. -/
private theorem closeBoundary_eventually (ω : ℕ → Fin 3)
    (hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)))
    (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (X : ℤ → ℤ) (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h) X)
    (k : ℤ) : ∀ᶠ m in atTop, boundaryLdpDifference ω k m = X k := by
  let w := fun i => ω (i + 1)
  obtain ⟨B0, hB0⟩ := closeReaches_boundary_tail w h
    (boundaryPresentVertex w h 0) (boundaryVertex_allocated w h 0)
  obtain ⟨Bk, hBk⟩ := closeReaches_boundary_tail w h
    (boundaryPresentVertex w h k) (boundaryVertex_allocated w h k)
  let B := max B0 Bk
  let y : ℕ → PresentVertex w := fun j => boundaryPresentVertex w h ((B + j : ℕ) : ℤ)
  have hy : Function.Injective y := by
    intro i j hij
    have hh := boundaryVertex_injective w h (congrArg PresentVertex.id hij)
    dsimp [y, boundaryPresentVertex] at hh
    omega
  have hr : ∀ j, Reachable (boundaryPresentVertex w h 0) (y j) ∧
      Reachable (boundaryPresentVertex w h k) (y j) := by
    intro j
    exact ⟨hB0 _ (by dsimp [B]; omega), hBk _ (by dsimp [B]; omega)⟩
  obtain ⟨N, hN⟩ := hX.2 0 k y hy hr
  refine eventually_atTop.mpr ⟨B + N, fun j hj => ?_⟩
  have hjB : B + (j - B) = j := by omega
  have heq := closeBoundaryLdpDifference_eq ω hb h k (B + (j - B))
    (hr (j - B)).1 (hr (j - B)).2
  have hx := hN (j - B) (by omega)
  rw [hX.1, sub_zero] at hx
  exact (congrArg (boundaryLdpDifference ω k) hjB).symm.trans (heq.trans hx.symm)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The characterized Busemann function evaluated on the actual raw seam gives its left profile. -/
private theorem closeSeam_formula (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hfin : hatLimitFiniteIncidence (fun i => ω (i + 1))) (q : RightDomain)
    (hw : (W q) = hatCodes (fun i => ω (i + 1)) h)
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin _ hfin)
      (boundaryPresentVertex _ hb) X) :
    LeftBusemannAlongGeodesic ω (leftAlongRawGeodesic _ h q hw)
      (closedLeftEdges _ h q) := by
  let w := fun i => ω (i + 1)
  let P := leftAlongRawGeodesic w h q hw
  let bound := presentPathLengthsBounded_of_hfin w hfin
  intro j hj
  let k : ℤ := -(j : ℤ)
  have hboundary := closeBoundary_eventually ω bound hb X hX k
  refine ⟨X k, ?_, hboundary, ?_⟩
  · exact eventualIntValue_eq 0 hboundary
  · let x := boundaryPresentVertex w hb k
    have hx : x ∈ closedLeftVertices w h q :=
      Or.inl (closeNegative_outside w hb j hj)
    obtain ⟨B, hB⟩ := eventually_atTop.mp
      (leftAlongRawGeodesic_eventually_reachable w h q hw x)
    let y : ℕ → PresentVertex w := fun i => (P.initial (B + i)).1
    have hy : Function.Injective y := by
      intro i l hil
      have hh := closeSeam_injective w h q hw hil
      omega
    have hr : ∀ i, Reachable (boundaryPresentVertex w hb 0) (y i) ∧
        Reachable (boundaryPresentVertex w hb k) (y i) := by
      intro i
      refine ⟨?_, hB (B + i) (by omega)⟩
      simpa only [boundaryPresentVertex, boundaryVertex_zero] using
        (P.initial (B + i)).2.reachable
    obtain ⟨N, hN⟩ := hX.2 0 k y hy hr
    refine eventually_atTop.mpr ⟨B + N, fun t ht => ?_⟩
    let i := t - B
    have hi : B + i = t := by dsimp [i]; omega
    obtain ⟨n, hn, hnval⟩ := leftAlongClosedLeft_greatest
      w h hfin q hw x hx (B + i) (hr i).2
    have hdiff := hN i (by dsimp [i]; omega)
    have hroot : presentLdpFiniteNat bound (hr i).1 = B + i := by
      have hh := presentLdpFiniteNat_eq_length bound
        (P.initial (B + i)).2.reachable
        (leftAlongRawGeodesic_initial_isLongest w h q hw (B + i))
      simpa only [boundaryPresentVertex, boundaryVertex_zero] using
        hh.trans (P.prefix_length (B + i))
    rw [hX.1, sub_zero, hroot, ← hnval] at hdiff
    refine ⟨n, ?_, leftAlongRawGeodesic_root_distance w h q hw t, ?_⟩
    · rw [← hi]
      rw [rightHat_boundaryIdTotal_eq ω hb]
      exact hn
    · rw [← hi]
      exact hdiff.symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Almost surely the left profile is the eventual closed-left maximum minus the seam index. -/
theorem leftAlongBusemannFormulaAE_proved : LeftAlongBusemannFormulaAE := by
  filter_upwards [rightHatIntegratedCarrierIdentification_proved,
    iidCodes_ae_boundaryBusemannLDP_existsUnique] with ω hc hω
  obtain ⟨h, q, _, hq, hw, _⟩ := hc
  obtain ⟨hfin, hb, X, hX, _⟩ := hω
  exact ⟨h, q, hw, hq, closeSeam_formula ω h hfin q hw hb X hX⟩

end DirectedDistances.Recursive
