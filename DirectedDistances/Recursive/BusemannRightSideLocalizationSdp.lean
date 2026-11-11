module

public import DirectedDistances.Recursive.BusemannRightSideLocalization
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix
import DirectedDistances.PaperProofs.Section4.ThinMapAncestorRealization
import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfLaunchSeed
import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfSideRange
import DirectedDistances.PaperProofs.Section7.HitCoupling

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.

This file localizes shortest distances to the closed right side of the leftmost SDP
geodesic. Unreachable distances retain the value `⊤`; ordered boundary pairs below
are reached along their boundary path. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section7
open Quiver MeasureTheory Filter

local notation "RightDomain" =>
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
local notation "RB" => fun (q : RightDomain) (j : ℕ) =>
  thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.right j
local notation "SV" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q) a
local notation "SE" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) a

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Natural path lengths attained in the literal closed right side of the leftmost SDP -/
@[expose] def rightSideSdpLengths (q : RightDomain) (j m : ℕ) : Set ℕ :=
  {n | ∃ p : Path (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩,
    p.length = n ∧ ∀ e ∈ pathEdgeList p,
      e ∈ sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Almost surely, right-side shortest lengths equal the raw finite SDP distances eventually,
and their difference is the measurable finite-target representative. Source: -/
@[expose] def RightClosedSideSdpLocalization : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : RightDomain),
      q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = hatCodes w h ∧
      (∀ j, hatLimitVertexMap w h (RB q j) =
        boundaryVertex w (hatBoundaryHitWitnesses w h) (j : ℤ)) ∧
      ∀ j : ℕ, ∀ᶠ m in atTop, ∃ nj n0 : ℕ,
        IsLeast (rightSideSdpLengths q j m) nj ∧
        IsLeast (rightSideSdpLengths q 0 m) n0 ∧
        sdp (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (j : ℤ))
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) =
          (nj : ℕ∞) ∧
        sdp (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) 0)
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) =
          (n0 : ℕ∞) ∧
        boundarySdpDifference ω (j : ℤ) m = (nj : ℤ) - (n0 : ℤ)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Identifies the right boundary edge at index j with the edge at its least hit time. -/
private theorem rightBoundaryEdge_eq_firstHit (u : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R u n ≤ a) (j : ℕ) (hj : 1 ≤ j)
    (hhit : ∃ n, R u n = -(j : ℤ)) :
    kmswRightBoundaryEdge u j = act u (Nat.find hhit) := by
  classical
  obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually u hR j
  let n := max N (Nat.find hhit)
  have ht : Nat.find hhit ≤ n := Nat.le_max_right _ _
  have hmin : (j : ℤ) ≤ -minR u n := by
    have hh := runningMin_le (R u) n (Nat.find hhit) ht
    have hv := Nat.find_spec hhit
    change minR u n ≤ R u (Nat.find hhit) at hh
    omega
  obtain ⟨_, hi, he, _, _⟩ := kmsw_bdy_lower_right_first_hit u n j
    (Nat.find hhit) hj hmin ht (Nat.find_spec hhit)
    (fun k hk => Nat.find_min hhit hk)
  have hg := hN n (Nat.le_max_left _ _)
  rw [List.getElem?_eq_getElem hi, he] at hg
  exact (Option.some.inj hg).symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Identifies each thin-map right boundary vertex with its raw hit-indexed boundary vertex. -/
private theorem rightHat_thinBoundary_sdp (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : RightDomain) (hw : (W q) = hatCodes w h)
    (j : ℕ) :
    hatLimitVertexMap w h (RB q j) =
      boundaryVertex w (hatBoundaryHitWitnesses w h) (j : ℤ) := by
  cases j with
  | zero =>
    change hatLimitVertexMap w h 0 = boundaryVertex w _ (0 : ℤ)
    rw [boundaryVertex_zero]
    exact (hatLimitExplicitInput w h).root
  | succ j =>
    have hb := ancestor_boundaryVertex_eq (W q) (HF q) (HL q) (HT q) (HR q)
      .right (j + 1)
    change RB q (j + 1) = edgeWest (W q) (kmswRightBoundaryEdge (W q) (j + 1)) at hb
    rw [hb, hw]
    have he := rightBoundaryEdge_eq_firstHit (hatCodes w h)
      (hat_R_unbounded_hatted w h) (j + 1) (by omega)
      (hattedRightHit_exists w h (j + 1) (by omega))
    rw [he]
    change hatLimitVertexMap w h (edgeWest (hatCodes w h)
      (act (hatCodes w h) (hattedRightHitTime w h (j + 1) (by omega)))) = _
    have hv : edgeWest (hatCodes w h)
        (act (hatCodes w h) (hattedRightHitTime w h (j + 1) (by omega))) =
        activeInitial (hatCodes w h) (hattedRightHitTime w h (j + 1) (by omega)) := by
      exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1.symm.trans
        (CutConverse.activeInitial_eq _ _).symm
    rw [hv]
    exact (hattedRightHitTime_isLeast_sourceVertex w h
      (hatBoundaryHitWitnesses w h) (j + 1) (by omega)).1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Recovers stream c from q's integrated code within the selected coherent domain. -/
private theorem rightHat_sdpCoherentStream (q : RightDomain) (c : ℕ → Fin 3)
    (hc : q.1 = integrateCodes c) : (W q) = c := by
  obtain ⟨_, _, _, _, hw, _⟩ := selectedCutCoherentDomain_spec
    XDP.sdp renewalTime renewalTime_positiveSuccessTime q
  exact integrateCodes_injective (hw.trans hc)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Shows the integrated hatted code lies in the selected coherent domain almost surely. -/
private theorem rightHat_integrate_mem_sdpCoherent_ae :
    ∀ᵐ ω ∂iidCodeMeasure, integrateCodes (hatLawCodes ω) ∈ RightDomain := by
  have hd : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, p ∈ RightDomain :=
    ae_iff.mpr (selectedCutCoherentDomain_measurable_conull
      XDP.sdp renewalTime renewalTime_positiveSuccessTime).2
  have hm : AEMeasurable (fun ω => integrateCodes (hatLawCodes ω)) iidCodeMeasure :=
    measurable_integrateCodes.comp_aemeasurable aemeasurable_hatLawCodes.1
  exact ae_of_ae_map hm (hatLawCodes_integrate_law.symm ▸ hd)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The actual right boundary of the SDP seam maps to the raw hit-indexed boundary. -/
theorem rightHatThinBoundarySdpIdentification_proved :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (q : RightDomain),
        q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = hatCodes w h ∧
        ∀ j, hatLimitVertexMap w h (RB q j) =
          boundaryVertex w (hatBoundaryHitWitnesses w h) (j : ℤ) := by
  filter_upwards [rightHat_integrate_mem_sdpCoherent_ae,
    iidCodeMeasure_ae_hasFlowLineHits] with ω hq h
  let w := fun i => ω (i + 1)
  let q : RightDomain := ⟨integrateCodes (hatLawCodes ω), hq⟩
  have hc : hatLawCodes ω = hatCodes w h := by
    dsimp only [w]
    simp only [hatLawCodes, dite_eq_left h]
  have hw : (W q) = hatCodes w h := (rightHat_sdpCoherentStream q _ rfl).trans hc
  exact ⟨h, q, rfl, hw, rightHat_thinBoundary_sdp w h q hw⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A vertex in both side vertex sets is an initial vertex of the seam path. -/
private theorem side_vertex_inter (q : RightDomain) (v : PresentVertex (W q))
    (hl : v.id ∈ SV q .left) (hr : v.id ∈ SV q .right) :
    ∃ i, v = ((P q).initial i).1 := by
  have hv : (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q))).pos v.id ∈
      pathTrace (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q)))
        (fun i => ((P q).edge i, false)) := by
    rw [← thinMapSideRegions_inter_eq_seamTrace
      (W q) (HF q) (HL q) (HT q) (HR q) (P q)]
    exact ⟨hl, hr⟩
  obtain ⟨i, hi⟩ := (thinMapVertex_mem_seamTrace_iff (W q) (HF q) (P q) v.id).mp hv
  exact ⟨i, congrArg PresentVertex.mk hi⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Places a non-seam outgoing edge from a side-a vertex in side a's edge set. -/
private theorem nonseam_edge_in_side (q : RightDomain) (a : ThinMapSide)
    {u v : PresentVertex (W q)} (e : u ⟶ v) (hu : Reachable ⟨0⟩ u)
    (hv : u.id ∈ SV q a) (hs : ∀ i, u ≠ ((P q).initial i).1) :
    e.val ∈ SE q a := by
  have hoff : ∀ i, e.val ≠ (P q).edge i := by
    intro i hi
    apply hs i
    exact congrArg PresentVertex.mk
      (e.property.2.1.symm.trans (hi ▸ ((P q).edge_outgoing_at_initial (W q) i).2))
  apply (thinMapArc_subset_sideRegion_iff_seed
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) a e.val hoff).mpr
  apply thinMapArcSeed_mem_side_of_nonseam_launch
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) a e.val e.property.1
  · exact e.property.2.1.symm ▸ hu
  · exact e.property.2.1.symm ▸ hv
  · intro i hi
    exact hs i (congrArg PresentVertex.mk (e.property.2.1.symm.trans hi))
  · exact hoff

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Constructs an infinite path from u by prepending edge e to the path Q. -/
private noncomputable def prependPath {q : RightDomain} {u v : PresentVertex (W q)}
    (e : u ⟶ v) (Q : InfinitePresentPath (W q) v) : InfinitePresentPath (W q) u where
  edge
    | 0 => e.val
    | n + 1 => Q.edge n
  initial
    | 0 => ⟨u, .nil⟩
    | n + 1 => ⟨(Q.initial n).1, e.toPath.comp (Q.initial n).2⟩
  prefix_length n := by
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Path.length_comp, Path.length_toPath, Q.prefix_length, Nat.add_comm]
  prefix_edges n := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [pathEdgeList_comp, Q.prefix_edges, List.ofFn_succ]
      rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Extends an infinite path backward along p, preserving inclusion of its edge range. -/
private theorem extendPath {q : RightDomain} {u v : PresentVertex (W q)}
    (p : Path u v) (S : InfinitePresentPath (W q) v) :
    ∃ Q : InfinitePresentPath (W q) u, Set.range S.edge ⊆ Set.range Q.edge := by
  induction p with
  | nil => exact ⟨S, Set.Subset.rfl⟩
  | @cons v z p e ih =>
    obtain ⟨Q, hQ⟩ := ih (prependPath e S)
    refine ⟨Q, ?_⟩
    rintro f ⟨i, rfl⟩
    exact hQ ⟨i + 1, rfl⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every edge from a root-reachable vertex belongs to the left or right side edge set. -/
private theorem edge_side_dichotomy (q : RightDomain)
    {u v : PresentVertex (W q)} (e : u ⟶ v) (hu : Reachable ⟨0⟩ u) :
    e.val ∈ SE q .left ∨ e.val ∈ SE q .right := by
  classical
  by_cases hs : ∃ i, e.val = (P q).edge i
  · obtain ⟨i, hi⟩ := hs
    exact Or.inl (hi ▸ seamEdge_mem_sideEdges
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left i)
  · have hoff := fun i hi => hs ⟨i, hi⟩
    obtain ⟨p⟩ := hu
    let S := prependPath e (kmswRightmostPath (W q) (HF q) (HL q) (HT q) (HR q) v.id)
    obtain ⟨Q, hQ⟩ := extendPath p S
    obtain ⟨i, hi⟩ := hQ (show e.val ∈ Set.range S.edge from ⟨0, rfl⟩)
    have hseed := thinMapPathTrace_subset_sideRegions
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) Q
      (Set.mem_iUnion.mpr ⟨i, hi ▸
        (thinMapArcSeed_mem_interior (W q) (HF q) e.val).1⟩)
    rw [hi] at hseed
    rcases hseed with hl | hr
    · exact Or.inl ((thinMapArc_subset_sideRegion_iff_seed
        (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left e.val hoff).mpr hl)
    · exact Or.inr ((thinMapArc_subset_sideRegion_iff_seed
        (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right e.val hoff).mpr hr)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A path from a left-side vertex to a right-side vertex contains a seam vertex. -/
private theorem path_hits_seam (q : RightDomain)
    {u v : PresentVertex (W q)} (p : Path u v) (hu : Reachable ⟨0⟩ u)
    (hl : u.id ∈ SV q .left) (hr : v.id ∈ SV q .right) :
    ∃ i, ((P q).initial i).1 ∈ p.vertices := by
  classical
  by_contra hn
  have hno : ∀ z ∈ p.vertices, ∀ i, z ≠ ((P q).initial i).1 := by
    intro z hz i hi
    exact hn ⟨i, hi ▸ hz⟩
  have hend : v.id ∈ SV q .left := by
    clear hr hn
    induction p with
    | nil => exact hl
    | @cons y z p e ih =>
      have hpno : ∀ b ∈ p.vertices, ∀ i, b ≠ ((P q).initial i).1 := by
        intro b hb
        exact hno b ((Path.mem_vertices_cons p e).2 (Or.inl hb))
      have hy := ih hpno
      have ey := nonseam_edge_in_side q .left e (hu.trans p.reachable) hy
        (hno y ((Path.mem_vertices_cons p e).2 (Or.inl p.end_mem_vertices)))
      exact e.property.2.2 ▸
        (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left ey).2
  obtain ⟨i, hi⟩ := side_vertex_inter q v hend hr
  exact hno v p.end_mem_vertices i hi

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Replaces a path between seam vertices with a no-longer path using only right-side edges. -/
private theorem seam_segment (q : RightDomain) (i j : ℕ)
    (p : Path ((P q).initial i).1 ((P q).initial j).1) :
    ∃ r : Path ((P q).initial i).1 ((P q).initial j).1,
      r.length ≤ p.length ∧ ∀ e ∈ pathEdgeList r, e ∈ SE q .right := by
  obtain ⟨_, hgS⟩ := selectedCutCoherentDomain_infinite_extremal
    XDP.sdp renewalTime renewalTime_positiveSuccessTime q
  have hshort : (P q).HasShortestSegments :=
    kmswLeftmostSdpPath_hasShortestSegments
      (W q) (HF q) (HL q) (HT q) (HR q) 0 hgS
  have hij : i ≤ j := by
    by_contra hn
    have hji : j ≤ i := by omega
    have H := (P q).exists_shift_split j (i - j)
    rw [Nat.add_sub_of_le hji] at H
    obtain ⟨_, r, _, _, hlen, _⟩ := H
    have hz := presentVertex_acyclic (W q) _ (r.comp p)
    rw [Path.length_comp, hlen] at hz
    omega
  have H := (P q).exists_shift_split i (j - i)
  rw [Nat.add_sub_of_le hij] at H
  obtain ⟨s, r, heq, _, _, hlist⟩ := H
  have hop := (P q).initial_isShortest (W q) hshort j
  rw [heq] at hop
  refine ⟨r, hop.of_comp_right p, ?_⟩
  intro e he
  rw [hlist] at he
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
  exact hk ▸ seamEdge_mem_sideEdges
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right (i + k.val)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every path between root-reachable right-side vertices has a right-side competitor no
longer than it. Excursions are replaced by shortest seam segments. Source: -/
theorem rightSideSdp_path_dominance (q : RightDomain)
    {u v : PresentVertex (W q)} (p : Path u v) (hu : Reachable ⟨0⟩ u)
    (hur : u.id ∈ SV q .right) (hvr : v.id ∈ SV q .right) :
    ∃ r : Path u v, r.length ≤ p.length ∧
      ∀ e ∈ pathEdgeList r, e ∈ SE q .right := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    by_cases hz : p.length = 0
    · obtain rfl := p.eq_of_length_zero hz
      obtain rfl := p.eq_nil_of_length_zero hz
      exact ⟨.nil, by omega, fun _ he => False.elim (List.not_mem_nil he)⟩
    · obtain ⟨b, e, t, hp, hlen⟩ := p.length_ne_zero_iff_eq_comp.mp hz
      have hb : Reachable (⟨0⟩ : PresentVertex (W q)) b := hu.trans e.toPath.reachable
      by_cases he : e.val ∈ SE q .right
      · have hbr : b.id ∈ SV q .right := e.property.2.2 ▸
          (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right he).2
        obtain ⟨r, hrlen, hr⟩ := ih t.length (by omega) t hb hbr hvr rfl
        refine ⟨e.toPath.comp r, ?_, ?_⟩
        · rw [← hn, hp, Path.length_comp, Path.length_comp]
          exact Nat.add_le_add_left hrlen _
        · intro f hf
          rw [pathEdgeList_comp] at hf
          rcases List.mem_append.mp hf with hf | hf
          · have hfe : f = e.val := by
              change f ∈ ([] ++ [e.val]) at hf
              exact List.mem_singleton.mp hf
            exact hfe ▸ he
          · exact hr f hf
      · have hus : ∃ i, u = ((P q).initial i).1 := by
          by_contra hs
          exact he (nonseam_edge_in_side q .right e hu hur
            (fun i hi => hs ⟨i, hi⟩))
        have hel := (edge_side_dichotomy q e hu).resolve_right he
        have hbl : b.id ∈ SV q .left := e.property.2.2 ▸
          (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left hel).2
        obtain ⟨j, hj⟩ := path_hits_seam q t hb hbl hvr
        obtain ⟨s, t', ht⟩ := t.exists_eq_comp_of_mem_vertices hj
        obtain ⟨i, hi⟩ := hus
        have hex : ∃ r : Path u ((P q).initial j).1,
            r.length ≤ (e.toPath.comp s).length ∧
              ∀ f ∈ pathEdgeList r, f ∈ SE q .right := by
          subst u
          exact seam_segment q i j (e.toPath.comp s)
        obtain ⟨r, hrlen, hr⟩ := hex
        have hjr := seamVertex_mem_sideVertices
          (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right j
        have hjreach : Reachable (⟨0⟩ : PresentVertex (W q))
            ((P q).initial j).1 := hb.trans s.reachable
        have hsplit : p.length = 1 + s.length + t'.length := by
          rw [hp, ht, Path.length_comp, Path.length_comp, Path.length_toPath]
          omega
        obtain ⟨r', hr'len, hr'⟩ := ih t'.length (by omega) t' hjreach hjr hvr rfl
        refine ⟨r.comp r', ?_, ?_⟩
        · simp only [Path.length_comp, Path.length_toPath] at hrlen ⊢
          omega
        · intro f hf
          rw [pathEdgeList_comp] at hf
          exact (List.mem_append.mp hf).elim (hr f) (hr' f)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Constructs a right-side path from boundary index j to boundary index j + d. -/
private theorem boundary_path (q : RightDomain) (j d : ℕ) :
    ∃ p : Path (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q (j + d)⟩,
      ∀ e ∈ pathEdgeList p, e ∈ SE q .right := by
  induction d with
  | zero => exact ⟨.nil, fun _ he => False.elim (List.not_mem_nil he)⟩
  | succ d ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨e, he, hpres, hwest, heast⟩ := thinMapBoundaryVertex_step
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right (j + d)
    let f : (⟨RB q (j + d)⟩ : PresentVertex (W q)) ⟶ ⟨RB q (j + d + 1)⟩ :=
      ⟨e, hpres, hwest, heast⟩
    refine ⟨p.cons f, ?_⟩
    intro a ha
    change a ∈ pathEdgeList p ++ [e] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hp a ha
    · exact (List.mem_singleton.mp ha) ▸ he

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For ordered right-boundary endpoints, the ambient and closed-side shortest lengths are -/
theorem rightSideSdpLengths_least (q : RightDomain) (j m : ℕ) (hjm : j ≤ m) :
    ∃ n : ℕ, IsLeast (rightSideSdpLengths q j m) n ∧
      IsLeast (pathLengths (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩) n ∧
      sdp (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩ = (n : ℕ∞) := by
  have H := boundary_path q j (m - j)
  rw [Nat.add_sub_of_le hjm] at H
  obtain ⟨p, _⟩ := H
  have H0 := boundary_path q 0 j
  obtain ⟨r0, _⟩ := H0
  have hur : RB q j ∈ SV q .right :=
    (thinMapBoundaryVertex_mem_sourceAncestorVertices
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right j).1
  have hvr : RB q m ∈ SV q .right :=
    (thinMapBoundaryVertex_mem_sourceAncestorVertices
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right m).1
  have hroot := r0.reachable
  change Reachable (⟨0⟩ : PresentVertex (W q)) ⟨RB q (0 + j)⟩ at hroot
  rw [Nat.zero_add] at hroot
  obtain ⟨r, hr⟩ := exists_isShortest p.reachable
  obtain ⟨s, hslen, hs⟩ := rightSideSdp_path_dominance q r hroot hur hvr
  have hlen : s.length = r.length := Nat.le_antisymm hslen (hr s)
  refine ⟨r.length, ⟨⟨s, hlen, hs⟩, ?_⟩, ⟨⟨r, rfl⟩, ?_⟩,
    (isShortest_iff_length_eq_sdp r).mp hr |>.symm⟩
  · rintro n ⟨t, ht, _⟩
    rw [← ht]
    exact hr t
  · rintro n ⟨t, ht⟩
    rw [← ht]
    exact hr t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every finite path has a same-length representative in each sufficiently late stage. -/
private theorem path_in_late_stages {w : ℕ → Fin 3} {a b : PresentVertex w}
    (p : Path a b) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ r : Path (⟨a.id⟩ : StagePresentVertex w n) ⟨b.id⟩, r.length = p.length := by
  induction p with
  | nil => exact ⟨0, fun _ _ => ⟨.nil, rfl⟩⟩
  | @cons b c p e ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := e.property.1.eventually_present
    refine ⟨max N M, fun n hn => ?_⟩
    obtain ⟨r, hr⟩ := hN n ((Nat.le_max_left _ _).trans hn)
    obtain ⟨he, hp⟩ := hM n ((Nat.le_max_right _ _).trans hn)
    let en : (⟨b.id⟩ : StagePresentVertex w n) ⟶ ⟨c.id⟩ :=
      ⟨e.val, he, hp,
        (edge_endpoints_eq w he).1.trans e.property.2.1,
        (edge_endpoints_eq w he).2.trans e.property.2.2⟩
    exact ⟨r.cons en, by simp only [Path.length_cons, hr]⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For reachable vertices, stage SDP codes eventually equal the finite SDP distance. -/
private theorem stageSdpCode_eventually_eq (ω : ℕ → Fin 3)
    {a b : PresentVertex (fun i => ω (i + 1))} (hr : Reachable a b) :
    ∀ᶠ n in atTop, busemannStageSdpCode ω n a.id b.id =
      ((sdp a b).toNat : ℤ) := by
  obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
  obtain ⟨N, hN⟩ := path_in_late_stages p
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  obtain ⟨q, hq⟩ := hN n hn
  have heq : sdp (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b.id⟩ =
      sdp a b := by
    apply le_antisymm
    · calc
        sdp (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b.id⟩
            ≤ (q.length : ℕ∞) := sdp_le_length q
        _ = (p.length : ℕ∞) := by rw [hq]
        _ = sdp a b := hp
    · exact sdp_limit_le_sdp_stage (fun i => ω (i + 1)) n ⟨a.id⟩ ⟨b.id⟩
  unfold busemannStageSdpCode
  rw [heq]
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Least boundary path lengths determine the boundary SDP difference nj minus n0. -/
private theorem boundarySdpDifference_of_isLeast (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (j m nj n0 : ℕ)
    (hj : IsLeast (pathLengths (boundaryPresentVertex _ h (j : ℤ))
      (boundaryPresentVertex _ h (m : ℤ))) nj)
    (h0 : IsLeast (pathLengths (boundaryPresentVertex _ h 0)
      (boundaryPresentVertex _ h (m : ℤ))) n0) :
    boundarySdpDifference ω (j : ℤ) m = (nj : ℤ) - (n0 : ℤ) := by
  let a := boundaryPresentVertex (fun i => ω (i + 1)) h (j : ℤ)
  let b := boundaryPresentVertex (fun i => ω (i + 1)) h (m : ℤ)
  let a0 := boundaryPresentVertex (fun i => ω (i + 1)) h 0
  have hja : Reachable a b := by
    obtain ⟨p, hp⟩ := hj.1
    exact p.reachable
  have h0a : Reachable a0 b := by
    obtain ⟨p, hp⟩ := h0.1
    exact p.reachable
  have hlenj : (sdp a b).toNat = nj := by
    obtain ⟨p, hp⟩ := hj.1
    change p.length = nj at hp
    have hshort : IsShortest p := by
      intro q
      have hq : q.length ∈ pathLengths a b := ⟨q, rfl⟩
      have hle := hj.2 hq
      exact hp ▸ hle
    have heq := (isShortest_iff_length_eq_sdp p).mp hshort
    calc
      (sdp a b).toNat = ((p.length : ℕ∞).toNat) :=
        congrArg ENat.toNat heq.symm
      _ = p.length := by simp
      _ = nj := hp
  have hlen0 : (sdp a0 b).toNat = n0 := by
    obtain ⟨p, hp⟩ := h0.1
    change p.length = n0 at hp
    have hshort : IsShortest p := by
      intro q
      have hq : q.length ∈ pathLengths a0 b := ⟨q, rfl⟩
      have hle := h0.2 hq
      exact hp ▸ hle
    have heq := (isShortest_iff_length_eq_sdp p).mp hshort
    calc
      (sdp a0 b).toNat = ((p.length : ℕ∞).toNat) :=
        congrArg ENat.toNat heq.symm
      _ = p.length := by simp
      _ = n0 := hp
  unfold boundarySdpDifference
  simp only [rightHat_boundaryIdTotal_eq ω h]
  apply eventualIntValue_eq
  filter_upwards [stageSdpCode_eventually_eq ω hja,
    stageSdpCode_eventually_eq ω h0a] with s hj h0
  have hj' : busemannStageSdpCode ω s a.id b.id = (nj : ℤ) :=
    hj.trans (congrArg (fun n : ℕ => (n : ℤ)) hlenj)
  have h0' : busemannStageSdpCode ω s a0.id b.id = (n0 : ℤ) :=
    h0.trans (congrArg (fun n : ℕ => (n : ℤ)) hlen0)
  simpa only [a, b, a0, boundaryPresentVertex] using congrArg₂ (· - ·) hj' h0'

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Raw finite SDP distances between ordered right-boundary vertices are attained in the
closed right side eventually, with the exact stage difference. Source: -/
theorem rightClosedSideSdpLocalization_proved : RightClosedSideSdpLocalization := by
  filter_upwards [rightHatThinBoundarySdpIdentification_proved] with ω hω
  obtain ⟨h, q, hq, hw, hboundary⟩ := hω
  let w := fun i => ω (i + 1)
  refine ⟨h, q, hq, hw, hboundary, ?_⟩
  intro j
  refine eventually_atTop.mpr ⟨j, fun m hjm => ?_⟩
  obtain ⟨nj, hsj, hgj, hsdpj⟩ := rightSideSdpLengths_least q j m hjm
  obtain ⟨n0, hs0, hg0, hsdp0⟩ :=
    rightSideSdpLengths_least q 0 m (Nat.zero_le m)
  have hlengths (i : ℕ) :
      pathLengths (⟨RB q i⟩ : PresentVertex (W q)) ⟨RB q m⟩ =
        pathLengths (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (i : ℤ))
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) := by
    have hh := rightHatPathLengthIdentification_proved w h
      (⟨RB q i⟩ : PresentVertex (hatCodes w h)) ⟨RB q m⟩
    rw [hw]
    rw [hboundary i, hboundary m] at hh
    simpa only [boundaryPresentVertex] using hh
  have hsdp (i : ℕ) :
      sdp (⟨RB q i⟩ : PresentVertex (W q)) ⟨RB q m⟩ =
        sdp (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (i : ℤ))
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) := by
    have hh := rightHat_sdp w h
      (⟨RB q i⟩ : PresentVertex (hatCodes w h)) ⟨RB q m⟩
    rw [hw]
    rw [hboundary i, hboundary m] at hh
    simpa only [boundaryPresentVertex] using hh
  have hsdpRawj := (hsdp j).symm.trans hsdpj
  have hsdpRaw0 := (hsdp 0).symm.trans hsdp0
  rw [hlengths j] at hgj
  rw [hlengths 0] at hg0
  exact ⟨nj, n0, hsj, hs0, hsdpRawj, hsdpRaw0,
    boundarySdpDifference_of_isLeast ω (hatBoundaryHitWitnesses w h) j m nj n0 hgj hg0⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every right-side path to a right-side ancestor endpoint uses edges in its ancestor restriction. -/
private theorem sidePath_ancestorEdges (q : RightDomain) (m : ℕ)
    {u v : PresentVertex (W q)} (p : Path u v)
    (hp : ∀ e ∈ pathEdgeList p, e ∈ SE q .right)
    (ht : Relation.ReflTransGen
      (sideDirectedStep (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right)
      v.id (RB q m)) :
    ∀ e ∈ pathEdgeList p,
      e ∈ sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right m := by
  induction p with
  | nil => exact fun _ he => False.elim (List.not_mem_nil he)
  | @cons y z p e ih =>
    have he : e.val ∈ SE q .right := hp e.val (by
      change e.val ∈ pathEdgeList p ++ [e.val]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
    have hend := sideEdges_endpoints
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right he
    have hstep : sideDirectedStep
        (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right y.id z.id :=
      ⟨e.val, he, e.property⟩
    have hy := Relation.ReflTransGen.head hstep ht
    have hp' : ∀ f ∈ pathEdgeList p, f ∈ SE q .right := by
      intro f hf
      exact hp f (List.mem_append.mpr (Or.inl hf))
    intro f hf
    change f ∈ pathEdgeList p ++ [e.val] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih hp' hy f hf
    · have hf' : f = e.val := List.mem_singleton.mp hf
      subst f
      exact ⟨he, ⟨hend.1, e.property.2.1.symm ▸ hy⟩,
        ⟨hend.2, e.property.2.2.symm ▸ ht⟩⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every closed-right-side path to the m-th boundary vertex belongs to its geometric
ancestor restriction, retaining individual edge IDs. Source: -/
theorem rightSideSdp_path_mem_ancestorEdges (q : RightDomain) (m : ℕ)
    {u : PresentVertex (W q)} (p : Path u ⟨RB q m⟩)
    (hp : ∀ e ∈ pathEdgeList p, e ∈ SE q .right) :
    ∀ e ∈ pathEdgeList p,
      e ∈ sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right m :=
  sidePath_ancestorEdges q m p hp .refl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Closed-side path lengths agree with every later finite geometric ancestor restriction.
This does not identify that restriction with the thin code. Source: -/
theorem rightSideSdpLengths_eq_ancestorLengths (q : RightDomain) (j m s : ℕ)
    (hms : m ≤ s) :
    rightSideSdpLengths q j m =
      {n | ∃ p : Path (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩,
        p.length = n ∧ ∀ e ∈ pathEdgeList p,
          e ∈ sourceAncestorEdges
            (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right s} := by
  ext n
  constructor
  · rintro ⟨p, hp, hs⟩
    refine ⟨p, hp, fun e he => ?_⟩
    exact sourceAncestorEdges_mono (W q) (HF q) (HL q) (HT q) (HR q) (P q)
      .right hms (rightSideSdp_path_mem_ancestorEdges q m p hs e he)
  · rintro ⟨p, hp, hs⟩
    exact ⟨p, hp, fun e he => (hs e he).1⟩

end DirectedDistances.Recursive
