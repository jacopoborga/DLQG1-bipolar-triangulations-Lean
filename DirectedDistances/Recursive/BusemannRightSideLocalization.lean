module

public import DirectedDistances.Recursive.BusemannRightSideLocality
import DirectedDistances.PaperProofs.Section7.HitCoupling
import DirectedDistances.PaperProofs.Section4.ThinMapAncestorRealization
import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfLaunchSeed
import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix












public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section7
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
local notation "P" q => sourceAncestorPath
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "RB" => fun (q : RightDomain) (j : ℕ) =>
  thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.right j

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
Deterministic ordered-boundary identification at every nonnegative index, including zero. -/
theorem rightHat_thinBoundary (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : RightDomain) (hw : (W q) = hatCodes w h) (j : ℕ) :
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
The Section 4 indexed right-boundary vertices map to the raw boundary vertices. -/
theorem rightHatThinBoundaryIdentification_proved : RightHatThinBoundaryIdentification := by
  filter_upwards [rightHat_integrate_mem_coherent_ae,
    iidCodeMeasure_ae_hasFlowLineHits] with ω hq h
  let w := fun i => ω (i + 1)
  let q : RightDomain := ⟨integrateCodes (hatLawCodes ω), hq⟩
  have hc : hatLawCodes ω = hatCodes w h := by
    dsimp only [w]
    simp only [hatLawCodes, dite_eq_left h]
  have hw : (W q) = hatCodes w h := (rightHat_coherent_stream q _ rfl).trans hc
  exact ⟨h, q, rfl, hw, rightHat_thinBoundary w h q hw⟩

local notation "SV" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q) a
local notation "SE" => fun (q : RightDomain) (a : ThinMapSide) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) a

private theorem side_vertex_inter (q : RightDomain) (v : PresentVertex (W q))
    (hl : v.id ∈ SV q .left) (hr : v.id ∈ SV q .right) :
    ∃ i, v = ((P q).initial i).1 := by
  have hv : (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q))).pos v.id ∈
      pathTrace (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q)))
        (fun i => ((P q).edge i, false)) := by
    rw [← thinMapSideRegions_inter_eq_seamTrace (W q) (HF q) (HL q) (HT q) (HR q) (P q)]
    exact ⟨hl, hr⟩
  obtain ⟨i, hi⟩ := (thinMapVertex_mem_seamTrace_iff (W q) (HF q) (P q) v.id).mp hv
  exact ⟨i, congrArg PresentVertex.mk hi⟩

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

private theorem seam_segment (q : RightDomain) (i j : ℕ)
    (p : Path ((P q).initial i).1 ((P q).initial j).1) :
    ∃ r : Path ((P q).initial i).1 ((P q).initial j).1,
      p.length ≤ r.length ∧ ∀ e ∈ pathEdgeList r, e ∈ SE q .right := by
  have hlong : (P q).HasLongestSegments :=
    kmswLeftmostLdpPath_hasLongestSegments
      (W q) (HF q) (HL q) (HT q) (HR q) 0 _
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
  have hop := ((P q).initial_isLongest (W q) hlong j)
  rw [heq] at hop
  refine ⟨r, hop.of_comp_right p, ?_⟩
  intro e he
  rw [hlist] at he
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
  exact hk ▸ seamEdge_mem_sideEdges
    (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right (i + k.val)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every path between root-reachable right-side vertices has a right-side competitor
of at least its length. Excursions are replaced by longest seam segments. -/
theorem rightSide_path_dominance (q : RightDomain)
    {u v : PresentVertex (W q)} (p : Path u v) (hu : Reachable ⟨0⟩ u)
    (hur : u.id ∈ SV q .right) (hvr : v.id ∈ SV q .right) :
    ∃ r : Path u v, p.length ≤ r.length ∧
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
            (e.toPath.comp s).length ≤ r.length ∧
              ∀ f ∈ pathEdgeList r, f ∈ SE q .right := by
          subst u
          exact seam_segment q i j (e.toPath.comp s)
        obtain ⟨r, hrlen, hr⟩ := hex
        have hjr := seamVertex_mem_sideVertices
          (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right j
        have hjreach : Reachable (⟨0⟩ : PresentVertex (W q)) ((P q).initial j).1 :=
          hb.trans s.reachable
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

private theorem sup_eq_of_greatest {V : Type*} [Quiver V] {a b : V} {n : ℕ}
    (h : IsGreatest (pathLengths a b) n) : ldpSup a b = (n : WithBot ℕ) := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨n, h.1, rfl⟩
  · rintro z ⟨k, hk, rfl⟩
    exact WithBot.coe_le_coe.mpr (h.2 hk)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For ordered right-boundary endpoints, both the closed-side and ambient length sets
have the same attained greatest element. In particular, neither set is empty. -/
theorem rightSideLdpLengths_greatest (q : RightDomain) (j m : ℕ) (hjm : j ≤ m) :
    ∃ n : ℕ, IsGreatest (rightSideLdpLengths q j m) n ∧
      IsGreatest (pathLengths (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩) n ∧
      ldpSup (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩ = (n : WithBot ℕ) := by
  have H := boundary_path q j (m - j)
  rw [Nat.add_sub_of_le hjm] at H
  obtain ⟨p, _⟩ := H
  have hb := presentPathLengthsBounded_of_hfin (W q) (HF q)
  obtain ⟨r, hr⟩ := exists_isLongest_of_bddAbove (hb _ _ p.reachable) p.reachable
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
  obtain ⟨s, hlen, hs⟩ := rightSide_path_dominance q r hroot hur hvr
  have heq : s.length = r.length := Nat.le_antisymm (hr s) hlen
  have hg : IsGreatest (pathLengths (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩)
      r.length := ⟨⟨r, rfl⟩, fun _ ⟨t, ht⟩ => ht ▸ hr t⟩
  refine ⟨r.length, ⟨⟨s, heq, hs⟩, ?_⟩, hg, sup_eq_of_greatest hg⟩
  rintro n ⟨t, ht, _⟩
  exact ht ▸ hr t

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

private theorem stageLdpCode_eventually_of_greatest (ω : ℕ → Fin 3)
    {a b : PresentVertex (fun i => ω (i + 1))} {n : ℕ}
    (hg : IsGreatest (pathLengths a b) n) :
    ∀ᶠ s in atTop, busemannStageLdpCode ω s a.id b.id = (n : ℤ) := by
  obtain ⟨p, hp⟩ := hg.1
  obtain ⟨N, hN⟩ := path_in_late_stages p
  refine eventually_atTop.mpr ⟨N, fun s hs => ?_⟩
  obtain ⟨r, hr⟩ := hN s hs
  have hsg : IsGreatest
      (pathLengths (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) s) ⟨b.id⟩) n := by
    refine ⟨⟨r, hr.trans hp⟩, ?_⟩
    rintro k ⟨t, ht⟩
    have hlength := stageToLimit_length (fun i => ω (i + 1)) s t
    exact hg.2 ⟨(stageToLimit (fun i => ω (i + 1)) s).mapPath t,
      hlength.trans ht⟩
  unfold busemannStageLdpCode
  rw [sup_eq_of_greatest hsg]
  rfl

private theorem boundaryLdpDifference_of_greatest (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (j m nj n0 : ℕ)
    (hj : IsGreatest (pathLengths (boundaryPresentVertex _ h (j : ℤ))
      (boundaryPresentVertex _ h (m : ℤ))) nj)
    (h0 : IsGreatest (pathLengths (boundaryPresentVertex _ h 0)
      (boundaryPresentVertex _ h (m : ℤ))) n0) :
    boundaryLdpDifference ω (j : ℤ) m = (nj : ℤ) - (n0 : ℤ) := by
  unfold boundaryLdpDifference
  simp only [rightHat_boundaryIdTotal_eq ω h]
  apply eventualIntValue_eq
  filter_upwards [stageLdpCode_eventually_of_greatest ω hj,
    stageLdpCode_eventually_of_greatest ω h0] with s hj h0
  exact congrArg₂ (· - ·) hj h0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw finite LDP values are attained inside the closed right side for every
sufficiently late boundary target, and their finite difference is the stage representative. -/
theorem rightClosedSideLdpLocalization_proved : RightClosedSideLdpLocalization := by
  filter_upwards [rightHatThinBoundaryIdentification_proved] with ω hω
  obtain ⟨h, q, hq, hw, hboundary⟩ := hω
  let w := fun i => ω (i + 1)
  refine ⟨h, q, hq, hw, hboundary, ?_⟩
  intro j
  refine eventually_atTop.mpr ⟨j, fun m hjm => ?_⟩
  obtain ⟨nj, hsj, hgj, _⟩ := rightSideLdpLengths_greatest q j m hjm
  obtain ⟨n0, hs0, hg0, _⟩ := rightSideLdpLengths_greatest q 0 m (Nat.zero_le m)
  have hlengths (i : ℕ) :
      pathLengths (⟨RB q i⟩ : PresentVertex (W q)) ⟨RB q m⟩ =
        pathLengths (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (i : ℤ))
          (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) := by
    have hh := rightHatPathLengthIdentification_proved w h ⟨RB q i⟩ ⟨RB q m⟩
    have H : ∀ u : ℕ → Fin 3, u = hatCodes w h →
        pathLengths (⟨RB q i⟩ : PresentVertex u) ⟨RB q m⟩ =
          pathLengths (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (i : ℤ))
            (boundaryPresentVertex w (hatBoundaryHitWitnesses w h) (m : ℤ)) := by
      intro u hu
      subst u
      rw [hboundary i, hboundary m] at hh
      exact hh
    exact H (W q) hw
  rw [hlengths j] at hgj
  rw [hlengths 0, Nat.cast_zero] at hg0
  exact ⟨nj, n0, hsj, hs0, sup_eq_of_greatest hgj, sup_eq_of_greatest hg0,
    boundaryLdpDifference_of_greatest ω (hatBoundaryHitWitnesses w h) j m nj n0 hgj hg0⟩

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
Every closed-right-side path to the m-th boundary vertex already belongs to the
finite geometric ancestor restriction at level m, retaining each individual edge ID. -/
theorem rightSide_path_mem_ancestorEdges (q : RightDomain) (m : ℕ)
    {u : PresentVertex (W q)} (p : Path u ⟨RB q m⟩)
    (hp : ∀ e ∈ pathEdgeList p, e ∈ SE q .right) :
    ∀ e ∈ pathEdgeList p,
      e ∈ sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right m :=
  sidePath_ancestorEdges q m p hp .refl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Side path lengths agree exactly with lengths in each sufficiently large finite
geometric ancestor restriction. This does not identify that restriction with the code. -/
theorem rightSideLdpLengths_eq_ancestorLengths (q : RightDomain) (j m s : ℕ)
    (hms : m ≤ s) :
    rightSideLdpLengths q j m =
      {n | ∃ p : Path (⟨RB q j⟩ : PresentVertex (W q)) ⟨RB q m⟩,
        p.length = n ∧ ∀ e ∈ pathEdgeList p,
          e ∈ sourceAncestorEdges
            (W q) (HF q) (HL q) (HT q) (HR q) (P q) .right s} := by
  ext n
  constructor
  · rintro ⟨p, hp, hs⟩
    refine ⟨p, hp, fun e he => ?_⟩
    exact sourceAncestorEdges_mono (W q) (HF q) (HL q) (HT q) (HR q) (P q)
      .right hms (rightSide_path_mem_ancestorEdges q m p hs e he)
  · rintro ⟨p, hp, hs⟩
    exact ⟨p, hp, fun e he => (hs e he).1⟩

/- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Open finite-code obligation: equal right thin truncations at a level beyond both
endpoints determine the same difference of the two attained natural LDP maxima.
Only ordered endpoints occur, so the nonemptiness and attainment were proved above. -/
@[expose] def RightTruncationLdpDifferenceDetermination : Prop :=
  ∀ (q q' : RightDomain) (j m s : ℕ), j ≤ m → m ≤ s →
    thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime .right q.1 s =
      thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime .right q'.1 s →
    ((sSup (rightSideLdpLengths q j m) : ℕ) : ℤ) -
        ((sSup (rightSideLdpLengths q 0 m) : ℕ) : ℤ) =
      ((sSup (rightSideLdpLengths q' j m) : ℕ) : ℤ) -
        ((sSup (rightSideLdpLengths q' 0 m) : ℕ) : ℤ)

end DirectedDistances.Recursive
