/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRootStar

/-! Helper toward Lemma 5.5: old incoming darts at the stopped boundary root. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: every west endpoint has already been an active
initial vertex, or is the fresh vertex of an up step. The latter possibility
is needed for missing geometric edges and is not a directed-edge assertion. -/
theorem lPlus_stage_west_endpoint_history (w : ℕ → Fin 3) (n : ℕ)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    (∃ j ≤ n, edgeWest w e = activeInitial w j) ∨
      (∃ j < n, w j = 1 ∧ edgeWest w e = (kmswStage w j).nextVertex) := by
  induction n with
  | zero =>
    have he0 : e = 0 := by change e < 1 at he; omega
    subst e
    exact Or.inl ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    by_cases hold : e < (kmswStage w n).nextEdge
    · rcases ih hold with ⟨j, hj, hv⟩ | ⟨j, hj, hc, hv⟩
      · exact Or.inl ⟨j, by omega, hv⟩
      · exact Or.inr ⟨j, by omega, hc, hv⟩
    · let s := kmswStage w n
      have hnew : s.nextEdge ≤ e := by dsimp [s]; omega
      have hend := (edge_endpoints_eq w he).1.symm
      have hact := CutConverse.activeInitial_eq w (n + 1)
      change activeInitial w (n + 1) =
        (kmswStep s (w n)).west (kmswStep s (w n)).active at hact
      change edgeWest w e = (kmswStep s (w n)).west e at hend
      change e < (kmswStep s (w n)).nextEdge at he
      by_cases hc0 : w n = 0
      · cases hs : s.UL.dropLast.reverse with
        | nil =>
          have hid : e = s.nextEdge ∨ e = s.nextEdge + 1 := by
            simp only [kmswStep, kmswCodeStep, hc0, ↓reduceIte,
              kmswStepOfStep, hs, State.addEdge] at he
            omega
          apply Or.inl
          refine ⟨n + 1, le_rfl, ?_⟩
          rcases hid with rfl | rfl <;>
            simp [kmswStep, kmswCodeStep, hc0, kmswStepOfStep, hs,
              State.addEdge] at hend hact <;>
            exact hend.trans hact.symm
        | cons a as =>
          have hid : e = s.nextEdge := by
            simp only [kmswStep, kmswCodeStep, hc0, ↓reduceIte,
              kmswStepOfStep, hs, State.addEdge] at he
            omega
          subst e
          exact Or.inl ⟨n + 1, le_rfl, by
            simp [kmswStep, kmswCodeStep, hc0, kmswStepOfStep, hs,
              State.addEdge] at hend hact
            exact hend.trans hact.symm⟩
      · by_cases hc1 : w n = 1
        · have hid : e = s.nextEdge ∨ e = s.nextEdge + 1 := by
            simp [kmswStep, kmswCodeStep, hc1, kmswStepOfStep, State.addEdge] at he
            omega
          rcases hid with rfl | rfl
          · exact Or.inl ⟨n + 1, le_rfl, by
              simp [kmswStep, kmswCodeStep, hc1, kmswStepOfStep,
                State.addEdge] at hend hact
              exact hend.trans hact.symm⟩
          · exact Or.inr ⟨n, Nat.lt_succ_self n, hc1, by
              simpa [kmswStep, kmswCodeStep, hc1, kmswStepOfStep,
                State.addEdge] using hend⟩
        · have hc2 : w n = 2 := by
            apply Fin.ext
            have hb := (w n).isLt
            have h0 : (w n).val ≠ 0 := by intro h; exact hc0 (Fin.ext h)
            have h1 : (w n).val ≠ 1 := by intro h; exact hc1 (Fin.ext h)
            omega
          cases hs : s.UR with
          | nil =>
            have hid : e = s.nextEdge := by
              simp [kmswStep, kmswCodeStep, hc2, kmswStepOfStep, hs,
                State.addEdge] at he
              omega
            subst e
            exact Or.inl ⟨n + 1, le_rfl, by
              simp [kmswStep, kmswCodeStep, hc2, kmswStepOfStep, hs,
                State.addEdge] at hend hact
              exact hend.trans hact.symm⟩
          | cons a as =>
            simp [kmswStep, kmswCodeStep, hc2, kmswStepOfStep, hs] at he
            omega

/-- Helper toward Lemma 5.5: a geometric edge allocated strictly before a
positive boundary hit cannot have that boundary vertex as its west endpoint.
This includes missing edges; no directedness premise is imposed. -/
theorem lPlus_before_hit_west_ne_boundary_root
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 0 < k)
    (n : ℕ) (hn : n < boundaryHitTime w h k)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    edgeWest w e ≠ boundaryVertex w h k := by
  intro hv
  rcases lPlus_stage_west_endpoint_history w n e he with
    ⟨j, hj, hjv⟩ | ⟨j, _, hc, hjv⟩
  · exact boundaryVertex_first_visit_right w h (by omega) j (by omega)
      (hv.symm.trans hjv)
  · obtain ⟨N, hN, hLR⟩ := boundaryVertex_right_edge w h (by omega : 1 ≤ k)
    have hb := hLR N le_rfl
    have hroot : edgeWest w (act w (boundaryHitTime w h k)) =
        boundaryVertex w h k :=
      (edge_endpoints_eq w (act_lt_nextEdge w hN)).1.symm.trans hb.2.2.1
    exact (CutConverse.up_vertex_ne_LR_endpoints w hc N
      (act w (boundaryHitTime w h k)) hb.1).1
        (hjv.symm.trans (hv.trans hroot.symm))

/-- Helper toward Lemma 5.5: the old-incoming root class consists of east
darts of geometric edges already allocated at a stage strictly before the
root first becomes active, with east endpoint equal to that root. Edge IDs
and missing edges are retained. This is allocation/incidence data, not an
assumed classification, rotation, or return property. -/
@[expose] def LPlusOldIncomingRootDart (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) (d : ℕ × Bool) : Prop :=
  d.2 = true ∧ ∃ n < boundaryHitTime w h k,
    d.1 < (kmswStage w n).nextEdge ∧
      (kmswStage w n).east d.1 = boundaryVertex w h k

/-- Helper toward Lemma 5.5: the allocation-based old-incoming class has
exactly the prescribed endpoint, in the limit dart convention. -/
theorem lPlusOldIncomingRootDart_vertex
    {w : ℕ → Fin 3} {h : BoundaryHitWitnesses w} {k : ℤ}
    {d : ℕ × Bool} (hd : LPlusOldIncomingRootDart w h k d) :
    kmswLimitDartVertex w d = boundaryVertex w h k := by
  obtain ⟨hb, n, _, he, hv⟩ := hd
  simp only [kmswLimitDartVertex, hb, ↓reduceIte]
  exact (edge_endpoints_eq w he).2.symm.trans hv

/-- Helper toward Lemma 5.5: every prefix dart incident to a nonnegative
boundary root is old incoming. At index zero the prefix is empty. At a
positive index the result follows from the stage induction, the first-visit
property, and exclusion of up-created vertices from the lower-right boundary. -/
theorem lPlusPrefixDart_initial_vertex_old_incoming
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} (hk : 0 ≤ k) (d : LPlusPrefixDart W h k)
    (hd : kmswLimitDartVertex (shiftedStream W 0) d.val =
      boundaryVertex (shiftedStream W 0) h k) :
    LPlusOldIncomingRootDart (shiftedStream W 0) h k d.val := by
  by_cases hkpos : 0 < k
  · obtain ⟨m, hm, _, _⟩ := lPlus_positive_hit_fresh (shiftedStream W 0) h hkpos
    have he : d.val.1 < (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge :=
      (Set.ext_iff.mp (lPlusPrefixMinusEdges_eq_previousStage hkpos) d.val.1).mp
        d.property
    rw [hm] at he
    simp only [Nat.add_sub_cancel] at he
    have hb : d.val.2 = true := by
      cases hb : d.val.2 with
      | false =>
        have hv : edgeWest (shiftedStream W 0) d.val.1 =
            boundaryVertex (shiftedStream W 0) h k := by
          simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte] using hd
        exact False.elim (lPlus_before_hit_west_ne_boundary_root
          (shiftedStream W 0) h hkpos m (by omega) d.val.1 he hv)
      | true => rfl
    refine ⟨hb, m, by omega, he, ?_⟩
    have hv : edgeEast (shiftedStream W 0) d.val.1 =
        boundaryVertex (shiftedStream W 0) h k := by
      simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using hd
    exact (edge_endpoints_eq (shiftedStream W 0) he).2.trans hv
  · have hk0 : k = 0 := by omega
    subst k
    have he : d.val.1 ∈ (∅ : Set ℕ) :=
      (Set.ext_iff.mp (lPlusPrefixMinusEdges_zero (W := W) (h := h)) d.val.1).mp
        d.property
    exact False.elim he

/-- Helper toward Lemma 5.5: exact incidence characterization of the new
class on the prefix carrier. The allocation witness is proved, not assumed. -/
theorem lPlusPrefixDart_initial_vertex_iff_old_incoming
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} (hk : 0 ≤ k) (d : LPlusPrefixDart W h k) :
    kmswLimitDartVertex (shiftedStream W 0) d.val =
        boundaryVertex (shiftedStream W 0) h k ↔
      LPlusOldIncomingRootDart (shiftedStream W 0) h k d.val :=
  ⟨lPlusPrefixDart_initial_vertex_old_incoming hk d,
    lPlusOldIncomingRootDart_vertex⟩

/-- Helper toward Lemma 5.5: corrected root-star classification. The three
alternatives need not be disjoint: old incoming includes attachment east
darts and the initial east port when these are based at this root. -/
theorem lPlusPrefixDart_initial_vertex_attachment_or_old_incoming
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} (hk : 0 ≤ k) (d : LPlusPrefixDart W h k)
    (hd : kmswLimitDartVertex (shiftedStream W 0) d.val =
      boundaryVertex (shiftedStream W 0) h k) :
    (∃ i : Fin (List.reverse (List.dropLast (State.UL
        (kmswStage (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h k))))).length,
      ∃ b : Bool, d.val =
        ((List.reverse (List.dropLast (State.UL
          (kmswStage (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h k)))))[i.val], b)) ∨
      d.val = (0, true) ∨
      LPlusOldIncomingRootDart (shiftedStream W 0) h k d.val :=
  Or.inr (Or.inr (lPlusPrefixDart_initial_vertex_old_incoming hk d hd))

/-- Helper toward Lemma 5.5: the recorded left/left/down counterexample is
in the new allocation-based old-incoming class. Its failure to belong to the
two old alternatives remains certified by the imported obstruction theorem. -/
theorem lPlusRootStar_left_left_down_old_incoming
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    (hc₀ : shiftedStream W 0 0 = 0) (hc₁ : shiftedStream W 0 1 = 0)
    (hc₂ : shiftedStream W 0 2 = 2) :
    ∃ d : LPlusPrefixDart W h 1, d.val = (1, true) ∧
      LPlusOldIncomingRootDart (shiftedStream W 0) h 1 d.val := by
  obtain ⟨d, hd, hv, _⟩ :=
    lPlusRootStar_left_left_down_obstruction (h := h) hc₀ hc₁ hc₂
  exact ⟨d, hd, lPlusPrefixDart_initial_vertex_old_incoming (by omega) d hv⟩















































/- Validation: the temporary in-file axiom probes for all seven theorems
and the old-incoming class definition reported exactly propext,
were removed before final compilation. The import check exited 0. Three
development checks exited 1 (endpoint simplification, tactic layout, and
dependent subtype rewriting) and were corrected; subsequent development -/

end DirectedDistances.PaperProofs.Section5
