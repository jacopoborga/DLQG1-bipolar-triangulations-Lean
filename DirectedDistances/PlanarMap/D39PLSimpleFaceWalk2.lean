/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLSimpleFaceWalk
import DirectedDistances.PlanarMap.D39PLSegmentSeparation

/-! # Point occurrences in simple face walks

to the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

namespace Polyline




theorem point_boundaryConcat_decomposition (p q : Polyline)
    (hjoin : p.finish = q.start) (i : ℕ)
    (hi : i < (boundaryConcat p q).points.length - 1) :
    (i < p.points.length - 1 ∧ (boundaryConcat p q).point i = p.point i) ∨
    ∃ a : ℕ, a < q.points.length - 1 ∧
      i = p.points.length - 1 + a ∧ (boundaryConcat p q).point i = q.point a := by
  by_cases hp : i < p.points.length - 1
  · exact Or.inl ⟨hp, point_boundaryConcat_left p q i (by omega)⟩
  · have hplen : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    have hqlen : 0 < q.points.length := List.length_pos_iff.mpr q.nonempty
    rw [length_boundaryConcat] at hi
    let a := i - (p.points.length - 1)
    have ha : a < q.points.length - 1 := by dsimp [a]; omega
    have hia : i = p.points.length - 1 + a := by dsimp [a]; omega
    exact Or.inr ⟨a, ha, hia, hia ▸ point_boundaryConcat_right p q hjoin a (by omega)⟩

end Polyline

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the point offset of a dart occurrence
is the number of segments preceding it in the concatenated face walk. -/
@[expose] def faceWalkPointOffset {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (k : ℕ) : ℕ :=
  if k = 0 then 0 else (faceWalkPolyline B vert P d (k - 1)).points.length - 1

/-- Helper toward Proposition 5.16: every point before the final point of a
face walk retains a dart occurrence and an index before that arc's final point,
as well as the exact offset recovering its index in the whole walk. -/
theorem faceWalkPolyline_point_occurrence {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) (n : ℕ) :
    ∀ i : ℕ, i < (faceWalkPolyline B vert P d n).points.length - 1 →
      ∃ k a : ℕ, k ≤ n ∧
        a < (P.arc ((B.map.faceSucc : B.D → B.D)^[k] d)).points.length - 1 ∧
        i = faceWalkPointOffset B vert P d k + a ∧
        (faceWalkPolyline B vert P d n).point i =
          (P.arc ((B.map.faceSucc : B.D → B.D)^[k] d)).point a := by
  induction n with
  | zero =>
      intro i hi
      exact ⟨0, i, le_rfl, hi, by simp [faceWalkPointOffset], rfl⟩
  | succ n ih =>
      intro i hi
      obtain hleft | ⟨a, ha, hia, hpoint⟩ :=
        Polyline.point_boundaryConcat_decomposition
          (faceWalkPolyline B vert P d n)
          (P.arc ((B.map.faceSucc : B.D → B.D)^[n + 1] d))
          (finish_faceWalkPolyline_eq_next_start B vert P d n) i hi
      · obtain ⟨k, a, hk, ha, hia, hpoint⟩ := ih i hleft.1
        exact ⟨k, a, by omega, ha, hia, hleft.2.trans hpoint⟩
      · refine ⟨n + 1, a, le_rfl, ha, ?_, hpoint⟩
        simpa only [faceWalkPointOffset, Nat.add_eq_zero_iff,
          Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] using hia

end D39FiniteBall

namespace PLDrawing

/-- Helper toward Proposition 5.16: a bend strictly between the endpoints
of a simple dart arc belongs to the geometric interior of that arc. -/
theorem arc_point_mem_interior {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (d : D) (a : ℕ) (ha0 : 0 < a) (ha : a < (P.arc d).points.length - 1) :
    (P.arc d).point a ∈ (P.arc d).interior := by
  refine ⟨(P.arc d).point_mem_image (by omega), ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  rw [P.arc_start, P.arc_finish]
  exact ⟨P.bend_not_vertex d a ha0 (by omega) _,
    P.bend_not_vertex d a ha0 (by omega) _⟩

/-- Helper toward Proposition 5.16: half-open point lists of two different,
non-reversed dart arcs with different initial vertices are disjoint. -/
theorem arc_points_ne_of_initialVertex_ne {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (d e : D) (hv : vert d ≠ vert e) (hflip : e ≠ flip d)
    (a b : ℕ) (ha : a < (P.arc d).points.length - 1)
    (hb : b < (P.arc e).points.length - 1) :
    (P.arc d).point a ≠ (P.arc e).point b := by
  intro heq
  by_cases ha0 : a = 0
  · subst a
    rw [Polyline.point_zero_eq_start, P.arc_start] at heq
    by_cases hb0 : b = 0
    · subst b
      rw [Polyline.point_zero_eq_start, P.arc_start] at heq
      exact hv (P.pos_injective heq)
    · exact P.bend_not_vertex e b (by omega) (by omega) _ heq.symm
  · by_cases hb0 : b = 0
    · subst b
      rw [Polyline.point_zero_eq_start, P.arc_start] at heq
      exact P.bend_not_vertex d a (by omega) (by omega) _ heq
    · have hed : e ≠ d := fun h => hv (congrArg vert h.symm)
      exact Set.disjoint_left.mp (P.interior_disjoint d e hed hflip)
        (P.arc_point_mem_interior d a (by omega) ha)
        (heq.symm ▸ P.arc_point_mem_interior e b (by omega) hb)

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: distinct initial vertices and absence of
oppositely oriented occurrences imply injectivity of all walk points before
the final point. The hypotheses concern precisely the `n + 1` dart occurrences. -/
theorem faceWalkPolyline_points_injective_of_initialVertices {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) (n : ℕ)
    (hvertices : ∀ k l : ℕ, k ≤ n → l ≤ n → k ≠ l →
      vert ((B.map.faceSucc : B.D → B.D)^[k] d) ≠
        vert ((B.map.faceSucc : B.D → B.D)^[l] d))
    (hflip : ∀ k l : ℕ, k ≤ n → l ≤ n →
      (B.map.faceSucc : B.D → B.D)^[l] d ≠
        B.map.edgeInv ((B.map.faceSucc : B.D → B.D)^[k] d)) :
    ∀ i j : ℕ,
      i < (faceWalkPolyline B vert P d n).points.length - 1 →
      j < (faceWalkPolyline B vert P d n).points.length - 1 →
      (faceWalkPolyline B vert P d n).point i =
        (faceWalkPolyline B vert P d n).point j → i = j := by
  intro i j hi hj heq
  obtain ⟨k, a, hk, ha, hia, hpa⟩ :=
    B.faceWalkPolyline_point_occurrence vert P d n i hi
  obtain ⟨l, b, hl, hb, hjb, hpb⟩ :=
    B.faceWalkPolyline_point_occurrence vert P d n j hj
  have hab := hpa.symm.trans (heq.trans hpb)
  by_cases hkl : k = l
  · subst l
    have hab' : a = b := by
      by_contra hne
      exact PLDrawing.point_injective_of_isSimple _ (P.arc_simple _)
        (by omega) (by omega) hne hab
    omega
  · exact (P.arc_points_ne_of_initialVertex_ne _ _
      (hvertices k l hk hl hkl) (hflip k l hk hl) a b ha hb hab).elim

/-- Helper toward Proposition 5.16: a face successor starts at the terminal
vertex of the preceding dart, including for missing geometric edges. -/
theorem faceSucc_initialVertex {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (e : B.D) : vert (B.map.faceSucc e) = vert (B.map.edgeInv e) := by
  apply P.pos_injective
  simpa only [P.arc_start, P.arc_finish] using (arc_finish_faceSucc B vert P e).symm

/-- Helper toward Proposition 5.16: when the initial vertices of a full
face walk are distinct and its period is at least three, it contains no dart
together with its reverse. Such a pair would force a two-step vertex cycle. -/
theorem faceWalk_fullPeriod_no_flip_of_initialVertices {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D)
    (hperiod : 3 ≤ Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d)
    (hinj : ∀ k l : ℕ,
      k < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d →
      l < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d →
      vert ((B.map.faceSucc : B.D → B.D)^[k] d) =
        vert ((B.map.faceSucc : B.D → B.D)^[l] d) → k = l) :
    ∀ k l : ℕ,
      k < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d →
      l < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d →
      (B.map.faceSucc : B.D → B.D)^[l] d ≠
        B.map.edgeInv ((B.map.faceSucc : B.D → B.D)^[k] d) := by
  let f : B.D → B.D := B.map.faceSucc
  let m := Function.minimalPeriod f d
  let s : ℕ → ℕ := fun k => if k + 1 < m then k + 1 else 0
  have hslt (k : ℕ) (hk : k < m) : s k < m := by
    dsimp [s]
    split_ifs <;> omega
  have hnext (k : ℕ) (hk : k < m) :
      vert (f^[s k] d) = vert (B.map.edgeInv (f^[k] d)) := by
    have hv := B.faceSucc_initialVertex vert P (f^[k] d)
    change vert (f (f^[k] d)) = vert (B.map.edgeInv (f^[k] d)) at hv
    by_cases h : k + 1 < m
    · simpa only [s, ite_eq_left h, Function.iterate_succ_apply'] using hv
    · have hkm : k + 1 = m := by omega
      have hclose : f (f^[k] d) = d := by
        calc
          f (f^[k] d) = f^[k + 1] d := (Function.iterate_succ_apply' f k d).symm
          _ = f^[m] d := by rw [hkm]
          _ = d := Function.iterate_minimalPeriod
      simpa only [s, ite_eq_right h, Function.iterate_zero_apply, hclose] using hv
  intro k l hk hl hflip
  have h1 : s k = l := hinj _ _ (hslt k hk) hl
    ((hnext k hk).trans (congrArg vert hflip).symm)
  have h2 : s l = k := hinj _ _ (hslt l hl) hk (by
    rw [hnext l hl, hflip, P.flip_involutive])
  change 3 ≤ m at hperiod
  change k < m at hk
  change l < m at hl
  dsimp [s] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- Helper toward Proposition 5.16: under no cut vertices, vertices of the
full walk polyline are injective except for its closing point. -/
theorem faceWalkPolyline_points_injective_of_noCutVertex {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hnocut : ∀ v, ¬ B.map.isCutVertex v) (d : B.D)
    (hperiod : 3 ≤ Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d) :
    ∀ a b : ℕ,
      a < (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).points.length - 1 →
      b < (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).points.length - 1 →
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).point a =
        (faceWalkPolyline B vert P d
          (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).point b →
      a = b := by
  have hdistinct := B.faceWalk_iterate_initialVertex_injective_of_noCutVertex vert P hnocut d
  have hinj : ∀ k l : ℕ,
      k < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d →
      l < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d →
      vert ((B.map.faceSucc : B.D → B.D)^[k] d) =
        vert ((B.map.faceSucc : B.D → B.D)^[l] d) → k = l := by
    intro k l hk hl heq
    rcases lt_trichotomy k l with hlt | hequal | hgt
    · exact (hdistinct k l hlt hl heq).elim
    · exact hequal
    · exact (hdistinct l k hgt hk heq.symm).elim
  apply B.faceWalkPolyline_points_injective_of_initialVertices vert P d
  · intro k l hk hl hne heq
    exact hne (hinj k l (by omega) (by omega) heq)
  · intro k l hk hl
    exact B.faceWalk_fullPeriod_no_flip_of_initialVertices vert P d hperiod hinj
      k l (by omega) (by omega)

/-- Helper toward Proposition 5.16: a no-cut full-period face walk with at
least three darts is cyclically simple. -/
theorem faceWalkPolyline_fullPeriod_isCyclicSimple_of_noCutVertex {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hnocut : ∀ v, ¬ B.map.isCutVertex v) (d : B.D)
    (hperiod : 3 ≤ Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d) :
    (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).start =
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).finish ∧
    (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple := by
  let n := Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1
  let c := faceWalkPolyline B vert P d n
  have hlen : 4 ≤ c.points.length :=
    B.faceWalkPolyline_fullPeriod_points_length_ge_four vert P d hperiod
  have hclosed : c.start = c.finish := B.faceWalkPolyline_fullPeriod_closed vert P d
  have hinj := B.faceWalkPolyline_points_injective_of_noCutVertex vert P hnocut d hperiod
  have hfull : c.intervalPolyline 0 (c.points.length - 1) = c := by
    have hext (p q : Polyline) (h : p.points = q.points) : p = q := by
      cases p with
      | mk ps hps =>
          cases q with
          | mk qs hqs =>
              change ps = qs at h
              cases h
              rfl
    apply hext
    have hpoints : (c.intervalPolyline 0 (c.points.length - 1)).points = c.points := by
      apply List.ext_getElem
      · rw [Polyline.length_intervalPolyline]
        omega
      · intro i hi hj
        have heq := Polyline.point_intervalPolyline c 0 (c.points.length - 1) i (by omega)
        simpa only [Nat.zero_add, Polyline.point, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hj, Option.getD_some] using heq
    exact hpoints
  refine ⟨hclosed, ?_⟩
  have hs := B.intervalPolyline_isCyclicSimple_of_faceWalk vert P d n 0
    (c.points.length - 1) (by change 0 + (c.points.length - 1) < c.points.length; omega)
    (by change 4 ≤ (c.intervalPolyline 0 (c.points.length - 1)).points.length; rwa [hfull])
    (by change (c.intervalPolyline 0 (c.points.length - 1)).start =
          (c.intervalPolyline 0 (c.points.length - 1)).finish; rwa [hfull])
    (by change ∀ a b : ℕ,
          a < (c.intervalPolyline 0 (c.points.length - 1)).points.length - 1 →
          b < (c.intervalPolyline 0 (c.points.length - 1)).points.length - 1 →
          (c.intervalPolyline 0 (c.points.length - 1)).point a =
            (c.intervalPolyline 0 (c.points.length - 1)).point b → a = b
        rwa [hfull])
  change (c.intervalPolyline 0 (c.points.length - 1)).IsCyclicSimple at hs
  rwa [hfull] at hs

/-- Helper toward Proposition 5.16: every no-cut face-successor orbit with
at least three darts has a closed cyclically simple walk tracing its entire
PL boundary. -/
theorem exists_cyclicSimple_plOrbitBoundary_of_noCutVertex {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hnocut : ∀ v, ¬ B.map.isCutVertex v)
    (O : D39BallFaceCycleOrbit B) (d : B.D) (hd : d ∈ O.val)
    (hperiod : 3 ≤ Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d) :
    ∃ q : Polyline, q.start = q.finish ∧ q.IsCyclicSimple ∧
      q.image = B.plOrbitBoundary vert P O := by
  obtain ⟨hclosed, hsimple⟩ :=
    B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_noCutVertex vert P hnocut d hperiod
  exact ⟨_, hclosed, hsimple, B.faceWalkPolyline_image_eq_plOrbitBoundary vert P O d hd⟩

end D39FiniteBall

end DirectedDistances.PlanarMap

end
