/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedEquiv





public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open scoped ENNReal Topology

universe uV uE uV' uE'

/-- Helper toward Definition 3.8: the root vertex of an ordered geometric dart.
The Boolean records whether the dart follows the stored `src` to `tgt` order. -/
@[expose] def d39GeomRootVertex {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) : V :=
  if rho.2 then M.toPlaneMapWithMissing.src rho.1
  else M.toPlaneMapWithMissing.tgt rho.1

/-- Helper toward Definition 3.8: the other endpoint of an ordered root dart. -/
@[expose] def d39GeomRootOtherVertex {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) : V :=
  if rho.2 then M.toPlaneMapWithMissing.tgt rho.1
  else M.toPlaneMapWithMissing.src rho.1

/-- Helper toward Definition 3.8: undirected adjacency using every geometric
edge, including edges tagged missing. Parallel edge identities are retained by
`ballEdges`; adjacency intentionally records only existence of a traversable
edge, as required for graph distance. -/
@[expose] def d39GeomAdj {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (v w : V) : Prop :=
  v ≠ w ∧ ∃ e : E,
    (M.toPlaneMapWithMissing.src e = v ∧ M.toPlaneMapWithMissing.tgt e = w) ∨
    (M.toPlaneMapWithMissing.src e = w ∧ M.toPlaneMapWithMissing.tgt e = v)

/-- Helper toward Definition 3.8: the simple graph for undirected distance,
with all geometric edges traversable. -/
@[expose] def d39GeomGraph {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) : SimpleGraph V where
  Adj := d39GeomAdj M
  symm := ⟨by
    intro v w h
    rcases h with ⟨hne, e, h | h⟩
    · exact ⟨hne.symm, e, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨hne.symm, e, Or.inl ⟨h.1, h.2⟩⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

/-- Helper toward Definition 3.8: the directed graph distance measured after
forgetting orientations and missing-edge tags, while retaining all geometric
edge identities in the ball data. Unreachable pairs have distance `⊤` through
`SimpleGraph.edist`. -/
@[expose] def d39GeomGraphDistance {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (v w : V) : ℕ∞ :=
  (d39GeomGraph M).edist v w

/-- Helper toward Definition 3.8: vertices within undirected geometric graph
distance at most `r` from the first endpoint of the ordered root dart. -/
@[expose] def d39GeomBallVertices {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) : Set V :=
  {v | d39GeomGraphDistance M (d39GeomRootVertex M rho) v ≤ (r : ℕ∞)}

/-- Helper toward Definition 3.8: all geometric edge identities whose two
endpoints lie in the vertex ball. Missing tags and present orientations are
retained by the edge identity and map data. -/
@[expose] def d39GeomBallEdges {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) : Set E :=
  {e | M.toPlaneMapWithMissing.src e ∈ d39GeomBallVertices M rho r ∧
       M.toPlaneMapWithMissing.tgt e ∈ d39GeomBallVertices M rho r}

/-- Helper toward Definition 3.8: original faces whose boundary vertices, read
as vertices with positions in the closure of the face, all lie in the vertex
ball. -/
@[expose] def d39GeomRetainedFaces {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) :
    Set (M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :=
  {F | ∀ v, M.toPlaneMapWithMissing.pos v ∈ closure F.val →
      v ∈ d39GeomBallVertices M rho r}

/-- Helper toward Definition 3.8: a homeomorphism realization of an
isomorphism between positive-radius geometric balls. It preserves the plane
orientation, all ball vertices and edge identities, incidence, missing tags,
present orientations, the ordered root mark, and every retained original face. -/
structure D39GeomBallIso {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'} (r : ℕ)
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) where
  radius_pos : 0 < r
  h : ℂ ≃ₜ ℂ
  orientationPreserving : OrientationPreserving h
  vertexEquiv : {v // v ∈ d39GeomBallVertices M rho r} ≃
    {v // v ∈ d39GeomBallVertices M' rho' r}
  edgeEquiv : {e // e ∈ d39GeomBallEdges M rho r} ≃
    {e // e ∈ d39GeomBallEdges M' rho' r}
  faceEquiv : {F // F ∈ d39GeomRetainedFaces M rho r} ≃
    {F // F ∈ d39GeomRetainedFaces M' rho' r}
  pos_map : ∀ v, h (M.toPlaneMapWithMissing.pos v.1) =
    M'.toPlaneMapWithMissing.pos (vertexEquiv v).1
  arc_range_map : ∀ e,
    h '' Set.range (M.toPlaneMapWithMissing.arc e.1) =
      Set.range (M'.toPlaneMapWithMissing.arc (edgeEquiv e).1)
  src_map : ∀ e,
    (vertexEquiv (⟨M.toPlaneMapWithMissing.src e.1,
      e.2.1⟩ : {v // v ∈ d39GeomBallVertices M rho r})).1 =
      M'.toPlaneMapWithMissing.src (edgeEquiv e).1
  tgt_map : ∀ e,
    (vertexEquiv (⟨M.toPlaneMapWithMissing.tgt e.1,
      e.2.2⟩ : {v // v ∈ d39GeomBallVertices M rho r})).1 =
      M'.toPlaneMapWithMissing.tgt (edgeEquiv e).1
  missing_map : ∀ e,
    M'.toPlaneMapWithMissing.missing (edgeEquiv e).1 ↔
      M.toPlaneMapWithMissing.missing e.1
  orientation_map : ∀ e (he : ¬ M.toPlaneMapWithMissing.missing e.1),
    M'.forward ⟨(edgeEquiv e).1,
      by simpa [missing_map e] using he⟩ =
    M.forward ⟨e.1, he⟩
  root_edge_map :
      (edgeEquiv (⟨rho.1, by
      have hroot : d39GeomRootVertex M rho ∈ d39GeomBallVertices M rho r := by
        simp [d39GeomBallVertices, d39GeomGraphDistance]
      have hother : d39GeomRootOtherVertex M rho ∈ d39GeomBallVertices M rho r := by
        by_cases heq : d39GeomRootVertex M rho = d39GeomRootOtherVertex M rho
        · simpa [heq] using hroot
        · have hadj : (d39GeomGraph M).Adj
              (d39GeomRootVertex M rho) (d39GeomRootOtherVertex M rho) := by
            refine ⟨heq, rho.1, ?_⟩
            by_cases hb : rho.2
            · exact Or.inl ⟨by simp [d39GeomRootVertex, hb], by simp [d39GeomRootOtherVertex, hb]⟩
            · exact Or.inr ⟨by simp [d39GeomRootOtherVertex, hb], by simp [d39GeomRootVertex, hb]⟩
          have hd : d39GeomGraphDistance M (d39GeomRootVertex M rho)
              (d39GeomRootOtherVertex M rho) = 1 :=
            (SimpleGraph.edist_eq_one_iff_adj).2 hadj
          change d39GeomGraphDistance M (d39GeomRootVertex M rho)
            (d39GeomRootOtherVertex M rho) ≤ (r : ℕ∞)
          rw [hd]
          exact_mod_cast radius_pos
      by_cases hb : rho.2
      · exact ⟨by simpa [d39GeomRootVertex, hb] using hroot,
          by simpa [d39GeomRootOtherVertex, hb] using hother⟩
      · exact ⟨by simpa [d39GeomRootOtherVertex, hb] using hother,
          by simpa [d39GeomRootVertex, hb] using hroot⟩⟩)).1 = rho'.1
  root_initial_map :
    (vertexEquiv ⟨d39GeomRootVertex M rho, by
      simp [d39GeomBallVertices, d39GeomGraphDistance]⟩).1 =
      d39GeomRootVertex M' rho'
  face_image_map : ∀ F,
    h '' F.1 = (faceEquiv F).1

/-- Helper toward Definition 3.8: a positive-radius ball contains the ordered
root edge as a geometric edge, with both endpoints in its vertex set. -/
theorem d39GeomRootEdge_mem {V : Type uV} {E : Type uE}
    {r : ℕ} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (hr : 0 < r) : rho.1 ∈ d39GeomBallEdges M rho r := by
  have hroot : d39GeomRootVertex M rho ∈ d39GeomBallVertices M rho r := by
    simp [d39GeomBallVertices, d39GeomGraphDistance]
  have hother : d39GeomRootOtherVertex M rho ∈ d39GeomBallVertices M rho r := by
    by_cases heq : d39GeomRootVertex M rho = d39GeomRootOtherVertex M rho
    · simpa [heq] using hroot
    · have hadj : (d39GeomGraph M).Adj
          (d39GeomRootVertex M rho) (d39GeomRootOtherVertex M rho) := by
        refine ⟨heq, rho.1, ?_⟩
        by_cases hb : rho.2
        · exact Or.inl ⟨by simp [d39GeomRootVertex, hb],
            by simp [d39GeomRootOtherVertex, hb]⟩
        · exact Or.inr ⟨by simp [d39GeomRootOtherVertex, hb],
            by simp [d39GeomRootVertex, hb]⟩
      have hd : d39GeomGraphDistance M (d39GeomRootVertex M rho)
          (d39GeomRootOtherVertex M rho) = 1 :=
        (SimpleGraph.edist_eq_one_iff_adj).2 hadj
      change d39GeomGraphDistance M (d39GeomRootVertex M rho)
        (d39GeomRootOtherVertex M rho) ≤ (r : ℕ∞)
      rw [hd]
      exact_mod_cast hr
  change M.toPlaneMapWithMissing.src rho.1 ∈ d39GeomBallVertices M rho r ∧
    M.toPlaneMapWithMissing.tgt rho.1 ∈ d39GeomBallVertices M rho r
  by_cases hb : rho.2
  · exact ⟨by simpa [d39GeomRootVertex, hb] using hroot,
      by simpa [d39GeomRootOtherVertex, hb] using hother⟩
  · exact ⟨by simpa [d39GeomRootOtherVertex, hb] using hother,
      by simpa [d39GeomRootVertex, hb] using hroot⟩

namespace D39GeomBallIso

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {r : ℕ} {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: the identity isomorphism of a geometric ball. -/
@[expose] def refl (hr : 0 < r) : D39GeomBallIso r M rho M rho where
  radius_pos := hr
  h := Homeomorph.refl ℂ
  orientationPreserving := orientationPreserving_refl
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  faceEquiv := Equiv.refl _
  pos_map := by intro v; rfl
  arc_range_map := by
    intro e
    change id '' Set.range (M.toPlaneMapWithMissing.arc e.1) =
      Set.range (M.toPlaneMapWithMissing.arc e.1)
    exact Set.image_id _
  src_map := by intro e; rfl
  tgt_map := by intro e; rfl
  missing_map := by intro e; rfl
  orientation_map := by intro e he; rfl
  root_edge_map := rfl
  root_initial_map := rfl
  face_image_map := by intro F; simp

/-- Helper toward Definition 3.8: reverse a geometric ball isomorphism. -/
@[expose] def symm (e : D39GeomBallIso r M rho M' rho') :
    D39GeomBallIso r M' rho' M rho where
  radius_pos := e.radius_pos
  h := e.h.symm
  orientationPreserving := OrientationPreserving.symm e.orientationPreserving
  vertexEquiv := e.vertexEquiv.symm
  edgeEquiv := e.edgeEquiv.symm
  faceEquiv := e.faceEquiv.symm
  pos_map := by
    intro v
    simpa using (congrArg e.h.symm
      (e.pos_map (e.vertexEquiv.symm v))).symm
  arc_range_map := by
    intro e'
    calc
      e.h.symm '' Set.range (M'.toPlaneMapWithMissing.arc e'.1) =
          e.h.symm '' (e.h '' Set.range
            (M.toPlaneMapWithMissing.arc (e.edgeEquiv.symm e').1)) := by
              rw [e.arc_range_map (e.edgeEquiv.symm e')]
              rw [show (e.edgeEquiv (e.edgeEquiv.symm e')).1 = e'.1 from
                congrArg Subtype.val (Equiv.apply_symm_apply e.edgeEquiv e')]
      _ = Set.range (M.toPlaneMapWithMissing.arc (e.edgeEquiv.symm e').1) := by
            rw [Set.image_image]
            simp
  src_map := by
    intro e'
    let a : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.src (e.edgeEquiv.symm e').1,
        (e.edgeEquiv.symm e').2.1⟩
    let b : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.src e'.1, e'.2.1⟩
    have hab : e.vertexEquiv a = b := by
      apply Subtype.ext
      simpa [a, b] using e.src_map (e.edgeEquiv.symm e')
    have h := congrArg (fun x => (e.vertexEquiv.symm x).1) hab
    simpa [a, b] using h.symm
  tgt_map := by
    intro e'
    let a : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.tgt (e.edgeEquiv.symm e').1,
        (e.edgeEquiv.symm e').2.2⟩
    let b : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.tgt e'.1, e'.2.2⟩
    have hab : e.vertexEquiv a = b := by
      apply Subtype.ext
      simpa [a, b] using e.tgt_map (e.edgeEquiv.symm e')
    have h := congrArg (fun x => (e.vertexEquiv.symm x).1) hab
    simpa [a, b] using h.symm
  missing_map := by
    intro e'
    simpa using (e.missing_map (e.edgeEquiv.symm e')).symm
  orientation_map := by
    intro e' he'
    have he : ¬ M.toPlaneMapWithMissing.missing (e.edgeEquiv.symm e').1 := by
      intro hm
      apply he'
      simpa using (e.missing_map (e.edgeEquiv.symm e')).mpr hm
    simpa using (e.orientation_map (e.edgeEquiv.symm e') he).symm
  root_edge_map := by
    let a : {e : E // e ∈ d39GeomBallEdges M rho r} :=
      ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩
    let b : {e : E' // e ∈ d39GeomBallEdges M' rho' r} :=
      ⟨rho'.1, d39GeomRootEdge_mem M' rho' e.radius_pos⟩
    have hab : b = e.edgeEquiv a := by
      apply Subtype.ext
      simpa [a, b] using e.root_edge_map.symm
    calc
      (e.edgeEquiv.symm b).1 = (e.edgeEquiv.symm (e.edgeEquiv a)).1 := by
        rw [hab]
      _ = rho.1 := by simp [a]
  root_initial_map := by
    let a : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨d39GeomRootVertex M rho, by
        simp [d39GeomBallVertices, d39GeomGraphDistance]⟩
    let b : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨d39GeomRootVertex M' rho', by
        simp [d39GeomBallVertices, d39GeomGraphDistance]⟩
    have hab : b = e.vertexEquiv a := by
      apply Subtype.ext
      simpa [a, b] using e.root_initial_map.symm
    calc
      (e.vertexEquiv.symm b).1 = (e.vertexEquiv.symm (e.vertexEquiv a)).1 := by
        rw [hab]
      _ = d39GeomRootVertex M rho := by simp [a]
  face_image_map := by
    intro F'
    calc
      e.h.symm '' F'.1 = e.h.symm '' (e.h '' (e.faceEquiv.symm F').1) := by
        rw [e.face_image_map (e.faceEquiv.symm F')]
        simp
      _ = (e.faceEquiv.symm F').1 := by
        rw [Set.image_image]
        simp

/-- Helper toward Definition 3.8: compose geometric ball isomorphisms at a
fixed radius. -/
@[expose] def trans {V'' E'' : Type*}
    {M'' : DirectedPlaneMapWithMissing V'' E''} {rho'' : E'' × Bool}
    (e : D39GeomBallIso r M rho M' rho')
    (f : D39GeomBallIso r M' rho' M'' rho'') :
    D39GeomBallIso r M rho M'' rho'' where
  radius_pos := e.radius_pos
  h := e.h.trans f.h
  orientationPreserving := OrientationPreserving.trans
    e.orientationPreserving f.orientationPreserving
  vertexEquiv := e.vertexEquiv.trans f.vertexEquiv
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  faceEquiv := e.faceEquiv.trans f.faceEquiv
  pos_map := by
    intro v
    rw [Homeomorph.trans_apply, Equiv.trans_apply, e.pos_map]
    exact f.pos_map (e.vertexEquiv v)
  arc_range_map := by
    intro a
    calc
      (e.h.trans f.h) '' Set.range (M.toPlaneMapWithMissing.arc a.1) =
          f.h '' (e.h '' Set.range (M.toPlaneMapWithMissing.arc a.1)) := by
            ext z
            simp [Homeomorph.trans_apply]
      _ = f.h '' Set.range
          (M'.toPlaneMapWithMissing.arc (e.edgeEquiv a).1) := by
            rw [e.arc_range_map a]
      _ = Set.range
          (M''.toPlaneMapWithMissing.arc (f.edgeEquiv (e.edgeEquiv a)).1) :=
            f.arc_range_map (e.edgeEquiv a)
  src_map := by
    intro a
    let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.src a.1, a.2.1⟩
    let y : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1,
        (e.edgeEquiv a).2.1⟩
    have hxy : e.vertexEquiv x = y := by
      apply Subtype.ext
      simpa [x, y] using e.src_map a
    calc
      (f.vertexEquiv (e.vertexEquiv x)).1 = (f.vertexEquiv y).1 := by rw [hxy]
      _ = M''.toPlaneMapWithMissing.src (f.edgeEquiv (e.edgeEquiv a)).1 :=
        f.src_map (e.edgeEquiv a)
  tgt_map := by
    intro a
    let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.tgt a.1, a.2.2⟩
    let y : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1,
        (e.edgeEquiv a).2.2⟩
    have hxy : e.vertexEquiv x = y := by
      apply Subtype.ext
      simpa [x, y] using e.tgt_map a
    calc
      (f.vertexEquiv (e.vertexEquiv x)).1 = (f.vertexEquiv y).1 := by rw [hxy]
      _ = M''.toPlaneMapWithMissing.tgt (f.edgeEquiv (e.edgeEquiv a)).1 :=
        f.tgt_map (e.edgeEquiv a)
  missing_map := by
    intro a
    exact (f.missing_map (e.edgeEquiv a)).trans (e.missing_map a)
  orientation_map := by
    intro a ha
    have ha' : ¬ M'.toPlaneMapWithMissing.missing (e.edgeEquiv a).1 := by
      intro hm
      exact ha ((e.missing_map a).mp hm)
    calc
      M''.forward ⟨(f.edgeEquiv (e.edgeEquiv a)).1, by
        simpa [f.missing_map] using ha'⟩ =
          M'.forward ⟨(e.edgeEquiv a).1, ha'⟩ := f.orientation_map (e.edgeEquiv a) ha'
      _ = M.forward ⟨a.1, ha⟩ := e.orientation_map a ha
  root_edge_map := by
    let a : {e : E // e ∈ d39GeomBallEdges M rho r} :=
      ⟨rho.1, d39GeomRootEdge_mem M rho e.radius_pos⟩
    let b : {e : E' // e ∈ d39GeomBallEdges M' rho' r} :=
      ⟨rho'.1, d39GeomRootEdge_mem M' rho' e.radius_pos⟩
    let c : {e : E'' // e ∈ d39GeomBallEdges M'' rho'' r} :=
      ⟨rho''.1, d39GeomRootEdge_mem M'' rho'' e.radius_pos⟩
    have hab : e.edgeEquiv a = b := by
      apply Subtype.ext
      simpa [a, b] using e.root_edge_map
    have hbc : f.edgeEquiv b = c := by
      apply Subtype.ext
      simpa [b, c] using f.root_edge_map
    calc
      (f.edgeEquiv (e.edgeEquiv a)).1 = (f.edgeEquiv b).1 := by rw [hab]
      _ = rho''.1 := congrArg Subtype.val hbc
  root_initial_map := by
    let a : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨d39GeomRootVertex M rho, by
        simp [d39GeomBallVertices, d39GeomGraphDistance]⟩
    let b : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨d39GeomRootVertex M' rho', by
        simp [d39GeomBallVertices, d39GeomGraphDistance]⟩
    let c : {v // v ∈ d39GeomBallVertices M'' rho'' r} :=
      ⟨d39GeomRootVertex M'' rho'', by
        simp [d39GeomBallVertices, d39GeomGraphDistance]⟩
    have hab : e.vertexEquiv a = b := by
      apply Subtype.ext
      simpa [a, b] using e.root_initial_map
    have hbc : f.vertexEquiv b = c := by
      apply Subtype.ext
      simpa [b, c] using f.root_initial_map
    calc
      (f.vertexEquiv (e.vertexEquiv a)).1 = (f.vertexEquiv b).1 := by rw [hab]
      _ = d39GeomRootVertex M'' rho'' := congrArg Subtype.val hbc
  face_image_map := by
    intro F
    calc
      (e.h.trans f.h) '' F.1 = f.h '' (e.h '' F.1) := by
        ext z
        simp [Homeomorph.trans_apply]
      _ = f.h '' (e.faceEquiv F).1 := by rw [e.face_image_map F]
      _ = (f.faceEquiv (e.faceEquiv F)).1 := f.face_image_map (e.faceEquiv F)

end D39GeomBallIso

/-- Helper toward Definition 3.8: the local distance is the infimum, in
`ℝ≥0∞`, of `(1/2)^r` over positive integer radii at which the rooted balls are
isomorphic. An empty set of successful radii has infimum `⊤`, matching the
existing local topology combinatorial convention. -/
@[expose] noncomputable def d39GeomDistance {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) : ℝ≥0∞ :=
  ⨅ r : {r : ℕ // 0 < r},
    ⨅ (_ : Nonempty (D39GeomBallIso r.1 M rho M' rho')),
      ((1 / 2 : ℝ≥0∞) ^ r.1)

















end DirectedDistances.PaperProofs.Section3

end
