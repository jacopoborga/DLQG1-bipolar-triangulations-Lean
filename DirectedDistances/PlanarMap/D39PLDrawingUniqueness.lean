/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLStarFace
public import DirectedDistances.PlanarMap.D39PLOrientedPlaneHomeomorph
public import DirectedDistances.PlanarMap.D39PLSimpleFaceWalk2
public import DirectedDistances.PlanarMap.D39PLExistsImageHomeomorph2

/- # Finishing plane extensions after face subdivision

Helpers toward Proposition 5.16. These results supply the simplicity and
orientation steps for drawings whose full-period initial vertices are distinct.
They do not construct the surrounding frame or iterate face stars. Independent -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: both finite drawings lie strictly inside
one axis-aligned square, with any prescribed positive additional margin. -/
theorem exists_common_square_bound
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (margin : ℝ) (hmargin : 0 < margin) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ P.image ∪ P'.image,
      |z.re| + margin < R ∧ |z.im| + margin < R := by
  obtain ⟨r, hr⟩ := (P.isCompact_image.union P'.isCompact_image).isBounded.exists_norm_le
  refine ⟨max r 0 + margin + 1, by positivity, fun z hz => ?_⟩
  have hn : ‖z‖ + margin < max r 0 + margin + 1 := by
    have hle := (hr z hz).trans (le_max_left r 0)
    linarith
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  constructor <;> linarith

/-- Helper toward Proposition 5.16: a common enclosing square has its entire
boundary in the marked exterior of each drawing. This constructs the geometric
frame boundary, but does not insert its darts into the combinatorial map. -/
theorem exists_common_exterior_square
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
    ∃ R : ℝ, 0 < R ∧ (Polyline.enclosingSquare R).IsCyclicSimple ∧
      P.image ∪ P'.image ⊆ (Polyline.enclosingSquare R).inside ∧
      (Polyline.enclosingSquare R).image ⊆ (B.plOrbitFace vert P hvert O_ext).val ∧
      (Polyline.enclosingSquare R).image ⊆ (B.plOrbitFace vert P' hvert O_ext).val := by
  obtain ⟨r, hp, hout, _⟩ := P.exists_closedBall_containing_other_faces
    (B.plOrbitFace vert P hvert O_ext) hext.1
  obtain ⟨r', hp', hout', _⟩ := P'.exists_closedBall_containing_other_faces
    (B.plOrbitFace vert P' hvert O_ext) hext.2
  let R := max (max r r') 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hr : r < R := by
    have h₁ := le_max_left r r'
    have h₂ := le_max_left (max r r') 0
    dsimp [R]
    linarith
  have hr' : r' < R := by
    have h₁ := le_max_right r r'
    have h₂ := le_max_left (max r r') 0
    dsimp [R]
    linarith
  have hnorm (z : ℂ) (hz : z ∈ (Polyline.enclosingSquare R).image) : R ≤ ‖z‖ := by
    have hside := ((Polyline.mem_enclosingSquare_image_iff R hR z).mp hz).2.2
    have hre := Complex.abs_re_le_norm z
    have him := Complex.abs_im_le_norm z
    rcases hside with hz | hz | hz | hz
    · rw [hz, abs_neg, abs_of_pos hR] at hre
      exact hre
    · rw [hz, abs_of_pos hR] at hre
      exact hre
    · rw [hz, abs_neg, abs_of_pos hR] at him
      exact him
    · rw [hz, abs_of_pos hR] at him
      exact him
  refine ⟨R, hR, Polyline.enclosingSquare_isCyclicSimple R hR, ?_, ?_, ?_⟩
  · intro z hz
    have hzR : ‖z‖ < R := by
      rcases hz with hz | hz
      · have h := hp hz
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h.trans_lt hr
      · have h := hp' hz
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h.trans_lt hr'
    rw [Polyline.enclosingSquare_inside R hR]
    exact ⟨abs_lt.mp ((Complex.abs_re_le_norm z).trans_lt hzR),
      abs_lt.mp ((Complex.abs_im_le_norm z).trans_lt hzR)⟩
  · intro z hz
    apply hout
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    exact hr.trans_le (hnorm z hz)
  · intro z hz
    apply hout'
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    exact hr'.trans_le (hnorm z hz)

/-- Helper toward Proposition 5.16: distinct initial vertices in a full-period
walk of length at least three imply cyclic simplicity of the actual walk,
including all subdivision points of the dart arcs. -/
theorem faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D)
    (hperiod : 3 ≤ Function.minimalPeriod B.map.faceSucc d)
    (hinj : Set.InjOn (fun n : ℕ => vert
      ((B.map.faceSucc : B.D → B.D)^[n] d))
      (Set.Iio (Function.minimalPeriod B.map.faceSucc d))) :
    (faceWalkPolyline B vert P d
      (Function.minimalPeriod B.map.faceSucc d - 1)).start =
      (faceWalkPolyline B vert P d
        (Function.minimalPeriod B.map.faceSucc d - 1)).finish ∧
    (faceWalkPolyline B vert P d
      (Function.minimalPeriod B.map.faceSucc d - 1)).IsCyclicSimple := by
  let n := Function.minimalPeriod B.map.faceSucc d - 1
  let c := faceWalkPolyline B vert P d n
  have hlen : 4 ≤ c.points.length :=
    B.faceWalkPolyline_fullPeriod_points_length_ge_four vert P d hperiod
  have hclosed : c.start = c.finish := B.faceWalkPolyline_fullPeriod_closed vert P d
  have hpoints := B.faceWalkPolyline_points_injective_of_initialVertices vert P d n
    (fun k l hk hl hne heq => hne (hinj
      (by show k < Function.minimalPeriod B.map.faceSucc d; dsimp [n] at hk; omega)
      (by show l < Function.minimalPeriod B.map.faceSucc d; dsimp [n] at hl; omega) heq))
    (fun k l hk hl => B.faceWalk_fullPeriod_no_flip_of_initialVertices vert P d
      hperiod (fun k l hk hl heq => hinj hk hl heq) k l
        (by dsimp [n] at hk; omega) (by dsimp [n] at hl; omega))
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
    apply List.ext_getElem
    · rw [Polyline.length_intervalPolyline]
      omega
    · intro i hi hj
      have heq := Polyline.point_intervalPolyline c 0 (c.points.length - 1) i (by omega)
      simpa only [Nat.zero_add, Polyline.point, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hj, Option.getD_some] using heq
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
        rw [hfull]
        exact hpoints)
  change (c.intervalPolyline 0 (c.points.length - 1)).IsCyclicSimple at hs
  rwa [hfull] at hs

/-- Helper toward Proposition 5.16: the full-period walks of two drawings
give the whole-boundary simplicity package directly from common dart and
initial-vertex data. -/
theorem exists_simple_orbit_boundaries_of_initialVertices
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hperiod : ∀ d : B.D, 3 ≤ Function.minimalPeriod B.map.faceSucc d)
    (hinj : ∀ d : B.D, Set.InjOn (fun n : ℕ => vert
      ((B.map.faceSucc : B.D → B.D)^[n] d))
      (Set.Iio (Function.minimalPeriod B.map.faceSucc d))) :
    ∀ O : D39BallFaceCycleOrbit B, ∃ q q' : Polyline,
      q.start = q.finish ∧ q.IsCyclicSimple ∧
      q.image = B.plOrbitBoundary vert P O ∧
      q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
      q'.image = B.plOrbitBoundary vert P' O := by
  intro O
  obtain ⟨d, hO⟩ := O.property
  have hd : d ∈ O.val := hO ▸ Equiv.Perm.SameCycle.rfl
  have hs := B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
    vert P d (hperiod d) (hinj d)
  have hs' := B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
    vert P' d (hperiod d) (hinj d)
  exact ⟨_, _, hs.1, hs.2,
    B.faceWalkPolyline_image_eq_plOrbitBoundary vert P O d hd,
    hs'.1, hs'.2, B.faceWalkPolyline_image_eq_plOrbitBoundary vert P' O d hd⟩

/-- Helper toward Proposition 5.16: an orbit with distinct initial vertices
and period at least three cannot contain the reverse of one of its darts.
Consequently a second orbit exists, without an extra bounded-face premise. -/
theorem exists_orbit_ne_of_initialVertices
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (O : D39BallFaceCycleOrbit B) (d : B.D) (hd : d ∈ O.val)
    (hperiod : 3 ≤ Function.minimalPeriod B.map.faceSucc d)
    (hinj : Set.InjOn (fun n : ℕ => vert
      ((B.map.faceSucc : B.D → B.D)^[n] d))
      (Set.Iio (Function.minimalPeriod B.map.faceSucc d))) :
    ∃ O' : D39BallFaceCycleOrbit B, O' ≠ O := by
  let O' : D39BallFaceCycleOrbit B :=
    ⟨{e | B.map.faceSucc.SameCycle (B.map.edgeInv d) e}, B.map.edgeInv d, rfl⟩
  refine ⟨O', ?_⟩
  intro heq
  have hflip : B.map.edgeInv d ∈ O.val :=
    heq ▸ (show B.map.edgeInv d ∈ O'.val from Equiv.Perm.SameCycle.rfl)
  obtain ⟨a, ha⟩ := O.property
  have had : B.map.faceSucc.SameCycle a d := by rw [ha] at hd; exact hd
  have haf : B.map.faceSucc.SameCycle a (B.map.edgeInv d) := by
    rw [ha] at hflip
    exact hflip
  obtain ⟨n, hn⟩ := (had.symm.trans haf).exists_nat_pow_eq
  have hn' : (B.map.faceSucc : B.D → B.D)^[n] d = B.map.edgeInv d := by
    simpa only [Equiv.Perm.coe_pow] using hn
  have hm : n % Function.minimalPeriod B.map.faceSucc d <
      Function.minimalPeriod B.map.faceSucc d := Nat.mod_lt _ (by omega)
  have hno := B.faceWalk_fullPeriod_no_flip_of_initialVertices vert P d hperiod
    (fun k l hk hl heq => hinj hk hl heq) 0
    (n % Function.minimalPeriod B.map.faceSucc d) (by omega) hm
  apply hno
  change (B.map.faceSucc : B.D → B.D)^[n % Function.minimalPeriod B.map.faceSucc d] d =
    B.map.edgeInv d
  exact Function.iterate_mod_minimalPeriod_eq.trans hn'

/-- Helper toward Proposition 5.16: for drawings with distinct full-period
initial vertices, an image homeomorphism extends to an orientation-preserving
plane homeomorphism preserving vertices, arcs, and all open and closed faces.
The marked exterior is unbounded in both drawings. -/
theorem exists_orientationPreserving_plane_homeomorph_of_initialVertices
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hperiod : ∀ d : B.D, 3 ≤ Function.minimalPeriod B.map.faceSucc d)
    (hinj : ∀ d : B.D, Set.InjOn (fun n : ℕ => vert
      ((B.map.faceSucc : B.D → B.D)^[n] d))
      (Set.Iio (Function.minimalPeriod B.map.faceSucc d))) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : P.image, H x = (f.toHomeomorph x : ℂ)) ∧
      (∀ v : V, H (P.pos v) = P'.pos v) ∧
      (∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      ∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val := by
  obtain ⟨H, hH, harc, hclosed, hface⟩ :=
    B.exists_plane_homeomorph_of_simple_orbit_boundaries_mapping_faces
      vert P P' hvert hconn f O_ext hext
      (B.exists_simple_orbit_boundaries_of_initialVertices vert P P' hperiod hinj)
  obtain ⟨dext, hdext⟩ := O_ext.property
  obtain ⟨O, hO⟩ := B.exists_orbit_ne_of_initialVertices vert P O_ext dext
    (hdext ▸ Equiv.Perm.SameCycle.rfl) (hperiod dext) (hinj dext)
  obtain ⟨d, hdO⟩ := O.property
  have hd : d ∈ O.val := hdO ▸ Equiv.Perm.SameCycle.rfl
  obtain ⟨hb, hb'⟩ := B.isBounded_plOrbitFace_of_ne_external
    vert P P' hvert hconn O_ext hext O hO
  have hor : OrientationPreserving H := B.orientationPreserving_of_simple_fullPeriod_faceWalks
    vert P P' hvert hconn f H hH harc hface O hb hb' d hd
    (B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
      vert P d (hperiod d) (hinj d)).2
    (B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
      vert P' d (hperiod d) (hinj d)).2
  refine ⟨H, hor, hH, ?_, harc, hclosed, hface⟩
  intro v
  exact (hH ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩).trans (f.vertex_image v)

/-- Helper toward Proposition 5.16: one representative per orbit suffices
for the plane-extension step. This is the form needed when completed stars
are listed by triangle representatives and the exterior by a frame dart. -/
theorem exists_orientationPreserving_plane_homeomorph_extending_image_of_orbit_initialVertices
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hfaces : ∀ O : D39BallFaceCycleOrbit B, ∃ d ∈ O.val,
      3 ≤ Function.minimalPeriod B.map.faceSucc d ∧
      Set.InjOn (fun n : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[n] d))
        (Set.Iio (Function.minimalPeriod B.map.faceSucc d))) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : P.image, H x = (f.toHomeomorph x : ℂ)) ∧
      (∀ v : V, H (P.pos v) = P'.pos v) ∧
      (∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      ∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val := by
  have hsimple : ∀ O : D39BallFaceCycleOrbit B, ∃ q q' : Polyline,
      q.start = q.finish ∧ q.IsCyclicSimple ∧ q.image = B.plOrbitBoundary vert P O ∧
      q'.start = q'.finish ∧ q'.IsCyclicSimple ∧ q'.image = B.plOrbitBoundary vert P' O := by
    intro O
    obtain ⟨d, hd, hp, hv⟩ := hfaces O
    have hs := B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices vert P d hp hv
    have hs' := B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices vert P' d hp hv
    exact ⟨_, _, hs.1, hs.2, B.faceWalkPolyline_image_eq_plOrbitBoundary vert P O d hd,
      hs'.1, hs'.2, B.faceWalkPolyline_image_eq_plOrbitBoundary vert P' O d hd⟩
  obtain ⟨H, hH, harc, hclosed, hface⟩ :=
    B.exists_plane_homeomorph_of_simple_orbit_boundaries_mapping_faces
      vert P P' hvert hconn f O_ext hext hsimple
  obtain ⟨dext, hdext, hpext, hvext⟩ := hfaces O_ext
  obtain ⟨O, hO⟩ := B.exists_orbit_ne_of_initialVertices vert P O_ext dext hdext hpext hvext
  obtain ⟨d, hd, hp, hv⟩ := hfaces O
  obtain ⟨hb, hb'⟩ := B.isBounded_plOrbitFace_of_ne_external
    vert P P' hvert hconn O_ext hext O hO
  have hor : OrientationPreserving H := B.orientationPreserving_of_simple_fullPeriod_faceWalks
    vert P P' hvert hconn f H hH harc hface O hb hb' d hd
    (B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices vert P d hp hv).2
    (B.faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices vert P' d hp hv).2
  refine ⟨H, hor, hH, ?_, harc, hclosed, hface⟩
  intro v
  exact (hH ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩).trans (f.vertex_image v)

/-- Helper toward Proposition 5.16: vertex-simple full-period orbit data
give an orientation-preserving equivalence of the two plane drawings.
The drawing-image homeomorphism is constructed, rather than assumed. -/
theorem exists_orientationPreserving_plane_homeomorph_of_orbit_initialVertices
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hfaces : ∀ O : D39BallFaceCycleOrbit B, ∃ d ∈ O.val,
      3 ≤ Function.minimalPeriod B.map.faceSucc d ∧
      Set.InjOn (fun n : ℕ => vert ((B.map.faceSucc : B.D → B.D)^[n] d))
        (Set.Iio (Function.minimalPeriod B.map.faceSucc d))) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ v : V, H (P.pos v) = P'.pos v) ∧
      (∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      ∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val := by
  obtain ⟨f⟩ := B.exists_plImageHomeomorph vert P P'
  obtain ⟨H, hor, _, hv, ha, hc, hf⟩ :=
    B.exists_orientationPreserving_plane_homeomorph_extending_image_of_orbit_initialVertices
      vert P P' hvert hconn f O_ext hext hfaces
  exact ⟨H, hor, hv, ha, hc, hf⟩

/-- Helper toward Proposition 5.16: cutting off a star triangle produces
simple full-period walks in both new drawings, even if the old face boundary
repeats vertices. All old labeled arcs and positions remain unchanged. -/
theorem exists_star_chord_step_simple_triangle
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hcentre : vert (B.map.faceSucc b) ≠ vert a) :
    let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
    ∃ (Q Q' : PLDrawing C.D V C.map.edgeInv C.map.rot (B.chordVert vert a b)),
      (∀ v, Q.pos v = P.pos v) ∧ (∀ v, Q'.pos v = P'.pos v) ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) ∧
      Function.minimalPeriod C.map.faceSucc (.inr true) = 3 ∧
      (faceWalkPolyline C (B.chordVert vert a b) Q (.inr true) 2).IsCyclicSimple ∧
      (faceWalkPolyline C (B.chordVert vert a b) Q' (.inr true) 2).IsCyclicSimple := by
  dsimp only
  obtain ⟨Q, Q', hp, hp', ha, ha', ht, hinj, _⟩ :=
    B.exists_star_chord_step vert P P' hvert a b hvab hi hwalk hcentre
  have hs := faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
      (B.insertChord a b (B.chord_corners_ne vert a b hvab))
      (B.chordVert vert a b) Q (.inr true) (by omega) (by rwa [ht])
  have hs' := faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
      (B.insertChord a b (B.chord_corners_ne vert a b hvab))
      (B.chordVert vert a b) Q' (.inr true) (by omega) (by rwa [ht])
  refine ⟨Q, Q', hp, hp', ha, ha', ht, ?_, ?_⟩
  · simpa only [ht, Nat.reduceSub] using hs.2
  · simpa only [ht, Nat.reduceSub] using hs'.2

/-- Helper toward Proposition 5.16: a star chord in another face preserves
cyclic simplicity of the full-period walk of a previously completed face.
The new drawing may have a different subdivision schedule on the new chord. -/
theorem star_chord_preserves_simple_walk
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (a b : B.D) (hab : a ≠ b) (hface : B.map.faceSucc.SameCycle b a)
    (x : B.D) (hx : ¬ B.map.faceSucc.SameCycle b x)
    (Q : PLDrawing (B.insertChord a b hab).D V
      (B.insertChord a b hab).map.edgeInv (B.insertChord a b hab).map.rot
      (B.chordVert vert a b))
    (hperiod : 3 ≤ Function.minimalPeriod B.map.faceSucc x)
    (hinj : Set.InjOn (fun n : ℕ => vert
      ((B.map.faceSucc : B.D → B.D)^[n] x))
      (Set.Iio (Function.minimalPeriod B.map.faceSucc x))) :
    (faceWalkPolyline (B.insertChord a b hab) (B.chordVert vert a b) Q (.inl x)
      (Function.minimalPeriod (B.insertChord a b hab).map.faceSucc (.inl x) - 1)).IsCyclicSimple := by
  obtain ⟨hp, _, hv⟩ := B.star_chord_preserves_unaffected vert a b hab hface x hx
  apply (faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
    (B.insertChord a b hab) (B.chordVert vert a b) Q (.inl x) ?_ ?_).2
  · change 3 ≤ Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inl x)
    rwa [hp]
  · change Set.InjOn _ (Set.Iio
      (Function.minimalPeriod (B.chordMap a b hab).faceSucc (.inl x)))
    rw [hp]
    exact (hv _).mpr hinj

end D39FiniteBall

namespace PLDrawing

/-- Helper toward Proposition 5.16: preservation of the labeled vertices
and geometric arcs implies preservation of the entire original drawing image.
This also retains vertices that are not initial vertices of any dart. -/
theorem image_image_of_vertices_arcs
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P P' : PLDrawing D V flip rot vert) (H : ℂ → ℂ)
    (hpos : ∀ v, H (P.pos v) = P'.pos v)
    (harc : ∀ d, H '' (P.arc d).image = (P'.arc d).image) :
    H '' P.image = P'.image := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨v, rfl⟩ | ⟨d, hd⟩
    · exact Or.inl ⟨v, (hpos v).symm⟩
    · exact Or.inr ⟨d, harc d ▸ Set.mem_image_of_mem H hd⟩
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact ⟨P.pos v, Or.inl ⟨v, rfl⟩, hpos v⟩
    · obtain ⟨x, hx, hxy⟩ := (harc d).symm ▸ hd
      exact ⟨x, Or.inr ⟨d, hx⟩, hxy⟩

/-- Helper toward Proposition 5.16: a plane homeomorphism of augmented
drawings restricts to every original labeled vertex and arc whenever the
augmentation retains their positions and polylines. -/
theorem restrict_plane_homeomorph
    {D V E W : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : E → E} {rot' : Equiv.Perm E} {vert' : E → W}
    (P P' : PLDrawing D V flip rot vert)
    (Q Q' : PLDrawing E W flip' rot' vert') (ι : D → E) (σ : V → W)
    (hpos : ∀ v, Q.pos (σ v) = P.pos v)
    (hpos' : ∀ v, Q'.pos (σ v) = P'.pos v)
    (harc : ∀ d, Q.arc (ι d) = P.arc d)
    (harc' : ∀ d, Q'.arc (ι d) = P'.arc d)
    (H : ℂ ≃ₜ ℂ)
    (hHpos : ∀ w, H (Q.pos w) = Q'.pos w)
    (hHarc : ∀ e, H '' (Q.arc e).image = (Q'.arc e).image) :
    (∀ v, H (P.pos v) = P'.pos v) ∧
    (∀ d, H '' (P.arc d).image = (P'.arc d).image) ∧ H '' P.image = P'.image := by
  have hv (v : V) : H (P.pos v) = P'.pos v := by
    rw [← hpos v, hHpos, hpos']
  have ha (d : D) : H '' (P.arc d).image = (P'.arc d).image := by
    rw [← harc d, hHarc, harc']
  exact ⟨hv, ha, P.image_image_of_vertices_arcs P' H hv ha⟩

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: an augmented equivalence restricts to
the original drawings, including all closed and open faces, once their closed
faces are identified as unions of the corresponding augmented closed faces.
This theorem does not construct the augmentation or prove those union identities. -/
theorem exists_orientationPreserving_plane_homeomorph_of_augmentation
    {V W : Type*} [Finite W]
    (B C : D39FiniteBall) (vert : B.D → V) (v : C.D → W)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (Q Q' : PLDrawing C.D W C.map.edgeInv C.map.rot v)
    (hvert : Function.Surjective vert) (hv : Function.Surjective v)
    (hconn : ∀ d e : C.D, Relation.EqvGen
      (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e)
    (ι : B.D → C.D) (σ : V → W)
    (hpos : ∀ x, Q.pos (σ x) = P.pos x)
    (hpos' : ∀ x, Q'.pos (σ x) = P'.pos x)
    (harc : ∀ d, Q.arc (ι d) = P.arc d)
    (harc' : ∀ d, Q'.arc (ι d) = P'.arc d)
    (O_ext : D39BallFaceCycleOrbit C)
    (hext : (¬ Bornology.IsBounded (C.plOrbitFace v Q hv O_ext).val) ∧
      (¬ Bornology.IsBounded (C.plOrbitFace v Q' hv O_ext).val))
    (hfaces : ∀ O : D39BallFaceCycleOrbit C, ∃ d ∈ O.val,
      3 ≤ Function.minimalPeriod C.map.faceSucc d ∧
      Set.InjOn (fun n : ℕ => v ((C.map.faceSucc : C.D → C.D)^[n] d))
        (Set.Iio (Function.minimalPeriod C.map.faceSucc d)))
    (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C))
    (hcover : ∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val)
    (hcover' : ∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image) ∧
      (H '' P.image = P'.image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      ∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val := by
  obtain ⟨H, hor, hHpos, hHarc, hHclosed, _⟩ :=
    C.exists_orientationPreserving_plane_homeomorph_of_orbit_initialVertices
      v Q Q' hv hconn O_ext hext hfaces
  obtain ⟨hp, ha, himage⟩ := P.restrict_plane_homeomorph P' Q Q' ι σ
    hpos hpos' harc harc' H hHpos hHarc
  have hc (O : D39BallFaceCycleOrbit B) :
      H '' closure (B.plOrbitFace vert P hvert O).val =
        closure (B.plOrbitFace vert P' hvert O).val := by
    rw [hcover O, hcover' O]
    simp only [Set.image_iUnion, hHclosed]
  refine ⟨H, hor, hp, ha, himage, hc, ?_⟩
  intro O
  rw [← P.closure_face_diff_image hvert, ← P'.closure_face_diff_image hvert,
    Set.image_sdiff H.injective, hc O, himage]

end D39FiniteBall







































































end DirectedDistances.PlanarMap
end
