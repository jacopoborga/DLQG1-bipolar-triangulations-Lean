/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso5
public import DirectedDistances.PlanarMap.D39PLSimpleFaceWalk2
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness6

/- # Orbit-local simplicity and positive winding

not establish the general original-face identification or exterior transport. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

/-- Helper toward Proposition 5.16: different dart occurrences have strictly
increasing point offsets, since every dart arc contributes at least one
segment to the concatenated walk. -/
theorem faceWalkPointOffset_strictMono
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert) (d : A.D) :
    StrictMono (D39FiniteBall.faceWalkPointOffset A vert P d) := by
  apply strictMono_nat_of_lt_succ
  intro k
  cases k with
  | zero =>
      change 0 < (P.arc d).points.length - 1
      have hlen := P.arc_length d
      omega
  | succ k =>
      simp only [D39FiniteBall.faceWalkPointOffset, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
        faceWalkPolyline, Polyline.length_boundaryConcat]
      have hlen := P.arc_length ((A.map.faceSucc : A.D → A.D)^[k + 1] d)
      have hpos := A.faceWalkPolyline_points_length_ge_two vert P d k
      omega

/-- Helper toward Proposition 5.16: every dart occurrence starts at its
exact point offset in the whole walk, before the closing point. This retains
occurrence identity even when the initial vertex is repeated. -/
theorem faceWalkPolyline_point_at_offset
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert) (d : A.D) (n : ℕ) :
    ∀ k : ℕ, k ≤ n →
      D39FiniteBall.faceWalkPointOffset A vert P d k <
        (faceWalkPolyline A vert P d n).points.length - 1 ∧
      (faceWalkPolyline A vert P d n).point
          (D39FiniteBall.faceWalkPointOffset A vert P d k) =
        P.pos (vert ((A.map.faceSucc : A.D → A.D)^[k] d)) := by
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simp only [D39FiniteBall.faceWalkPointOffset, ↓reduceIte,
        faceWalkPolyline, Function.iterate_zero_apply]
      refine ⟨by have := P.arc_length d; omega, ?_⟩
      exact (Polyline.point_zero_eq_start _).trans (P.arc_start d)
  | succ n ih =>
      intro k hk
      by_cases hkn : k ≤ n
      · obtain ⟨hbound, hpoint⟩ := ih k hkn
        refine ⟨?_, ?_⟩
        · rw [faceWalkPolyline, Polyline.length_boundaryConcat]
          have hlen := P.arc_length ((A.map.faceSucc : A.D → A.D)^[n + 1] d)
          omega
        · rw [faceWalkPolyline, Polyline.point_boundaryConcat_left _ _ _ (by omega)]
          exact hpoint
      · have hkeq : k = n + 1 := by omega
        subst k
        have hoff : D39FiniteBall.faceWalkPointOffset A vert P d (n + 1) =
            (faceWalkPolyline A vert P d n).points.length - 1 := by
          simp only [D39FiniteBall.faceWalkPointOffset, Nat.add_eq_zero_iff,
            Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        rw [hoff]
        refine ⟨?_, ?_⟩
        · rw [faceWalkPolyline, Polyline.length_boundaryConcat]
          have hlen := P.arc_length ((A.map.faceSucc : A.D → A.D)^[n + 1] d)
          have hpos := A.faceWalkPolyline_points_length_ge_two vert P d n
          omega
        · rw [faceWalkPolyline]
          have hpoint := Polyline.point_boundaryConcat_right
            (faceWalkPolyline A vert P d n)
            (P.arc ((A.map.faceSucc : A.D → A.D)^[n + 1] d))
            (finish_faceWalkPolyline_eq_next_start A vert P d n) 0
            (by have := P.arc_length ((A.map.faceSucc : A.D → A.D)^[n + 1] d); omega)
          simpa only [Nat.add_zero, Polyline.point_zero_eq_start, P.arc_start] using hpoint

/-- Helper toward Proposition 5.16: a cyclically simple full-period walk
cannot repeat an initial vertex before closing. Thus repeated incidences
cannot be discharged by asserting simplicity of the unmodified walk. -/
theorem faceWalk_initialVertices_injOn_of_fullPeriod_isCyclicSimple
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert) (d : A.D)
    (hc : (faceWalkPolyline A vert P d
      (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).IsCyclicSimple) :
    Set.InjOn (fun k : ℕ => vert ((A.map.faceSucc : A.D → A.D)^[k] d))
      (Set.Iio (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d)) := by
  intro k hk l hl heq
  obtain ⟨hkbound, hkpoint⟩ := faceWalkPolyline_point_at_offset A vert P d
    (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1) k (by
      change k < _ at hk; omega)
  obtain ⟨hlbound, hlpoint⟩ := faceWalkPolyline_point_at_offset A vert P d
    (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1) l (by
      change l < _ at hl; omega)
  apply (faceWalkPointOffset_strictMono A vert P d).injective
  exact Polyline.point_injective_before_closure _ hc hkbound hlbound
    (hkpoint.trans ((congrArg P.pos heq).trans hlpoint.symm))

/-- Helper toward Proposition 5.16: a repeated initial vertex at two distinct
occurrences before closing rules out cyclic simplicity of the original full
walk. Thickening or augmentation must therefore change that walk. -/
theorem not_faceWalkPolyline_fullPeriod_isCyclicSimple_of_repeated_initialVertex
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert) (d : A.D)
    (k l : ℕ)
    (hk : k < Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d)
    (hl : l < Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d)
    (hkl : k ≠ l)
    (heq : vert ((A.map.faceSucc : A.D → A.D)^[k] d) =
      vert ((A.map.faceSucc : A.D → A.D)^[l] d)) :
    ¬ (faceWalkPolyline A vert P d
      (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).IsCyclicSimple := by
  intro hc
  exact hkl (faceWalk_initialVertices_injOn_of_fullPeriod_isCyclicSimple
    A vert P d hc hk hl heq)

/-- Helper toward Proposition 5.16: injectivity of the initial vertices
within one full face period suffices for geometric cyclic simplicity. No
condition on the other face orbits or on cut vertices is used. The period
bound is explicit; one- and two-dart orbits are not covered. -/
theorem faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert) (d : A.D)
    (hperiod : 3 ≤ Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d)
    (hinj : Set.InjOn
      (fun k : ℕ => vert ((A.map.faceSucc : A.D → A.D)^[k] d))
      (Set.Iio (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d))) :
    (faceWalkPolyline A vert P d
      (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).IsCyclicSimple := by
  apply P.isCyclicSimple_of_arc_segment_sources
  · exact A.faceWalkPolyline_fullPeriod_points_length_ge_four vert P d hperiod
  · exact faceWalkPolyline_closed A vert P d
  · apply A.faceWalkPolyline_points_injective_of_initialVertices vert P d
    · intro k l hk hl hne heq
      exact hne (hinj (by change k < _; omega) (by change l < _; omega) heq)
    · intro k l hk hl
      exact A.faceWalk_fullPeriod_no_flip_of_initialVertices vert P d hperiod
        (fun k l hk hl heq => hinj hk hl heq) k l (by omega) (by omega)
  · exact faceWalkPolyline_segment_sources A vert P d _

/-- Helper toward Proposition 5.16: vertex injectivity on the particular
dart orbit supplies cyclic simplicity of its restricted full-period walk.
This uses the exact orbit characterization rather than a global no-cut
assumption. -/
theorem faceWalkPolyline_fullPeriod_isCyclicSimple_of_orbit_vertex_injective
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (O : D39BallFaceCycleOrbit A) (d : A.D) (hd : d ∈ O.val)
    (hperiod : 3 ≤ Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d)
    (hinj : Set.InjOn vert O.val) :
    (faceWalkPolyline A vert P d
      (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).IsCyclicSimple := by
  apply faceWalkPolyline_fullPeriod_isCyclicSimple_of_initialVertices A vert P d hperiod
  apply (D39FiniteBall.drawing_initialVertices_injOn_iff A.map.faceSucc vert d).mpr
  obtain ⟨a, ha⟩ := O.property
  have had : A.map.faceSucc.SameCycle a d := by
    simpa only [ha, Set.mem_ofPred_eq] using hd
  intro e he f hf hef
  exact hinj (by simpa only [ha, Set.mem_ofPred_eq] using had.trans he)
    (by simpa only [ha, Set.mem_ofPred_eq] using had.trans hf) hef






theorem faceWalkPolyline_fullPeriod_simple_and_angleSum_one_of_orbit_vertex_injective
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : A.D, Relation.EqvGen
      (fun x y => A.map.rot x = y ∨ A.map.edgeInv x = y) d e)
    (O : D39BallFaceCycleOrbit A)
    (hbounded : Bornology.IsBounded (A.plOrbitFace vert P hvert O).val)
    (d : A.D) (hd : d ∈ O.val)
    (hperiod : 3 ≤ Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d)
    (hinj : Set.InjOn vert O.val) :
    (faceWalkPolyline A vert P d
      (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).IsCyclicSimple ∧
    ∀ z ∈ (A.plOrbitFace vert P hvert O).val,
      (faceWalkPolyline A vert P d
        (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).angleSum z = 1 := by
  have hc := faceWalkPolyline_fullPeriod_isCyclicSimple_of_orbit_vertex_injective
    A vert P O d hd hperiod hinj
  exact ⟨hc, A.faceWalkPolyline_fullPeriod_angleSum_eq_one_of_isBounded
    vert P hvert hconn O hbounded d hd (faceWalkPolyline_closed A vert P d) hc⟩

/-- Helper toward Proposition 5.16: every target face orbit has a preimage
under a ball isomorphism, without any exterior-marker condition. -/
theorem plBallFaceOrbitMap_surjective
    {A B : D39FiniteBall} (I : D39BallIso A B) :
    Function.Surjective (plBallFaceOrbitMap I) := by
  intro S
  refine ⟨plBallFaceOrbitMap I.symm S, ?_⟩
  apply Subtype.ext
  ext e
  obtain ⟨d, rfl⟩ := I.toEquiv.surjective e
  rw [plBallFaceOrbitMap_mem_iff]
  have h := plBallFaceOrbitMap_mem_iff I.symm S (I.toEquiv d)
  simpa only [D39BallIso.symm, Equiv.symm_apply_apply] using h

/-- Helper toward Proposition 5.16: one direction of boundedness
preservation already characterizes exterior transport. Surjectivity of
orbit transport and uniqueness of each drawing's unbounded orbit prove
the converse, without constructing a plane homeomorphism or using DU1.
This is a reduction, not a proof that boundedness is preserved. -/
theorem d39FacedBallPLDrawing_external_iff_preserves_boundedness
    {M N : D39RootedMap}
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) :
    (∀ d : (d39FacedBall M r hr).D,
      I.toEquiv d ∈ (d39FacedBallPLWithExternal N Q r hr).externalOrbit.val ↔
        d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val) ↔
    ∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      Bornology.IsBounded
        ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val →
      Bornology.IsBounded
        ((d39FacedBall N r hr).plOrbitFace
          (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N Q r hr)
          (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
          (plBallFaceOrbitMap I O)).val := by
  constructor
  · intro hext O
    exact ((d39FacedBallPLDrawing_external_iff_orbitFace_boundedness
      P Q r hr I).mp hext O).mp
  · intro hb
    obtain ⟨O, hO⟩ := plBallFaceOrbitMap_surjective I
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit
    have hnot : ¬ Bornology.IsBounded
        ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val := by
      intro hbounded
      have htarget := hb O hbounded
      rw [hO] at htarget
      exact d39FacedBallPLWithExternal_unbounded N Q r hr htarget
    have hsource := (d39FacedBallPLWithExternal_external_iff M P r hr O).mpr hnot
    apply (plBallFaceOrbitMap_eq_iff I
      (d39FacedBallPLWithExternal M P r hr).externalOrbit
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit).mp
    rw [← hsource]
    exact hO



























































































































































end DirectedDistances.PaperProofs.Section5

end
