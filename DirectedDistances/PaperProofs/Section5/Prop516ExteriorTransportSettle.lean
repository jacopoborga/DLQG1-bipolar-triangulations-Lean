/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516BallMarkerPreservation
public import DirectedDistances.PaperProofs.Section5.Prop516PLExteriorTransport

/- # Actual-ball tests for exterior transport

Helpers toward Proposition 5.16 and Definition 3.8
all-present acyclic rooted map, not arbitrary finite marked-ball data.
Geometric representations of it are a separate obligation. Independent -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16: a permutation-invariant dart test is
constant on each face or vertex cycle of a finite carrier. -/
theorem exteriorTest_sameCycle_invariant {D E : Type*} [Finite D]
    (p : Equiv.Perm D) (f : D → E) (hf : ∀ d, f (p d) = f d)
    {d e : D} (h : p.SameCycle d e) : f d = f e := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hf]
    exact ih

/-- Helper toward Proposition 5.16: the degree-two rotation of a digon;
the first Boolean distinguishes its two geometric edges. -/
@[expose] def exteriorTestDigonRot : Equiv.Perm (Bool × Bool) where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by rintro ⟨a, b⟩; cases a <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases a <;> rfl

/-- Helper toward Proposition 5.16: geometric edge reversal exchanges
the two endpoint incidences without identifying the parallel edges. -/
@[expose] def exteriorTestDigonFlip : Equiv.Perm (Bool × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨a, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases b <;> rfl

/-- Helper toward Proposition 5.16: the vertex Boolean descends to the
rotation-orbit quotient, so the two digon endpoints remain distinct. -/
@[expose] def exteriorTestDigonVertexSide :
    RootedLocallyFiniteVertex (Bool × Bool) exteriorTestDigonRot → Bool :=
  Quotient.lift Prod.snd (fun _ _ h =>
    exteriorTest_sameCycle_invariant exteriorTestDigonRot Prod.snd (fun _ => rfl) h)

private theorem digon_directed_step_sides
    {v w : RootedLocallyFiniteVertex (Bool × Bool) exteriorTestDigonRot}
    (h : rootedLocallyFiniteDirectedStep exteriorTestDigonRot
      exteriorTestDigonFlip (fun _ => False) (fun d => d.2 = false) v w) :
    exteriorTestDigonVertexSide v = false ∧
      exteriorTestDigonVertexSide w = true := by
  obtain ⟨⟨a, b⟩, _, hb, rfl, rfl⟩ := h
  cases b
  · exact ⟨rfl, rfl⟩
  · exact Bool.noConfusion hb

/-- Helper toward Proposition 5.16: an all-present, two-edge, two-vertex
acyclic digon with its first forward dart as the ordered root. -/
@[expose] def exteriorTestDigon : D39RootedMap :=
  { core :=
      { D := Bool × Bool
        rot := exteriorTestDigonRot
        edgeInv := exteriorTestDigonFlip
        edgeInv_invol := by rintro ⟨a, b⟩; cases b <;> rfl
        edgeInv_ne := by rintro ⟨a, b⟩; cases a <;> cases b <;> decide
        missing := fun _ => False
        missing_edgeInv := fun _ => Iff.rfl
        tail := fun d => d.2 = false
        tail_iff := by rintro ⟨a, b⟩ _; cases a <;> cases b <;> decide
        tail_missing := fun _ h => False.elim h
        outer := (false, false)
        missing_outer := fun _ h => False.elim h
        locallyFinite := fun _ => Set.toFinite _
        connected := by
          rintro ⟨a, b⟩ ⟨c, d⟩
          have hrot : Relation.ReflTransGen
              (fun x y : Bool × Bool => y = exteriorTestDigonRot x ∨
                y = exteriorTestDigonRot.symm x ∨
                y = exteriorTestDigonFlip x ∨ y = exteriorTestDigonFlip.symm x)
              (a, b) (c, b) := by
            cases a <;> cases c
            · exact .refl
            · exact .single (Or.inl rfl)
            · exact .single (Or.inl rfl)
            · exact .refl
          apply hrot.trans
          cases b <;> cases d
          · exact .refl
          · exact .single (Or.inr (Or.inr (Or.inl rfl)))
          · exact .single (Or.inr (Or.inr (Or.inl rfl)))
          · exact .refl
        acyclic := by
          intro v h
          have hsides : ∀ {v w}, Relation.TransGen
              (rootedLocallyFiniteDirectedStep exteriorTestDigonRot
                exteriorTestDigonFlip (fun _ => False) (fun d => d.2 = false)) v w →
              exteriorTestDigonVertexSide v = false ∧
                exteriorTestDigonVertexSide w = true := by
            intro v w hp
            induction hp with
            | single h => exact digon_directed_step_sides h
            | tail _ h ih =>
              have hs := digon_directed_step_sides h
              exact False.elim (Bool.noConfusion (ih.2.symm.trans hs.1))
          have hs := hsides h
          exact Bool.noConfusion (hs.1.symm.trans hs.2) }
    rootMark := .present (false, false) (fun h => h) rfl }

/-- Helper toward Proposition 5.16: the two incidences at either digon
endpoint represent the same rotation-orbit vertex. -/
theorem exteriorTestDigon_vertex_class (a b : Bool) :
    d39VertexClass exteriorTestDigon (a, b) =
      d39VertexClass exteriorTestDigon (false, b) := by
  cases a
  · rfl
  · apply Quotient.sound
    exact (Equiv.Perm.SameCycle.refl exteriorTestDigonRot (false, b)).apply_left

/-- Helper toward Proposition 5.16: every vertex of the digon lies in
the actual radius-one vertex ball. -/
theorem exteriorTestDigon_vertex_mem (d : exteriorTestDigon.core.D) :
    d39VertexClass exteriorTestDigon d ∈ d39BallVertices exteriorTestDigon 1 := by
  obtain ⟨a, b⟩ := d
  rw [exteriorTestDigon_vertex_class]
  apply (mem_d39BallVertices _ _ _).mpr
  cases b
  · exact .stay .root
  · exact .edge .root ⟨(false, false), rfl, rfl⟩

/-- Helper toward Proposition 5.16: the actual radius-one ball retains
both parallel edges and all four endpoint incidences. -/
theorem exteriorTestDigon_all_darts_retained (d : exteriorTestDigon.core.D) :
    d ∈ d39BallDarts exteriorTestDigon 1 :=
  (mem_d39BallDarts _ _ _).mpr
    ⟨exteriorTestDigon_vertex_mem d,
      exteriorTestDigon_vertex_mem (exteriorTestDigon.core.edgeInv d)⟩

/-- Helper toward Proposition 5.16: every face incidence in the actual
radius-one digon ball is tagged original. -/
theorem exteriorTestDigon_original_eq_univ :
    (d39FacedBall exteriorTestDigon 1 (by decide)).original = Set.univ :=
  d39FacedBall_original_eq_univ_of_all_darts_retained _ _ _
    exteriorTestDigon_all_darts_retained

/-- Helper toward Proposition 5.16: the two ambient digon face cycles
are distinguished by the parity of their edge and endpoint Booleans. -/
theorem exteriorTestDigon_face_parity
    {d e : exteriorTestDigon.core.D}
    (h : Equiv.Perm.SameCycle
      (exteriorTestDigon.core.rot.symm * exteriorTestDigon.core.edgeInv) d e) :
    Bool.xor d.1 d.2 = Bool.xor e.1 e.2 := by
  let : Fintype exteriorTestDigon.core.D := inferInstanceAs (Fintype (Bool × Bool))
  apply exteriorTest_sameCycle_invariant
    (exteriorTestDigon.core.rot.symm * exteriorTestDigon.core.edgeInv)
    (fun d : Bool × Bool => Bool.xor d.1 d.2) (fun d => ?_) h
  obtain ⟨a, b⟩ := d
  cases a <;> cases b <;> rfl

/-- Helper toward Proposition 5.16: the same parity is invariant under
the actual radius-one ball's face successor, since every ambient face is retained. -/
theorem exteriorTestDigon_ball_face_parity
    (d : (d39FacedBall exteriorTestDigon 1 (by decide)).D) :
    let e := (d39FacedBall exteriorTestDigon 1 (by decide)).map.faceSucc d
    Bool.xor e.val.1 e.val.2 = Bool.xor d.val.1 d.val.2 := by
  classical
  have hf := d39Ball_faceSucc_of_contained exteriorTestDigon 1 d
    (fun e _ => exteriorTestDigon_all_darts_retained e)
  change Bool.xor ((d39BallMap exteriorTestDigon 1).faceSucc d).val.1
    ((d39BallMap exteriorTestDigon 1).faceSucc d).val.2 = _
  rw [hf]
  obtain ⟨⟨a, b⟩, hd⟩ := d
  cases a <;> cases b <;> rfl

/-- Helper toward Proposition 5.16: even an actual positive-radius,
all-present ball with every face original admits distinct face-cycle markers.
The identity raw isomorphism does not lift between those marked balls.
This does not identify either marker as a geometric exterior. -/
theorem exists_actual_d39FacedBall_refl_without_external_lift :
    ∃ (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
      (O S : D39BallFaceCycleOrbit (d39FacedBall M r hr)),
      (∀ d, ¬ M.core.missing d) ∧
      (d39FacedBall M r hr).original = Set.univ ∧ O ≠ S ∧
      ¬ ∃ J : D39BallIsoWithExternal ⟨d39FacedBall M r hr, O⟩
        ⟨d39FacedBall M r hr, S⟩,
        J.toD39BallIso = D39BallIso.refl (d39FacedBall M r hr) := by
  let A := d39FacedBall exteriorTestDigon 1 (by decide)
  let d : A.D := ⟨(false, false), exteriorTestDigon_all_darts_retained _⟩
  let e : A.D := ⟨(true, false), exteriorTestDigon_all_darts_retained _⟩
  let O := plBallDartOrbit A d
  let S := plBallDartOrbit A e
  have hne : O ≠ S := by
    intro h
    have hd : d ∈ O.val := Equiv.Perm.SameCycle.rfl
    have he : d ∈ S.val := h ▸ hd
    have hp := exteriorTest_sameCycle_invariant A.map.faceSucc
      (fun x : A.D => Bool.xor x.val.1 x.val.2)
      exteriorTestDigon_ball_face_parity he
    exact Bool.noConfusion hp
  refine ⟨exteriorTestDigon, 1, by decide, O, S, fun _ h => h,
    exteriorTestDigon_original_eq_univ, hne, ?_⟩
  intro h
  exact hne ((d39BallIso_refl_external_lift_iff A O S).mp h)

/-- Helper toward Proposition 5.16: a connected rooted rotation system
admits at most one dart isomorphism to another rooted rotation system. -/
theorem d39BallIso_eq_of_connected {A B : D39FiniteBall}
    (hconn : A.map.IsConnected) (I J : D39BallIso A B) : I = J := by
  have heq : I.toEquiv = J.toEquiv := by
    ext d
    have hp := hconn A.rootDart d
    induction hp with
    | refl => exact I.root_comm.trans J.root_comm.symm
    | @tail x y _ hxy ih =>
      rcases hxy with h | h | h | h
      · rw [h, I.rot_comm, J.rot_comm, ih]
      · apply B.map.rot.injective
        rw [← I.rot_comm, ← J.rot_comm, h, A.map.rot.apply_symm_apply, ih]
      · rw [h, I.edgeInv_comm, J.edgeInv_comm, ih]
      · apply B.map.edgeInv.injective
        rw [← I.edgeInv_comm, ← J.edgeInv_comm, h,
          A.map.edgeInv.apply_symm_apply, ih]
  cases I
  cases J
  cases heq
  rfl

/-- Helper toward Proposition 5.16: all actual positive-radius rooted
ball isomorphisms are unique; changing the chosen isomorphism cannot fix
an exterior mismatch. -/
theorem d39FacedBall_iso_unique (M N : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (I J : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) : I = J := by
  classical
  exact d39BallIso_eq_of_connected (d39BallMap_connected M r hr) I J

/-- Helper toward Proposition 5.16: every raw automorphism of an actual
positive-radius rooted ball fixes every face cycle. -/
theorem d39FacedBall_faceOrbitMap_self (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall M r hr))
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) :
    plBallFaceOrbitMap I O = O := by
  rw [d39FacedBall_iso_unique M M r hr I (D39BallIso.refl _)]
  exact plBallFaceOrbitMap_refl _ O

/-- Helper toward Proposition 5.16: for an actual rooted ball, a marked
self-isomorphism exists exactly when the two external markers agree.
The raw rooted ball has no alternative automorphism that could repair a mismatch. -/
theorem d39FacedBall_external_lift_iff (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (O S : D39BallFaceCycleOrbit (d39FacedBall M r hr)) :
    Nonempty (D39BallIsoWithExternal ⟨d39FacedBall M r hr, O⟩
      ⟨d39FacedBall M r hr, S⟩) ↔ O = S := by
  constructor
  · rintro ⟨J⟩
    exact (d39BallIso_refl_external_lift_iff _ O S).mp
      ⟨J, d39FacedBall_iso_unique M M r hr J.toD39BallIso (D39BallIso.refl _)⟩
  · rintro rfl
    exact ⟨D39BallIsoWithExternal.refl _⟩

/-- Helper toward Proposition 5.16: the all-present actual digon ball
admits two original face-cycle markers between which no marked rooted
isomorphism exists, even though the raw ball classes are identical.
The markers have not been realized as geometric exteriors. -/
theorem exists_actual_d39FacedBall_without_marked_iso :
    ∃ (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
      (O S : D39BallFaceCycleOrbit (d39FacedBall M r hr)),
      (∀ d, ¬ M.core.missing d) ∧
      (d39FacedBall M r hr).original = Set.univ ∧
      ¬ Nonempty (D39BallIsoWithExternal ⟨d39FacedBall M r hr, O⟩
        ⟨d39FacedBall M r hr, S⟩) := by
  obtain ⟨M, r, hr, O, S, hmissing, horiginal, hne, _⟩ :=
    exists_actual_d39FacedBall_refl_without_external_lift
  exact ⟨M, r, hr, O, S, hmissing, horiginal,
    fun h => hne ((d39FacedBall_external_lift_iff M r hr O S).mp h)⟩

/-- Helper toward Proposition 5.16: on two representations of the same
combinatorial rooted map, the proposed transport conclusion is exactly
equality of the two geometrically selected external orbits. No equality
or unbounded-incidence hypothesis is added. -/
theorem d39PLCylinderRepresentation_self_transport_iff
    {M : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation M C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall M r hr)) :
    plBallFaceOrbitMap I
        (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
      (d39FacedBallPLWithExternal M y.drawing r hr).externalOrbit ↔
    (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
      (d39FacedBallPLWithExternal M y.drawing r hr).externalOrbit := by
  have hfix := d39FacedBall_faceOrbitMap_self M r hr I
    (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit
  exact ⟨fun h => hfix.symm.trans h, fun h => hfix.trans h⟩

/-- Helper toward Proposition 5.16: a three-vertex polyline for one
digon edge, with a nonzero real height parameter. -/
@[expose] def exteriorTestDigonPolyline (s : ℝ) : Polyline :=
  ⟨[0, 1 + (s : ℂ) * Complex.I, 2], by simp⟩

/-- Helper toward Proposition 5.16: each candidate digon edge is simple
because its successive real coordinates are strictly increasing. -/
theorem exteriorTestDigonPolyline_simple (s : ℝ) :
    (exteriorTestDigonPolyline s).IsSimple := by
  apply Polyline.isSimple_of_XMonotone
  · norm_num [Polyline.XMonotone, exteriorTestDigonPolyline]
  · norm_num [exteriorTestDigonPolyline]

/-- Helper toward Proposition 5.16: every interior point of a candidate
digon edge has imaginary coordinate a strictly positive multiple of its height. -/
theorem exteriorTestDigonPolyline_interior_height (s : ℝ) {z : ℂ}
    (hz : z ∈ (exteriorTestDigonPolyline s).interior) :
    ∃ t : ℝ, 0 < t ∧ z.im = t * s := by
  have hends : z ≠ 0 ∧ z ≠ 2 := by
    simpa [exteriorTestDigonPolyline, Polyline.start, Polyline.finish,
      not_or] using hz.2
  rcases hz.1 with hzero | ⟨i, hi, hseg⟩
  · exact False.elim (hends.1 hzero)
  · have hi' : i = 0 ∨ i = 1 := by
      change i + 1 < 3 at hi
      omega
    rcases hi' with rfl | rfl
    · change z ∈ segment ℝ 0 (1 + (s : ℂ) * Complex.I) at hseg
      obtain ⟨a, b, _, hb, _, heq⟩ := hseg
      have hbpos : 0 < b := by
        apply lt_of_le_of_ne hb
        intro hbzero
        apply hends.1
        rw [← heq, ← hbzero]
        simp only [smul_zero, zero_smul, add_zero]
      refine ⟨b, hbpos, ?_⟩
      rw [← heq]
      simp
    · change z ∈ segment ℝ (1 + (s : ℂ) * Complex.I) 2 at hseg
      obtain ⟨a, b, ha, _, hab, heq⟩ := hseg
      have hapos : 0 < a := by
        apply lt_of_le_of_ne ha
        intro hazero
        have hb : b = 1 := by linarith
        apply hends.2
        rw [← heq, ← hazero, hb]
        simp only [zero_smul, one_smul, zero_add]
      refine ⟨a, hapos, ?_⟩
      rw [← heq]
      simp

/-- Helper toward Proposition 5.16: the proposed upper and lower digon
edges have disjoint interiors, with their geometric edge identities retained. -/
theorem exteriorTestDigonPolyline_interiors_disjoint :
    Disjoint (exteriorTestDigonPolyline 1).interior
      (exteriorTestDigonPolyline (-1)).interior := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨a, ha, hza⟩ := exteriorTestDigonPolyline_interior_height 1 hz
  obtain ⟨b, hb, hzb⟩ := exteriorTestDigonPolyline_interior_height (-1) hz'
  linarith

/-- Helper toward Proposition 5.16: the ordered dart polylines of the
digon, with opposite darts represented by reversed polylines. -/
@[expose] def exteriorTestDigonArc (d : Bool × Bool) : Polyline :=
  if d.2 then (exteriorTestDigonPolyline (if d.1 then -1 else 1)).reverse
  else exteriorTestDigonPolyline (if d.1 then -1 else 1)

/-- Helper toward Proposition 5.16: the two positions for the geometric
endpoints of the digon. -/
@[expose] def exteriorTestDigonPos (b : Bool) : ℂ := if b then 2 else 0

/-- Helper toward Proposition 5.16: the candidate digon arcs avoid both
endpoint positions in their interiors. -/
theorem exteriorTestDigonArc_avoids_vertices (d : Bool × Bool) (b : Bool) :
    exteriorTestDigonPos b ∉ (exteriorTestDigonArc d).interior := by
  intro h
  have hbase : exteriorTestDigonPos b ∈
      (exteriorTestDigonPolyline (if d.1 then -1 else 1)).interior := by
    cases hd : d.2
    · simpa only [exteriorTestDigonArc, hd, Bool.false_eq_true, ite_false] using h
    · simpa only [exteriorTestDigonArc, hd, ite_true,
        Polyline.interior_reverse_transfer] using h
  obtain ⟨t, ht, heq⟩ := exteriorTestDigonPolyline_interior_height _ hbase
  cases hd : d.1 <;> cases b <;> norm_num [hd, exteriorTestDigonPos] at heq <;> linarith

/-- Helper toward Proposition 5.16: a complete PL drawing of the finite
digon's four dart incidences on its two Boolean vertices. This is geometric
drawing data, not yet a v3 representation by a directed domain map. -/
@[expose] def exteriorTestDigonDrawing :
    PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd where
  flip_involutive := by rintro ⟨a, b⟩; cases b <;> rfl
  flip_ne := by rintro ⟨a, b⟩; cases a <;> cases b <;> decide
  vert_rotation := fun _ => rfl
  pos := exteriorTestDigonPos
  pos_injective := by
    intro a b h
    cases a <;> cases b
    · rfl
    · norm_num [exteriorTestDigonPos] at h
    · norm_num [exteriorTestDigonPos] at h
    · rfl
  arc := exteriorTestDigonArc
  arc_simple := by
    intro d
    cases hd : d.2
    · simpa only [exteriorTestDigonArc, hd, Bool.false_eq_true, ite_false] using
        exteriorTestDigonPolyline_simple (if d.1 then -1 else 1)
    · simpa only [exteriorTestDigonArc, hd, ite_true] using
        Polyline.isSimple_reverse_transfer _
          (exteriorTestDigonPolyline_simple (if d.1 then -1 else 1))
  arc_length := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;>
      norm_num [exteriorTestDigonArc, exteriorTestDigonPolyline, Polyline.reverse]
  arc_start := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  arc_finish := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  arc_flip := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  interior_disjoint := by
    rintro ⟨a, b⟩ ⟨c, f⟩ hne hflip
    have hac : a ≠ c := by
      intro h
      subst c
      cases b <;> cases f
      · exact hne rfl
      · exact hflip rfl
      · exact hflip rfl
      · exact hne rfl
    cases a <;> cases c
    · exact False.elim (hac rfl)
    · cases b <;> cases f <;>
        simpa only [exteriorTestDigonArc, ite_true, Bool.false_eq_true,
          ite_false, Polyline.interior_reverse_transfer] using
          exteriorTestDigonPolyline_interiors_disjoint
    · cases b <;> cases f <;>
        simpa only [exteriorTestDigonArc, ite_true, Bool.false_eq_true,
          ite_false, Polyline.interior_reverse_transfer] using
          exteriorTestDigonPolyline_interiors_disjoint.symm
    · exact False.elim (hac rfl)
  interior_avoids_vertices := exteriorTestDigonArc_avoids_vertices
  locally_finite := fun _ _ => Set.toFinite _
  initial_nonzero := by
    rintro ⟨a, b⟩ h
    have hi := congrArg Complex.im h
    cases a <;> cases b <;>
      norm_num [exteriorTestDigonArc, exteriorTestDigonPolyline, Polyline.reverse,
        Polyline.initialDirection, Polyline.point, Polyline.start] at hi
  initial_arg_injective := by
    rintro ⟨a, b⟩ ⟨c, f⟩ hv harg
    change b = f at hv
    subst f
    have him : (0 ≤ (exteriorTestDigonArc (a, b)).initialDirection.im) ↔
        0 ≤ (exteriorTestDigonArc (c, b)).initialDirection.im :=
      Complex.arg_nonneg_iff.symm.trans
        ((iff_of_eq (congrArg (fun t : ℝ => 0 ≤ t) harg)).trans Complex.arg_nonneg_iff)
    cases a <;> cases c
    · rfl
    · cases b <;> norm_num [exteriorTestDigonArc, exteriorTestDigonPolyline,
        Polyline.reverse, Polyline.initialDirection, Polyline.point, Polyline.start] at him
    · cases b <;> norm_num [exteriorTestDigonArc, exteriorTestDigonPolyline,
        Polyline.reverse, Polyline.initialDirection, Polyline.point, Polyline.start] at him
    · rfl
  rotation_agreement := by
    rintro ⟨a, b⟩
    refine ⟨Set.toFinite _, rfl, rfl, Or.inr ⟨?_, ?_⟩⟩
    · cases a <;> cases b <;> decide
    · rintro ⟨c, f⟩ hv hne
      change f = b at hv
      subst f
      have hc : (c, b) = exteriorTestDigonRot (a, b) := by
        cases a <;> cases c
        · exact False.elim (hne rfl)
        · rfl
        · rfl
        · exact False.elim (hne rfl)
      rw [hc]

/-- Helper toward Proposition 5.16: a finite digon ball on the explicit
four-dart carrier, allowing either parallel edge to carry the root. -/
@[expose] def exteriorTestDigonRawBall (rootEdge : Bool) : D39FiniteBall where
  D := Bool × Bool
  map :=
    { edgeInv := exteriorTestDigonFlip
      edgeInv_invol := by rintro ⟨a, b⟩; cases b <;> rfl
      edgeInv_ne := by rintro ⟨a, b⟩; cases a <;> cases b <;> decide
      rot := exteriorTestDigonRot }
  missing := fun _ => False
  tail := fun d => d.2 = false
  rootDart := (rootEdge, false)
  original := Set.univ
  original_closed := fun _ => Iff.rfl

/-- Helper toward Proposition 5.16: changing which parallel edge carries
the root admits the dart relabelling that exchanges those edges. -/
@[expose] def exteriorTestDigonSwapIso :
    D39BallIso (exteriorTestDigonRawBall true) (exteriorTestDigonRawBall false) where
  toEquiv := exteriorTestDigonRot
  rot_comm := fun _ => rfl
  edgeInv_comm := fun _ => rfl
  missing_iff := fun _ => Iff.rfl
  tail_iff := fun _ => Iff.rfl
  root_comm := rfl
  original_iff := fun _ => Iff.rfl

/-- Helper toward Proposition 5.16: the second complete PL drawing
exchanges the upper and lower geometric arcs while retaining the dart carrier. -/
@[expose] def exteriorTestDigonSwappedDrawing :
    PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd :=
  plDrawingRelabel exteriorTestDigonRot (Equiv.refl Bool)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) exteriorTestDigonDrawing

/-- Helper toward Proposition 5.16: all four incidences of the drawn
digon are connected by rotations and edge reversals. -/
theorem exteriorTestDigon_eqvGen_connected :
    ∀ d e : Bool × Bool, Relation.EqvGen
      (fun x y => exteriorTestDigonRot x = y ∨ exteriorTestDigonFlip x = y) d e := by
  rintro ⟨a, b⟩ ⟨c, f⟩
  have hr : Relation.EqvGen
      (fun x y => exteriorTestDigonRot x = y ∨ exteriorTestDigonFlip x = y)
      (a, b) (c, b) := by
    cases a <;> cases c
    · exact .refl _
    · exact .rel _ _ (Or.inl rfl)
    · exact .rel _ _ (Or.inl rfl)
    · exact .refl _
  apply hr.trans
  cases b <;> cases f
  · exact .refl _
  · exact .rel _ _ (Or.inr rfl)
  · exact .rel _ _ (Or.inr rfl)
  · exact .refl _

/-- Helper toward Proposition 5.16: exchanging the two parallel edges
fixes no digon face orbit. This concerns the actual orbit sets, not labels. -/
theorem exteriorTestDigonSwapIso_no_fixed_orbit
    (O : D39BallFaceCycleOrbit (exteriorTestDigonRawBall true)) :
    plBallFaceOrbitMap exteriorTestDigonSwapIso O ≠ O := by
  intro h
  obtain ⟨d, hd⟩ := O.property
  have hdO : d ∈ O.val := hd ▸ Equiv.Perm.SameCycle.rfl
  have hrd : exteriorTestDigonRot d ∈ O.val := by
    rw [← h]
    exact ⟨d, hdO, rfl⟩
  have hcycle : Equiv.Perm.SameCycle
      (exteriorTestDigonRot.symm * exteriorTestDigonFlip) d (exteriorTestDigonRot d) := by
    rw [hd] at hrd
    exact hrd
  have hp := exteriorTestDigon_face_parity hcycle
  obtain ⟨a, b⟩ := d
  cases a <;> cases b <;> exact Bool.noConfusion hp

/-- Helper toward Proposition 5.16: the two complete PL digon drawings
have different geometrically selected unbounded face orbits. The roots used
to package the finite carriers do not enter the geometric exterior selector.
This still supplies no v3 representation of either directed geometric map. -/
theorem exteriorTestDigon_drawings_distinct_externalOrbits :
    plExternalOrbit (exteriorTestDigonRawBall true) Prod.snd exteriorTestDigonDrawing
        (fun b => ⟨(false, b), rfl⟩) exteriorTestDigon_eqvGen_connected ≠
      plExternalOrbit (exteriorTestDigonRawBall false) Prod.snd
        exteriorTestDigonSwappedDrawing (fun b => ⟨(false, b), rfl⟩)
        exteriorTestDigon_eqvGen_connected := by
  let O := plExternalOrbit (exteriorTestDigonRawBall true) Prod.snd
    exteriorTestDigonDrawing (fun b => ⟨(false, b), rfl⟩)
    exteriorTestDigon_eqvGen_connected
  have hu : ¬ Bornology.IsBounded
      ((exteriorTestDigonRawBall true).plOrbitFace Prod.snd exteriorTestDigonDrawing
        (fun b => ⟨(false, b), rfl⟩) O).val :=
    (plExternalOrbit_eq_iff _ _ _ _ _ O).mp rfl
  have hf := plDrawingRelabel_orbitFace exteriorTestDigonSwapIso Prod.snd Prod.snd
    exteriorTestDigonDrawing (Equiv.refl Bool) (fun _ => rfl)
    (fun b => ⟨(false, b), rfl⟩) (fun b => ⟨(false, b), rfl⟩) O
  have htransport : plBallFaceOrbitMap exteriorTestDigonSwapIso O =
      plExternalOrbit (exteriorTestDigonRawBall false) Prod.snd
        exteriorTestDigonSwappedDrawing (fun b => ⟨(false, b), rfl⟩)
        exteriorTestDigon_eqvGen_connected := by
    apply (plExternalOrbit_eq_iff _ _ _ _ _ _).mpr
    change ¬ Bornology.IsBounded
      ((exteriorTestDigonRawBall false).plOrbitFace Prod.snd
        (plDrawingRelabel exteriorTestDigonSwapIso.toEquiv (Equiv.refl Bool)
          exteriorTestDigonSwapIso.edgeInv_comm exteriorTestDigonSwapIso.rot_comm
          (fun _ => rfl) exteriorTestDigonDrawing)
        (fun b => ⟨(false, b), rfl⟩)
        (plBallFaceOrbitMap exteriorTestDigonSwapIso O)).val
    exact fun hb => hu (hf ▸ hb)
  intro heq
  exact exteriorTestDigonSwapIso_no_fixed_orbit O (htransport.trans heq.symm)

/-- Helper toward Proposition 5.16: identify the digon's actual
rotation-orbit vertices with its two Boolean endpoint identities. -/
@[expose] def exteriorTestDigonVertexEquiv :
    RootedLocallyFiniteVertex exteriorTestDigon.core.D exteriorTestDigon.core.rot ≃ Bool where
  toFun := exteriorTestDigonVertexSide
  invFun b := d39VertexClass exteriorTestDigon (false, b)
  left_inv := by
    intro v
    refine Quotient.inductionOn v ?_
    rintro ⟨a, b⟩
    exact (exteriorTestDigon_vertex_class a b).symm
  right_inv := fun _ => rfl

/-- Helper toward Proposition 5.16: the upper/lower drawing on the
exact ambient vertex carrier required by PLCylinderBall.Representation. -/
@[expose] def exteriorTestDigonAmbientDrawing :
    PLDrawing exteriorTestDigon.core.D
      (RootedLocallyFiniteVertex exteriorTestDigon.core.D exteriorTestDigon.core.rot)
      exteriorTestDigon.core.edgeInv exteriorTestDigon.core.rot
      (d39VertexClass exteriorTestDigon) :=
  plDrawingRelabel (Equiv.refl (Bool × Bool)) exteriorTestDigonVertexEquiv.symm
    (fun _ => rfl) (fun _ => rfl)
    (fun d => (exteriorTestDigon_vertex_class d.1 d.2).symm) exteriorTestDigonDrawing

/-- Helper toward Proposition 5.16: the edge-exchanged drawing on the
same exact ambient carrier, also without assuming any v3 data. -/
@[expose] def exteriorTestDigonSwappedAmbientDrawing :
    PLDrawing exteriorTestDigon.core.D
      (RootedLocallyFiniteVertex exteriorTestDigon.core.D exteriorTestDigon.core.rot)
      exteriorTestDigon.core.edgeInv exteriorTestDigon.core.rot
      (d39VertexClass exteriorTestDigon) :=
  plDrawingRelabel (Equiv.refl (Bool × Bool)) exteriorTestDigonVertexEquiv.symm
    (fun _ => rfl) (fun _ => rfl)
    (fun d => (exteriorTestDigon_vertex_class d.1 d.2).symm) exteriorTestDigonSwappedDrawing

/-- Helper toward Proposition 5.16: forget the subtype proof from the
actual fully retained radius-one digon ball without losing a dart. -/
@[expose] def exteriorTestDigonBallDartEquiv :
    (d39FacedBall exteriorTestDigon 1 (by decide)).D ≃ Bool × Bool where
  toFun := Subtype.val
  invFun d := ⟨d, exteriorTestDigon_all_darts_retained d⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Helper toward Proposition 5.16: the explicit four-dart digon is
isomorphic to the actual fully retained radius-one faced ball. -/
@[expose] def exteriorTestDigonBallIsoRaw :
    D39BallIso (d39FacedBall exteriorTestDigon 1 (by decide))
      (exteriorTestDigonRawBall false) := by
  classical
  let A := d39FacedBall exteriorTestDigon 1 (by decide)
  have hf (d : A.D) : (A.map.faceSucc d).val =
      exteriorTestDigonRot.symm (exteriorTestDigonFlip d.val) :=
    d39Ball_faceSucc_of_contained exteriorTestDigon 1 d
      (fun e _ => exteriorTestDigon_all_darts_retained e)
  have hri (d : A.D) : (A.map.rot.symm d).val = exteriorTestDigonRot.symm d.val := by
    have h := hf (A.map.edgeInv d)
    have hid : A.map.faceSucc (A.map.edgeInv d) = A.map.rot.symm d := by
      change A.map.rot.symm (A.map.edgeInv (A.map.edgeInv d)) = _
      rw [A.map.edgeInv_invol]
    rw [hid] at h
    change (A.map.rot.symm d).val =
      exteriorTestDigonRot.symm (exteriorTestDigonFlip (exteriorTestDigonFlip d.val)) at h
    have hinv : exteriorTestDigonFlip (exteriorTestDigonFlip d.val) = d.val := by
      obtain ⟨⟨a, b⟩, hd⟩ := d
      cases b <;> rfl
    exact h.trans (congrArg exteriorTestDigonRot.symm hinv)
  refine
    { toEquiv := exteriorTestDigonBallDartEquiv
      rot_comm := ?_
      edgeInv_comm := fun _ => rfl
      missing_iff := fun _ => Iff.rfl
      tail_iff := fun _ => Iff.rfl
      root_comm := rfl
      original_iff := ?_ }
  · intro d
    apply exteriorTestDigonRot.symm.injective
    change exteriorTestDigonRot.symm (A.map.rot d).val =
      exteriorTestDigonRot.symm (exteriorTestDigonRot d.val)
    exact ((hri (A.map.rot d)).symm.trans
      (congrArg Subtype.val (A.map.rot.symm_apply_apply d))).trans
      (exteriorTestDigonRot.symm_apply_apply d.val).symm
  · intro d
    exact ⟨fun _ e _ => exteriorTestDigon_all_darts_retained e,
      fun _ => Set.mem_univ _⟩

/-- Helper toward Proposition 5.16: a genuine relabelling of a PL drawing
transports its selected exterior. Unlike independent drawings, this uses
the explicitly constructed relabelled drawing and needs no common-exterior premise. -/
theorem plDrawingRelabel_selected_external_transport
    {V W : Type*} [Finite V] [Finite W] {A B : D39FiniteBall}
    (I : D39BallIso A B) (vert : A.D → V) (vert' : B.D → W)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (f : V ≃ W) (hv : ∀ d, f (vert d) = vert' (I.toEquiv d))
    (hvert : Function.Surjective vert) (hvert' : Function.Surjective vert')
    (hc : ∀ d e : A.D, Relation.EqvGen
      (fun x y => A.map.rot x = y ∨ A.map.edgeInv x = y) d e)
    (hc' : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    plBallFaceOrbitMap I (plExternalOrbit A vert P hvert hc) =
      plExternalOrbit B vert'
        (plDrawingRelabel I.toEquiv f I.edgeInv_comm I.rot_comm hv P) hvert' hc' := by
  apply (plExternalOrbit_eq_iff _ _ _ _ _ _).mpr
  have hu := (plExternalOrbit_eq_iff A vert P hvert hc
    (plExternalOrbit A vert P hvert hc)).mp rfl
  have hf := plDrawingRelabel_orbitFace I vert vert' P f hv hvert hvert'
    (plExternalOrbit A vert P hvert hc)
  exact fun hb => hu (hf ▸ hb)

/-- Helper toward Proposition 5.16: compute both selected exteriors
using the same rooted raw ball; changing the root used in the first
selector does not change its unbounded orbit. -/
theorem exteriorTestDigon_same_raw_ball_distinct_externalOrbits :
    plExternalOrbit (exteriorTestDigonRawBall false) Prod.snd exteriorTestDigonDrawing
        (fun b => ⟨(false, b), rfl⟩) exteriorTestDigon_eqvGen_connected ≠
      plExternalOrbit (exteriorTestDigonRawBall false) Prod.snd
        exteriorTestDigonSwappedDrawing (fun b => ⟨(false, b), rfl⟩)
        exteriorTestDigon_eqvGen_connected := by
  have hroot : plExternalOrbit (exteriorTestDigonRawBall true) Prod.snd
      exteriorTestDigonDrawing (fun b => ⟨(false, b), rfl⟩)
      exteriorTestDigon_eqvGen_connected =
      plExternalOrbit (exteriorTestDigonRawBall false) Prod.snd
        exteriorTestDigonDrawing (fun b => ⟨(false, b), rfl⟩)
        exteriorTestDigon_eqvGen_connected := by
    apply (plExternalOrbit_eq_iff (exteriorTestDigonRawBall false) Prod.snd
      exteriorTestDigonDrawing (fun b => ⟨(false, b), rfl⟩)
      exteriorTestDigon_eqvGen_connected _).mpr
    exact (plExternalOrbit_eq_iff (exteriorTestDigonRawBall true) Prod.snd
      exteriorTestDigonDrawing (fun b => ⟨(false, b), rfl⟩)
      exteriorTestDigon_eqvGen_connected _).mp rfl
  exact fun h => exteriorTestDigon_drawings_distinct_externalOrbits (hroot.trans h)




theorem exists_actual_ball_plDrawings_with_distinct_externalOrbits :
    ∃ (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
      (vert : (d39FacedBall M r hr).D → Bool)
      (P Q : PLDrawing (d39FacedBall M r hr).D Bool
        (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).map.rot vert)
      (hv : Function.Surjective vert),
      plExternalOrbit (d39FacedBall M r hr) vert P hv (d39FacedBall_connected M r hr) ≠
        plExternalOrbit (d39FacedBall M r hr) vert Q hv (d39FacedBall_connected M r hr) := by
  let A := d39FacedBall exteriorTestDigon 1 (by decide)
  let I := exteriorTestDigonBallIsoRaw.symm
  let vert : A.D → Bool := fun d => d.val.2
  have hv : ∀ d, (Equiv.refl Bool) d.2 = vert (I.toEquiv d) := fun _ => rfl
  have hsurj : Function.Surjective vert := fun b =>
    ⟨⟨(false, b), exteriorTestDigon_all_darts_retained _⟩, rfl⟩
  let P := plDrawingRelabel I.toEquiv (Equiv.refl Bool)
    I.edgeInv_comm I.rot_comm hv exteriorTestDigonDrawing
  let Q := plDrawingRelabel I.toEquiv (Equiv.refl Bool)
    I.edgeInv_comm I.rot_comm hv exteriorTestDigonSwappedDrawing
  have hp := plDrawingRelabel_selected_external_transport I Prod.snd vert
    exteriorTestDigonDrawing (Equiv.refl Bool) hv (fun b => ⟨(false, b), rfl⟩)
    hsurj exteriorTestDigon_eqvGen_connected (d39FacedBall_connected exteriorTestDigon 1 (by decide))
  have hq := plDrawingRelabel_selected_external_transport I Prod.snd vert
    exteriorTestDigonSwappedDrawing (Equiv.refl Bool) hv (fun b => ⟨(false, b), rfl⟩)
    hsurj exteriorTestDigon_eqvGen_connected (d39FacedBall_connected exteriorTestDigon 1 (by decide))
  refine ⟨exteriorTestDigon, 1, by decide, vert, P, Q, hsurj, ?_⟩
  intro heq
  exact exteriorTestDigon_same_raw_ball_distinct_externalOrbits
    (plBallFaceOrbitMap_injective I (hp.trans (heq.trans hq.symm)))


























































end DirectedDistances.PaperProofs.Section5

end
