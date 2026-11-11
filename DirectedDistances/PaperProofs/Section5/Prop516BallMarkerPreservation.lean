/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLExteriorTransport
public import DirectedDistances.PaperProofs.Section5.Prop516PLCylinderBall

/-! # Missing-edge and face-orbit tests for the selected ball exterior

Helpers toward Proposition 5.16, using Definition 3.8 and author rulings
transport of a combinatorial test from identification of the geometric
exterior. No general exterior-preservation premise is assumed here. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16: the face-successor orbit through a
specified dart, retaining that incidence rather than an arbitrary marker. -/
@[expose] def plBallDartOrbit (A : D39FiniteBall) (d : A.D) :
    D39BallFaceCycleOrbit A :=
  ⟨{e | A.map.faceSucc.SameCycle d e}, d, rfl⟩

/-- Helper toward Proposition 5.16: an isomorphism carries the orbit through
a dart to the orbit through its image, using rotation and edge reversal. -/
theorem plBallFaceOrbitMap_dartOrbit {A B : D39FiniteBall}
    (I : D39BallIso A B) (d : A.D) :
    plBallFaceOrbitMap I (plBallDartOrbit A d) =
      plBallDartOrbit B (I.toEquiv d) := by
  apply (plBallFaceOrbitMap_eq_iff I _ _).mpr
  intro e
  exact (plBallFaceSameCycle_iff I d e).symm

/-- Helper toward Proposition 5.16: the orbit through the ordered root
is preserved without any hypothesis about its geometric location. -/
theorem plBallFaceOrbitMap_rootDartOrbit {A B : D39FiniteBall}
    (I : D39BallIso A B) :
    plBallFaceOrbitMap I (plBallDartOrbit A A.rootDart) =
      plBallDartOrbit B B.rootDart := by
  exact (plBallFaceOrbitMap_dartOrbit I A.rootDart).trans
    (congrArg (plBallDartOrbit B) I.root_comm)

/-- Helper toward Proposition 5.16: containing a missing dart is an
isomorphism-invariant test on face orbits. This does not say that the test
selects exactly one orbit or identifies the geometric exterior. -/
theorem plBallFaceOrbitMap_contains_missing_iff {A B : D39FiniteBall}
    (I : D39BallIso A B) (O : D39BallFaceCycleOrbit A) :
    (∃ e ∈ (plBallFaceOrbitMap I O).val, B.missing e) ↔
      ∃ d ∈ O.val, A.missing d := by
  constructor
  · rintro ⟨e, he, hmissing⟩
    obtain ⟨d, hd, rfl⟩ := he
    exact ⟨d, hd, (I.missing_iff d).mp hmissing⟩
  · rintro ⟨d, hd, hmissing⟩
    exact ⟨I.toEquiv d, ⟨d, hd, rfl⟩, (I.missing_iff d).mpr hmissing⟩

/-- Helper toward Proposition 5.16: an all-present ambient map supplies no
missing dart in any orbit of any positive-radius faced ball. -/
theorem d39FacedBall_no_missing_orbit_of_all_present
    (M : D39RootedMap) (hpresent : ∀ d, ¬ M.core.missing d)
    (r : ℕ) (hr : 0 < r) (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) :
    ¬ ∃ d ∈ O.val, (d39FacedBall M r hr).missing d := by
  rintro ⟨d, _, hd⟩
  exact hpresent d.val hd

/-- Helper toward Proposition 5.16: when every ambient dart is retained,
every face incidence is tagged original, including the selected exterior.
Thus this tag does not distinguish faces in a completely retained map. -/
theorem d39FacedBall_original_eq_univ_of_all_darts_retained
    (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (hretain : ∀ d, d ∈ d39BallDarts M r) :
    (d39FacedBall M r hr).original = Set.univ := by
  apply Set.eq_univ_of_forall
  intro d e _
  exact hretain e

/-- Helper toward Proposition 5.16: a missing edge whose two darts lie in
different face orbits gives two distinct orbits containing missing darts.
The missing tag belongs to the whole geometric edge, not one chosen side. -/
theorem d39FacedBall_two_missing_orbits_of_not_sameCycle
    (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D)
    (hd : (d39FacedBall M r hr).missing d)
    (hsep : ¬ (d39FacedBall M r hr).map.faceSucc.SameCycle d
      ((d39FacedBall M r hr).map.edgeInv d)) :
    ∃ O S : D39BallFaceCycleOrbit (d39FacedBall M r hr), O ≠ S ∧
      (∃ e ∈ O.val, (d39FacedBall M r hr).missing e) ∧
      (∃ e ∈ S.val, (d39FacedBall M r hr).missing e) := by
  classical
  let A := d39FacedBall M r hr
  let e := A.map.edgeInv d
  refine ⟨plBallDartOrbit A d, plBallDartOrbit A e, ?_,
    ⟨d, Equiv.Perm.SameCycle.rfl, hd⟩,
    ⟨e, Equiv.Perm.SameCycle.rfl, ?_⟩⟩
  · intro h
    have he : e ∈ (plBallDartOrbit A e).val := Equiv.Perm.SameCycle.rfl
    rw [← h] at he
    exact hsep he
  · exact (d39BallMissing_edgeInv M r d).mp hd

/-- Helper toward Proposition 5.16: a missing edge with distinct left and
right face orbits refutes uniqueness of the proposed missing-dart selector
on the actual positive-radius faced ball. -/
theorem d39FacedBall_not_existsUnique_missing_orbit_of_not_sameCycle
    (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D)
    (hd : (d39FacedBall M r hr).missing d)
    (hsep : ¬ (d39FacedBall M r hr).map.faceSucc.SameCycle d
      ((d39FacedBall M r hr).map.edgeInv d)) :
    ¬ ∃! O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      ∃ e ∈ O.val, (d39FacedBall M r hr).missing e := by
  obtain ⟨O, S, hOS, hO, hS⟩ :=
    d39FacedBall_two_missing_orbits_of_not_sameCycle M r hr d hd hsep
  rintro ⟨T, _, hunique⟩
  exact hOS ((hunique O hO).trans (hunique S hS).symm)

/-- Helper toward Proposition 5.16: two actual face orbits which contain
the same dart are equal. -/
theorem plBallFaceCycleOrbit_eq_of_mem {A : D39FiniteBall}
    (O S : D39BallFaceCycleOrbit A) (d : A.D)
    (hdO : d ∈ O.val) (hdS : d ∈ S.val) : O = S := by
  obtain ⟨a, ha⟩ := O.property
  obtain ⟨b, hb⟩ := S.property
  have had : A.map.faceSucc.SameCycle a d := by
    simpa only [ha, Set.mem_ofPred_eq] using hdO
  have hbd : A.map.faceSucc.SameCycle b d := by
    simpa only [hb, Set.mem_ofPred_eq] using hdS
  apply Subtype.ext
  rw [ha, hb]
  ext e
  exact ⟨fun he => hbd.trans (had.symm.trans he),
    fun he => had.trans (hbd.symm.trans he)⟩

/-- Helper toward Proposition 5.16: exact orbit transport is equivalent
to one shared incidence. This identifies the extra datum needed after
rotation and reversal already supply transport of all face cycles. -/
theorem plBallFaceOrbitMap_eq_iff_exists_common_dart {A B : D39FiniteBall}
    (I : D39BallIso A B) (O : D39BallFaceCycleOrbit A)
    (S : D39BallFaceCycleOrbit B) :
    plBallFaceOrbitMap I O = S ↔
      ∃ d ∈ O.val, I.toEquiv d ∈ S.val := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := O.property
    have hdO : d ∈ O.val := hd ▸ Equiv.Perm.SameCycle.rfl
    exact ⟨d, hdO, ((plBallFaceOrbitMap_eq_iff I O S).mp h d).mpr hdO⟩
  · rintro ⟨d, hdO, hdS⟩
    exact plBallFaceCycleOrbit_eq_of_mem _ _ (I.toEquiv d)
      ((plBallFaceOrbitMap_mem_iff I O d).mpr hdO) hdS

/-- Helper toward Proposition 5.16: on precisely the cylinder module's
representation carrier, exterior transport is equivalent to finding one
dart whose left face is unbounded in both restricted drawings. This is an
equivalence identifying an open obligation, not an assumption of it. -/
theorem d39PLRepresentation_external_transport_iff_exists_unbounded_dart
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) :
    plBallFaceOrbitMap I
        (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
      (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit ↔
    ∃ d : (d39FacedBall M r hr).D,
      (¬ Bornology.IsBounded
        ((d39FacedBall M r hr).plDartFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) d).val) ∧
      ¬ Bornology.IsBounded
        ((d39FacedBall N r hr).plDartFace
          (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N y.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
          (I.toEquiv d)).val := by
  refine (plBallFaceOrbitMap_eq_iff_exists_common_dart I
    (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit
    (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit).trans ?_
  apply exists_congr
  intro d
  exact and_congr
    (d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace M x.drawing r hr d)
    (d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace N y.drawing r hr
      (I.toEquiv d))
























































































end DirectedDistances.PaperProofs.Section5

end
