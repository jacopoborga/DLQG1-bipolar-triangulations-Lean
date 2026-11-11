module

public import DirectedDistances.PaperProofs.Section5.Prop516RootedLawConvergence
public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.PaperProofs.Section3.BSTopologyConcreteSystem

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory

attribute [local instance] Classical.propDecidable

local instance instMeasurableSpaceD39BallClass : MeasurableSpace D39BallClass := ⊤

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16;
not a paper result. Reinterpret a faced framed ball as a local topology finite ball. -/
def facedFramedBallToD39FiniteBall (B : FacedFramedBall) : D39FiniteBall where
  D := B.toFramedBall.D
  instFintypeD := B.toFramedBall.instFintypeD
  instDecidableEqD := B.toFramedBall.instDecidableEqD
  map := B.toFramedBall.map.toCombinatorialMap
  missing := B.toFramedBall.map.missing
  tail := B.toFramedBall.map.tail
  rootDart := B.toFramedBall.frameEdgeDart
  original := B.original
  original_closed := by
    intro d
    exact B.original_closed d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16;
not a paper result. Faced ball isomorphisms induce local topology finite ball isomorphisms. -/
def facedFramedBallIsoToD39BallIso {B C : FacedFramedBall}
    (I : FacedFramedBallIso B C) :
    D39BallIso (facedFramedBallToD39FiniteBall B)
      (facedFramedBallToD39FiniteBall C) where
  toEquiv := I.toFramedBallIso.mapIso.toEquiv
  rot_comm := I.toFramedBallIso.mapIso.rot_comm
  edgeInv_comm := I.toFramedBallIso.mapIso.edgeInv_comm
  missing_iff := I.toFramedBallIso.mapIso.missing_iff
  tail_iff := I.toFramedBallIso.mapIso.tail_iff
  root_comm := I.toFramedBallIso.frameEdge_comm
  original_iff := I.original_iff

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16;
not a paper result. Transport a faced ball class to its local topology ball class. -/
@[expose] def facedFramedBallClassToD39BallClass :
    FacedFramedBallClass → D39BallClass :=
  Quotient.lift
    (fun B => Quotient.mk D39FiniteBall.setoid (facedFramedBallToD39FiniteBall B))
    (by
      intro B C h
      obtain ⟨I⟩ := h
      exact Quotient.sound ⟨facedFramedBallIsoToD39BallIso I⟩)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16;
not a paper result. The local topology ball of a rooted planar map is transported from its -/
theorem d39BallClass_eq_facedFramedBallClassToD39BallClass
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) :
    d39BallClass M.toRootedLocallyFiniteMap.toD39RootedMap (r + 1)
        (Nat.succ_pos r) =
      facedFramedBallClassToD39BallClass
        (rootedLocallyFiniteFacedBallClass r M) := by
  classical
  change d39BallClass _ _ _ =
    Quotient.mk D39FiniteBall.setoid
      (facedFramedBallToD39FiniteBall
        (rootedLocallyFiniteFacedBall M (r + 1) (by omega)))
  apply Quotient.sound
  refine ⟨?_⟩
  let A := M.toRootedLocallyFiniteMap
  let n := r + 1
  let hD := d39BallDarts_toD39RootedMap A n
  let E :
      {d : A.D // d ∈ rootedLocallyFiniteBallDarts A n} ≃
        {d : A.D // d ∈ d39BallDarts A.toD39RootedMap n} := {
    toFun := fun d => ⟨d.1, hD.symm ▸ d.2⟩
    invFun := fun d => ⟨d.1, hD ▸ d.2⟩
    left_inv := by intro d; apply Subtype.ext; rfl
    right_inv := by intro d; apply Subtype.ext; rfl }
  have hrotVal (d : {d : A.D // d ∈ d39BallDarts A.toD39RootedMap n}) :
      ((d39BallMap A.toD39RootedMap n).rot d).1 =
        ((rootedLocallyFiniteBallCombinatorialMap A n).rot
          (⟨d.1, hD ▸ d.2⟩ : {d : A.D // d ∈ rootedLocallyFiniteBallDarts A n})).1 := by
    exact DirectedDistances.PaperProofs.Section3.cyclicFirstReturn_map_of_equiv
      (A.toD39RootedMap.core.rot) A.rot
      (d39BallDarts A.toD39RootedMap n)
      (rootedLocallyFiniteBallDarts A n) (Equiv.refl A.D)
      (by
        intro x
        exact Iff.of_eq (congrArg (fun S : Finset A.D => x ∈ S) hD))
      (by intro x; rfl)
      (by
        intro x
        obtain ⟨k, hk, heq⟩ := d39RotationReturn A.toD39RootedMap x.1
        exact ⟨k, hk, by rw [heq]; exact x.2⟩)
      (by
        intro x
        obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn A x.1
        exact ⟨k, hk, by rw [heq]; exact x.2⟩) d
  change D39BallIso
    (d39FacedBall A.toD39RootedMap n (by omega))
    (facedFramedBallToD39FiniteBall
      (rootedLocallyFiniteFacedBall M n (by omega)))
  refine {
    toEquiv := E.symm
    rot_comm := ?_
    edgeInv_comm := ?_
    missing_iff := ?_
    tail_iff := ?_
    root_comm := ?_
    original_iff := ?_ }
  · intro d
    apply Subtype.ext
    change ((d39BallMap A.toD39RootedMap n).rot d).1 =
      ((rootedLocallyFiniteBallCombinatorialMap A n).rot (E.symm d)).1
    simpa [E] using hrotVal d
  · intro d
    apply Subtype.ext
    rfl
  · intro d
    exact Iff.rfl
  · intro d
    exact Iff.rfl
  · apply Subtype.ext
    rfl
  · intro d
    change rootedLocallyFiniteBallContainsOriginalFace A n (E.symm d).1 ↔
      d39BallContainsOriginalFace A.toD39RootedMap n d.1
    have hval : (E.symm d).1 = d.1 := rfl
    rw [hval]
    unfold rootedLocallyFiniteBallContainsOriginalFace d39BallContainsOriginalFace
    change (∀ e : A.D, Equiv.Perm.SameCycle (A.rot.symm * A.edgeInv) d.1 e →
        e ∈ rootedLocallyFiniteBallDarts A n) ↔
      ∀ e : A.D, Equiv.Perm.SameCycle (A.rot.symm * A.edgeInv) d.1 e →
        e ∈ d39BallDarts A.toD39RootedMap n
    constructor
    · intro h e he
      exact hD.symm ▸ h e he
    · intro h e he
      exact hD ▸ h e he

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16;
not a paper result. Every local topology ball coordinate of the UIBHBOT code map is -/
theorem measurable_uibhbotD39BallClass (r : ℕ) :
    letI : MeasurableSpace D39BallClass := ⊤
    Measurable (fun W : ℤ → Fin 3 =>
      d39BallClass
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
        (r + 1) (Nat.succ_pos r)) := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  have hface : Measurable (fun W : ℤ → Fin 3 =>
      rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W)) := by
    have hmap : Measurable uibhbotRootedPlanarMapOfCode :=
      measurable_uibhbotRootedPlanarMapOfCode
    have hcoord : Measurable (rootedLocallyFiniteFacedBallClass r) := by
      apply measurable_iff_comap_le.mpr
      let S := rootedLocallyFiniteFacedBallSystem
      change MeasurableSpace.comap (S.ballClass r) ⊤ ≤
        @borel S.Object (bsLocalDistanceTopologyGeneric S)
      rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic S]
      exact le_iSup_of_le r le_rfl
    exact hcoord.comp hmap
  have htrans : Measurable facedFramedBallClassToD39BallClass :=
    measurable_of_countable _
  have hcomp := htrans.comp hface
  have hEq : (fun W : ℤ → Fin 3 => facedFramedBallClassToD39BallClass
      (rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W))) =
      (fun W : ℤ → Fin 3 => d39BallClass
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
        (r + 1) (Nat.succ_pos r)) := by
    funext W
    exact (d39BallClass_eq_facedFramedBallClassToD39BallClass
      (uibhbotRootedPlanarMapOfCode W) r).symm
  change Measurable (fun W : ℤ → Fin 3 => facedFramedBallClassToD39BallClass
    (rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W))) at hcomp
  rw [← hEq]
  exact hcomp

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16;
not a paper result. The UIBHBOT code map is measurable into the Borel space of -/
theorem measurable_uibhbotD39RootedMapOfCode :
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    Measurable (fun W : ℤ → Fin 3 =>
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap) := by
  classical
  apply (measurable_into_iff_ballClass_generic d39RootedBallSystem
    (fun W : ℤ → Fin 3 =>
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)).2
  intro r
  have hEq : d39RootedBallSystem.ballClass r ∘
      (fun W : ℤ → Fin 3 =>
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap) =
      (fun W : ℤ → Fin 3 => d39BallClass
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
        (r + 1) (Nat.succ_pos r)) := by
    funext W
    rfl
  rw [hEq]
  exact measurable_uibhbotD39BallClass r

end DirectedDistances.PaperProofs.Section5
