/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516BallMarkerPreservation
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedHball

/-! using the induced plane balls of Definition 3.8
a combinatorial face orbit functorially. Its identification with the finite
drawing's exterior is proved only when that same ambient drawing has an
unbounded face bordering the reversed root. No paper theorem is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

namespace Prop516RootExteriorEncoding

/-- Helper toward Proposition 5.16: mark the face orbit through the reversal
of the ordered root, without asserting that this orbit is geometric exterior. -/
@[expose] def rootBall (A : D39FiniteBall) : D39FiniteBallWithExternal :=
  ⟨A, plBallDartOrbit A (A.map.edgeInv A.rootDart)⟩

/-- Helper toward Proposition 5.16: root and reversal preservation carry the
reversed-root face orbit to the corresponding orbit in the target ball. -/
@[expose] def rootBallIso {A B : D39FiniteBall} (I : D39BallIso A B) :
    D39BallIsoWithExternal (rootBall A) (rootBall B) where
  toD39BallIso := I
  external_iff := (plBallFaceOrbitMap_eq_iff I _ _).mp <|
    (plBallFaceOrbitMap_dartOrbit I _).trans <|
      congrArg (plBallDartOrbit B)
        ((I.edgeInv_comm A.rootDart).trans
          (congrArg B.map.edgeInv I.root_comm))

/-- Helper toward Proposition 5.16: the reversed-root marking descends to
unmarked ball classes by the checked marked isomorphism. -/
@[expose] def rootLift : D39BallClass → ExteriorMarkedBallClass :=
  Quotient.lift
    (fun A => Quotient.mk exteriorMarkedBallSetoid (rootBall A))
    (fun _ _ ⟨I⟩ => Quotient.sound ⟨rootBallIso I⟩)

/-- Helper toward Proposition 5.16: forgetting the reversed-root marker
recovers precisely the original ball class. -/
theorem rootLift_forget (q : D39BallClass) : (rootLift q).forget = q := by
  induction q using Quotient.inductionOn with
  | _ A => rfl

/-- Helper toward Proposition 5.16: reversed-root marking loses no unmarked
ball-class information. -/
theorem rootLift_injective : Function.Injective rootLift := by
  intro q s h
  have hf := congrArg ExteriorMarkedBallClass.forget h
  exact (rootLift_forget q).symm.trans (hf.trans (rootLift_forget s))

/-- Helper toward Proposition 5.16: every whole-plane homeomorphism
preserves and reflects boundedness, by the existing compact-closure proof.
This concerns arbitrary sets, including nonretained complementary faces. -/
theorem planeHomeomorph_isBounded_image_iff (H : ℂ ≃ₜ ℂ) (S : Set ℂ) :
    Bornology.IsBounded (H '' S) ↔ Bornology.IsBounded S :=
  isBounded_planeHomeomorph_image_iff H S

/-- Helper toward Proposition 5.16: a whole-plane homeomorphism carries
components of the complement of any drawing image to components of the
complement of its image. No retained-face hypothesis is needed. -/
theorem planeHomeomorph_image_complementComponent
    (H : ℂ ≃ₜ ℂ) (S : Set ℂ) (z : ℂ) :
    H '' connectedComponentIn Sᶜ z = connectedComponentIn (H '' S)ᶜ (H z) :=
  Homeomorph.image_connectedComponentIn_compl H S z

/-- Helper toward Proposition 5.16: an ambient complementary face lies in
one complementary component of the restricted drawing, with the same
ambient face and the same drawing throughout. -/
theorem ambientFace_subset_restrictedFace
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (U : P.Face) :
    ∃ V : (d39FacedBallPLDrawing M P r hr).Face, U.val ⊆ V.val := by
  let Q := d39FacedBallPLDrawing M P r hr
  obtain ⟨z, hz, hU⟩ := U.property
  have hzQ : z ∉ Q.image :=
    fun h => hz (d39FacedBallPLDrawing_image_subset M P r hr h)
  refine ⟨⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩, ?_⟩
  rw [hU]
  exact connectedComponentIn_mono z
    (Set.compl_subset_compl.mpr (d39FacedBallPLDrawing_image_subset M P r hr))

/-- Helper toward Proposition 5.16: restricting the drawing preserves the
left-side bordering relation into any restricted face containing the
specified ambient face. The retained dart has exactly its ambient polyline. -/
theorem dartBorders_restrictedFace_of_subset
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D)
    (U : P.Face) (V : (d39FacedBallPLDrawing M P r hr).Face)
    (hUV : U.val ⊆ V.val) (hborder : P.dartBorders d.val U) :
    (d39FacedBallPLDrawing M P r hr).dartBorders d V := by
  obtain ⟨δ, hδ, hleft⟩ := hborder
  refine ⟨δ, hδ, ?_⟩
  intro s t hs hsδ ht htδ
  exact hUV (hleft s t hs hsδ ht htδ)

/-- Helper toward Proposition 5.16: an unbounded ambient left face remains
inside the restricted left face of each of its retained bordering darts. -/
theorem ambientUnboundedDart_mem_externalOrbit
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D)
    (U : P.Face) (hU : P.IsUnbounded U) (hborder : P.dartBorders d.val U) :
    d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  obtain ⟨V, hUV⟩ := ambientFace_subset_restrictedFace M P r hr U
  have hV := dartBorders_restrictedFace_of_subset M P r hr d U V hUV hborder
  have hface := ((d39FacedBall M r hr).plDartFace_eq_iff
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (d39FacedBallPLDrawing M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr) d V).mpr hV
  apply (d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace
    M P r hr d).mpr
  rw [hface]
  intro hb
  exact (P.isUnbounded_iff_not_isBounded U).mp hU (hb.subset hUV)

/-- Helper toward Proposition 5.16: if the reversed ordered root borders
an unbounded face of this ambient drawing, the selected finite exterior is
exactly its reversed-root orbit. Positive radius retains the root and its
reversal, including when the root edge is missing. -/
theorem externalOrbit_eq_reversedRootOrbit
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : P.dartBorders (M.core.edgeInv M.rootMark.dart) U) :
    (d39FacedBallPLWithExternal M P r hr).externalOrbit =
      (rootBall (d39FacedBall M r hr)).externalOrbit := by
  let d := (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart
  have hd : d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val :=
    ambientUnboundedDart_mem_externalOrbit M P r hr d U hU hborder
  exact plBallFaceCycleOrbit_eq_of_mem _ _ d hd Equiv.Perm.SameCycle.rfl

/-- Helper toward Proposition 5.16: under the same drawing-level unbounded
root-side hypotheses, the actual marked ball class is the reversed-root
lift of its unmarked class. Source constructions must still supply these
hypotheses for their exact drawings. -/
theorem markedBallClass_eq_rootLift
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : P.dartBorders (M.core.edgeInv M.rootMark.dart) U) :
    Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
      rootLift (d39BallClass M r hr) := by
  have heq : d39FacedBallPLWithExternal M P r hr =
      rootBall (d39FacedBall M r hr) := by
    have horbit := externalOrbit_eq_reversedRootOrbit M P r hr U hU hborder
    exact congrArg (fun O : D39BallFaceCycleOrbit (d39FacedBall M r hr) =>
      D39FiniteBallWithExternal.mk (d39FacedBall M r hr) O) horbit
  exact congrArg (Quotient.mk exteriorMarkedBallSetoid) heq








end Prop516RootExteriorEncoding
end DirectedDistances.PaperProofs.Section5

end
