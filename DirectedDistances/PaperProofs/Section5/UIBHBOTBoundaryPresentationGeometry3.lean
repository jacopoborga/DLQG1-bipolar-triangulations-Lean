/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry2

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.SourceResults

noncomputable section

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.2: adjust the presentation dart bit according
to the quotient edge's selected representative. -/
@[expose] def uibhbotAssemblyBoundaryDartAdjust :
    (G).GeometricEdge × Bool ≃ (G).GeometricEdge × Bool where
  toFun d := (d.1, if d.1.out.2 then !d.2 else d.2)
  invFun d := (d.1, if d.1.out.2 then !d.2 else d.2)
  left_inv d := by
    rcases d with ⟨q, b⟩
    cases hbit : q.out.2 <;> cases b <;> simp [hbit]
  right_inv d := by
    rcases d with ⟨q, b⟩
    cases hbit : q.out.2 <;> cases b <;> simp [hbit]

/-- Helper toward Definition 3.2: the representative-adjusted assembly dart
equivalence corrects the traversal bit after selecting a quotient representative. -/
@[expose] def uibhbotAssemblyBoundaryDartEquiv3 :
    WholePlaneDart W ≃ (G).GeometricEdge × Bool :=
  (uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa).trans
    (uibhbotAssemblyBoundaryDartAdjust W H h0 hL hR hfin P hp ha F hf hFim hFa)

/-- Helper toward Definition 3.2: the representative-adjusted carrier
equivalence preserves the map's initial-vertex function, with both endpoint
definitions unfolded to the stored arc endpoints. -/
theorem uibhbotAssemblyBoundaryDartEquiv3_initialVertex (d : WholePlaneDart W) :
    boundaryDartInitial M
      (uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa d) =
      wholePlaneDartVertex W d := by
  rcases d with ⟨e, b⟩
  let q := Quotient.mk (G).edgeSetoid (e, b)
  have hrep := (G).geometricEdge_out_mk (e, b)
  simp only [uibhbotAssemblyBoundaryDartEquiv3,
    uibhbotAssemblyBoundaryDartAdjust, uibhbotAssemblyBoundaryDartEquiv]
  change boundaryDartInitial M
      (q, if q.out.2 then !!b else !b) = wholePlaneDartVertex W (e, b)
  simp only [Bool.not_not]
  have hsrc (q : (G).GeometricEdge) :
      ((M).toPlaneMapWithMissing).src q = wholePlaneDartVertex W q.out := rfl
  have htgt (q : (G).GeometricEdge) :
      ((M).toPlaneMapWithMissing).tgt q = wholePlaneDartVertex W (wholePlaneDartFlip W q.out) := rfl
  rw [boundaryDartInitial_eq, hsrc, htgt]
  change (if (if q.out.2 then b else !b) then
      wholePlaneDartVertex W q.out else
        wholePlaneDartVertex W (wholePlaneDartFlip W q.out)) =
    wholePlaneDartVertex W (e, b)
  rcases hrep with hrep | hrep
  · rw [hrep]
    cases b <;> simp
  · rw [hrep]
    cases b <;> rfl

/-- Helper toward Definition 3.2: the representative adjustment commutes
with reversal of the presentation dart. -/
theorem uibhbotAssemblyBoundaryDartAdjust_flip
    (d : (G).GeometricEdge × Bool) :
    uibhbotAssemblyBoundaryDartAdjust W H h0 hL hR hfin P hp ha F hf hFim hFa
      (d.1, !d.2) =
      ((uibhbotAssemblyBoundaryDartAdjust W H h0 hL hR hfin P hp ha F hf hFim hFa d).1,
        !(uibhbotAssemblyBoundaryDartAdjust W H h0 hL hR hfin P hp ha F hf hFim hFa d).2) := by
  rcases d with ⟨q, b⟩
  cases hbit : q.out.2 <;> cases b <;>
    simp [uibhbotAssemblyBoundaryDartAdjust, hbit]

/-- Helper toward Definition 3.2: the representative-adjusted dart
equivalence commutes with reversal. -/
theorem uibhbotAssemblyBoundaryDartEquiv3_flip (d : WholePlaneDart W) :
    uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
      (wholePlaneDartFlip W d) =
      ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa d).1,
        !(uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa d).2) := by
  simp only [uibhbotAssemblyBoundaryDartEquiv3, Equiv.trans_apply]
  rw [uibhbotAssemblyBoundaryDartEquiv_flip W H h0 hL hR hfin P hp ha F hf hFim hFa d]
  exact uibhbotAssemblyBoundaryDartAdjust_flip W H h0 hL hR hfin P hp ha F hf hFim hFa _

/-- Helper toward Definition 3.2: conjugate the assembly rotation along the
representative-adjusted presentation dart equivalence. -/
@[expose] def uibhbotAssemblyBoundaryDartRotation3 :
    Equiv.Perm ((G).GeometricEdge × Bool) :=
  uiqbotTransportRotation
    (uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm
    (wholePlaneRotation W H)

/-- Helper toward Definition 3.2: the transported rotation commutes with the
representative-adjusted dart equivalence. -/
theorem uibhbotAssemblyBoundaryDartEquiv3_rotation (d : WholePlaneDart W) :
    uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa
      (uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa d) =
      uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
        (wholePlaneRotation W H d) := by
  simp [uibhbotAssemblyBoundaryDartRotation3, uiqbotTransportRotation]

/-- Helper toward Definition 3.2: transport the assembly PL drawing to the
presentation dart carrier, preserving its image and face-border relation. -/
theorem uibhbotAssemblyBoundaryDrawingTransport :
    ∃ G' : PLDrawing ((G).GeometricEdge × Bool) (WholePlaneVertex W)
        (fun d => (d.1, !d.2))
        (uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
        (boundaryDartInitial M),
      G'.image = (G).image ∧
      ∀ U : (G).Face, ∃ U' : G'.Face,
        U'.val = U.val ∧ ∀ d, G'.dartBorders
          (uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa d) U' ↔
          (G).dartBorders d U := by
  let e := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
  obtain ⟨G', himage, hface⟩ := DirectedDistances.PaperProofs.Section4.plDrawing_transport
    (D := WholePlaneDart W) (D' := (G).GeometricEdge × Bool)
    (V := WholePlaneVertex W)
    (flip := wholePlaneDartFlip W) (rot := wholePlaneRotation W H)
    (vert := wholePlaneDartVertex W)
    (flip' := fun d : (G).GeometricEdge × Bool => (d.1, !d.2))
    (rot' := uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
    (vert' := boundaryDartInitial M)
    e
    (by intro d; exact (uibhbotAssemblyBoundaryDartEquiv3_flip
      W H h0 hL hR hfin P hp ha F hf hFim hFa d).symm)
    (uibhbotAssemblyBoundaryDartEquiv3_rotation W H h0 hL hR hfin P hp ha F hf hFim hFa)
    (uibhbotAssemblyBoundaryDartEquiv3_initialVertex
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)
    G
  exact ⟨G', himage, hface⟩

/-- Helper toward Definition 3.2: transport the unique unbounded assembly
face, its exact external-dart classification, and geometric successor to the
representative-adjusted presentation dart carrier. -/
theorem uibhbotAssemblyBoundaryPresentationExternalFace3 :
    ∃ G' : PLDrawing ((G).GeometricEdge × Bool) (WholePlaneVertex W)
        (fun d => (d.1, !d.2))
        (uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa)
        (boundaryDartInitial M),
      ∃ U : G'.Face,
        (∃! V : G'.Face, G'.IsUnbounded V) ∧
        G'.IsUnbounded U ∧
        (∀ d, G'.dartBorders d U ↔
          (((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d).2 = true ∧
            ¬ wholePlaneEdgePresent W
              ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d).1)) ∧
        IsGeometricExternalFaceSucc G' U
          (fun d => uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
            (wholePlaneFaceSucc W H
              ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d))) := by
  let e := uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa
  let rot := uibhbotAssemblyBoundaryDartRotation3 W H h0 hL hR hfin P hp ha F hf hFim hFa
  obtain ⟨G', himage, hface⟩ := uibhbotAssemblyBoundaryDrawingTransport
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  obtain ⟨U₀, hU₀, hBorder₀, hSucc₀⟩ :=
    uibhbotAssembly_wholePlaneExternalFaceGeometry
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  obtain ⟨U, hval, hBorders⟩ := hface U₀
  have hUnbounded : G'.IsUnbounded U := by
    intro R
    obtain ⟨z, hz, hr⟩ := hU₀ R
    exact ⟨z, hval ▸ hz, hr⟩
  have hBorder (d : (G).GeometricEdge × Bool) :
      G'.dartBorders d U ↔ (e.symm d).2 = true ∧
        ¬ wholePlaneEdgePresent W (e.symm d).1 := by
    have hb := hBorders (e.symm d)
    rw [e.apply_symm_apply d] at hb
    exact hb.trans (hBorder₀ (e.symm d))
  have hUnique : ∃! V : G'.Face, G'.IsUnbounded V := by
    refine ⟨U, hUnbounded, ?_⟩
    intro V hV
    obtain ⟨V₀, hV₀val⟩ : ∃ V₀ : (G).Face, V₀.val = V.val := by
      obtain ⟨z, hz, hcomp⟩ := V.property
      refine ⟨⟨V.val, z, ?_, ?_⟩, rfl⟩
      · simpa only [himage] using hz
      · simpa only [himage] using hcomp
    have hV₀ : (G).IsUnbounded V₀ := by
      intro R
      obtain ⟨z, hz, hr⟩ := hV R
      exact ⟨z, hV₀val ▸ hz, hr⟩
    have heq : V₀ = U₀ := (uibhbot_assembly_unbounded_face_existsUnique
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos).unique hV₀ hU₀
    apply Subtype.ext
    calc
      V.val = V₀.val := hV₀val.symm
      _ = U₀.val := congrArg Subtype.val heq
      _ = U.val := hval.symm
  have hSucc : IsGeometricExternalFaceSucc G' U
      (fun d => e (wholePlaneFaceSucc W H (e.symm d))) := by
    refine ⟨hUnbounded, ?_⟩
    intro d hd
    let d₀ := e.symm d
    have hd₀ : (G).dartBorders d₀ U₀ := by
      have hd' : G'.dartBorders (e d₀) U := by simpa [d₀] using hd
      exact (hBorders d₀).mp hd'
    obtain ⟨hsucc, hnext⟩ := hSucc₀.2 d₀ hd₀
    refine ⟨?_, ?_⟩
    · change e (wholePlaneFaceSucc W H d₀) = rot.symm (d.1, !d.2)
      rw [hsucc]
      have hrotSymm (x : WholePlaneDart W) :
          e ((wholePlaneRotation W H).symm x) = rot.symm (e x) := by
        apply rot.injective
        rw [rot.apply_symm_apply]
        rw [uibhbotAssemblyBoundaryDartEquiv3_rotation
          W H h0 hL hR hfin P hp ha F hf hFim hFa ((wholePlaneRotation W H).symm x)]
        rw [Equiv.apply_symm_apply]
      have hflip' : (d.1, !d.2) = e (d₀.1, !d₀.2) := by
        have hd₀' : e d₀ = d := by
          dsimp [d₀]
          exact e.apply_symm_apply d
        calc
          (d.1, !d.2) = ((e d₀).1, !(e d₀).2) := by rw [← hd₀']
          _ = e (d₀.1, !d₀.2) :=
            (uibhbotAssemblyBoundaryDartEquiv3_flip
              W H h0 hL hR hfin P hp ha F hf hFim hFa d₀).symm
      rw [hflip']
      exact hrotSymm (wholePlaneDartFlip W d₀)
    · have hnext' : G'.dartBorders (e (wholePlaneFaceSucc W H d₀)) U :=
        (hBorders (wholePlaneFaceSucc W H d₀)).2 hnext
      simpa [d₀] using hnext'
  exact ⟨G', U, hUnique, hUnbounded, hBorder, hSucc⟩

end
end DirectedDistances.PaperProofs.Section5

end
