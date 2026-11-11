/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIBHBOTDefinitionV2
public import DirectedDistances.PaperProofs.Section3.D39GeometricDomain

/-! # The UIBHBOT assembly in the Definition 3.8 domain

Helpers toward Definition 3.8 applications (Propositions 5.9 and 5.16). -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory

section Assembly

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
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
    (shiftedStream W 0) h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.8 applications (Propositions 5.9 and 5.16):
the UIBHBOT assembly has finitely many incident geometric edge identities,
including the two darts of each missing edge. -/
theorem uibhbotAssemblyD39_locallyFinite :
    ∀ v : WholePlaneVertex W,
      ({e : (G).GeometricEdge | (M).toPlaneMapWithMissing.src e = v ∨
        (M).toPlaneMapWithMissing.tgt e = v}).Finite := by
  classical
  intro v
  let S : Set (WholePlaneDart W) := {d | wholePlaneDartVertex W d = v}
  have hS : S.Finite := wholePlaneStar_finite W H v
  let q : WholePlaneDart W → (G).GeometricEdge := fun d => Quotient.mk (G).edgeSetoid d
  apply (hS.image q).subset
  intro e he
  rcases he with hsrc | htgt
  · refine ⟨e.out, ?_, Quotient.out_eq e⟩
    change wholePlaneDartVertex W e.out = v at hsrc
    exact hsrc
  · have hflip : wholePlaneDartVertex W (wholePlaneDartFlip W e.out) = v := by
      change wholePlaneDartVertex W (wholePlaneDartFlip W e.out) = v at htgt
      exact htgt
    refine ⟨wholePlaneDartFlip W e.out, ?_, ?_⟩
    · exact hflip
    · calc
        q (wholePlaneDartFlip W e.out) = q e.out := (G).geometricEdge_flip e.out
        _ = e := Quotient.out_eq e

/-- Helper toward Definition 3.8 applications (Propositions 5.9 and 5.16):
the UIBHBOT assembly's all-edge geometric graph is connected. -/
theorem uibhbotAssemblyD39_connected :
    ∀ v w : WholePlaneVertex W, (d39GeomGraph M).Reachable v w := by
  intro v w
  obtain ⟨d, rfl⟩ := uibhbot_faceOrbit_dartVertex_surjective W H v
  obtain ⟨e, rfl⟩ := uibhbot_faceOrbit_dartVertex_surjective W H w
  have hwestEast (a : WholePlaneEdge W) :
      wholePlaneEdgeWest W a ≠ wholePlaneEdgeEast W a := by
    obtain ⟨⟨N, j⟩, hrep⟩ := Quotient.exists_rep a
    rw [← hrep]
    change wholePlaneVertexι W N (edgeWest (shiftedStream W N) j) ≠
      wholePlaneVertexι W N (edgeEast (shiftedStream W N) j)
    intro heq
    have hstage := wholePlaneVertexι_injective W N heq
    have halloc := kmsw_edge_allocated_by_self (shiftedStream W N) j
    have hrank := kmswStageRank_strict (shiftedStream W N) j j halloc
    have hend := edge_endpoints_eq (shiftedStream W N) halloc
    rw [hend.1, hend.2] at hrank
    rw [hstage] at hrank
    exact (lt_irrefl _ hrank)
  have hvertexNe (a : WholePlaneDart W) :
      wholePlaneDartVertex W a ≠ wholePlaneDartVertex W (wholePlaneDartFlip W a) := by
    rcases a with ⟨j, b⟩
    cases b
    · change wholePlaneEdgeWest W j ≠ wholePlaneEdgeEast W j
      exact hwestEast j
    · change wholePlaneEdgeEast W j ≠ wholePlaneEdgeWest W j
      exact (hwestEast j).symm
  have hflipAdj (a : WholePlaneDart W) :
      (d39GeomGraph M).Adj (wholePlaneDartVertex W a)
        (wholePlaneDartVertex W (wholePlaneDartFlip W a)) := by
    have hne := hvertexNe a
    change d39GeomAdj M (wholePlaneDartVertex W a)
      (wholePlaneDartVertex W (wholePlaneDartFlip W a))
    refine ⟨hne, Quotient.mk (G).edgeSetoid a, ?_⟩
    rcases (G).geometricEdge_out_mk a with hout | hout
    · left
      constructor
      · change wholePlaneDartVertex W (Quotient.mk (G).edgeSetoid a).out = _
        rw [hout]
      · change wholePlaneDartVertex W
          (wholePlaneDartFlip W (Quotient.mk (G).edgeSetoid a).out) = _
        rw [hout]
    · right
      constructor
      · change wholePlaneDartVertex W (Quotient.mk (G).edgeSetoid a).out = _
        rw [hout]
      · change wholePlaneDartVertex W
          (wholePlaneDartFlip W (Quotient.mk (G).edgeSetoid a).out) = _
        rw [hout, wholePlaneDartFlip_involutive]
  have hwalk : Relation.ReflTransGen
      (fun a b : WholePlaneDart W =>
        b = wholePlaneRotation W H a ∨
        b = (wholePlaneRotation W H).symm a ∨
        b = wholePlaneDartFlip W a ∨
        b = (wholePlaneDartFlip W).symm a) d e :=
    wholePlaneDart_connected W H d e
  let R : WholePlaneDart W → WholePlaneDart W → Prop := fun a b =>
    wholePlaneDartVertex W a = wholePlaneDartVertex W b ∨
      (d39GeomGraph M).Adj (wholePlaneDartVertex W a) (wholePlaneDartVertex W b)
  have hR : Relation.ReflTransGen R d e := by
    apply Relation.ReflTransGen.mono (r := fun a b : WholePlaneDart W =>
      b = wholePlaneRotation W H a ∨
      b = (wholePlaneRotation W H).symm a ∨
      b = wholePlaneDartFlip W a ∨
      b = (wholePlaneDartFlip W).symm a)
    · intro a b hab
      rcases hab with hr | hr | hf | hf
      · left
        rw [hr]
        exact (wholePlaneRotation_preserves_dartVertex W H a).symm
      · left
        rw [hr]
        have hrot := wholePlaneRotation_preserves_dartVertex W H
          ((wholePlaneRotation W H).symm a)
        simpa using hrot
      · right
        rw [hf]
        exact hflipAdj a
      · right
        have hinv : (wholePlaneDartFlip W).symm a = wholePlaneDartFlip W a := by
          apply (wholePlaneDartFlip W).injective
          rw [Equiv.apply_symm_apply, wholePlaneDartFlip_involutive]
        rw [hf, hinv]
        exact hflipAdj a
    · exact hwalk
  have hreach {a b : WholePlaneDart W}
      (h : Relation.ReflTransGen R a b) :
      (d39GeomGraph M).Reachable (wholePlaneDartVertex W a)
        (wholePlaneDartVertex W b) := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact SimpleGraph.Reachable.refl _
    | @head a b hab hrest ih =>
      have hstep : (d39GeomGraph M).Reachable (wholePlaneDartVertex W a)
          (wholePlaneDartVertex W b) := by
        rcases hab with heq | hadj
        · rw [heq]
        · exact SimpleGraph.Adj.reachable hadj
      exact hstep.trans ih
  exact hreach hR

/-- The local topology ordered mark corresponding to the west dart consumed by the
Proposition 5.9 rooted-map identification. Its Boolean bit compensates for the
quotient representative so its first endpoint is exactly the marked dart's
incident vertex. -/
noncomputable def uibhbotAssemblyD39RootMark : (G).GeometricEdge × Bool := by
  classical
  let d : WholePlaneDart W := (uibhbotRootEdge W, false)
  let e : (G).GeometricEdge := Quotient.mk (G).edgeSetoid d
  exact (e, decide (e.out = d))

/-- Helper toward Definition 3.8 applications (Propositions 5.9 and 5.16):
the selected first endpoint is the west dart `(uibhbotRootEdge W, false)`
identified by `uibhbotProviderAssemblyD39_identification`. -/
theorem uibhbotAssemblyD39RootMark_firstVertex :
    d39GeomRootVertex M (uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F
      hf hFim hFa) =
      wholePlaneDartVertex W (uibhbotRootEdge W, false) := by
  classical
  let d : WholePlaneDart W := (uibhbotRootEdge W, false)
  let e : (G).GeometricEdge := Quotient.mk (G).edgeSetoid d
  change (if decide (e.out = d) then wholePlaneDartVertex W e.out
    else wholePlaneDartVertex W (wholePlaneDartFlip W e.out)) =
      wholePlaneDartVertex W d
  obtain hout | hout := (G).geometricEdge_out_mk d
  · have hout' : e.out = d := by simpa [e] using hout
    simp [hout']
  · have hout' : e.out = wholePlaneDartFlip W d := by simpa [e] using hout
    have hne : e.out ≠ d := by
      rw [hout']
      exact (G).flip_ne d
    have hbool : decide (e.out = d) = false := by simp [hne]
    rw [hbool, hout']
    simp [wholePlaneDartFlip_involutive]

/-- Helper toward Definition 3.8 applications (Propositions 5.9 and 5.16):
almost surely, the provider's UIBHBOT witnesses give the complete corrected
geometric domain, with the rooted-map isomorphism's west dart retained. -/
theorem uibhbotCodeLawRel_ae_d39GeomDomain :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
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
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
          (shiftedStream W 0) h0 (H.1 0) ''
            ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W),
      e 0 = uibhbotRootEdge W ∧
        D39GeomDomain (uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)
          (uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa) := by
  filter_upwards [def_uibhbot_provider_v2] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hprovider⟩
  rcases hprovider with ⟨_, _, _, _, _, _, _, _, _, _, he, _, _, _, _, _,
    hrootMissing, _, _, _, _, _⟩
  refine ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    he, ?_⟩
  refine ⟨uibhbotAssemblyD39_connected W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos,
    uibhbotAssemblyD39_locallyFinite W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos,
    ?_⟩
  apply Or.inl
  simpa [uibhbotAssemblyD39RootMark] using hrootMissing

end Assembly

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory

section Assembly

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
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
    (shiftedStream W 0) h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa

/-- Helper toward Definition 3.8 consumers: the assembly root mark is the
quotient of the west root dart with its representative Boolean. -/
theorem uibhbotAssemblyD39RootMark_eq :
    (by
      classical
      exact uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa =
        (Quotient.mk (G).edgeSetoid (uibhbotRootEdge W, false),
          decide ((Quotient.mk (G).edgeSetoid (uibhbotRootEdge W, false)).out =
            (uibhbotRootEdge W, false)))) := by
  classical
  unfold uibhbotAssemblyD39RootMark
  rfl

end Assembly

end DirectedDistances.PaperProofs.Section5
