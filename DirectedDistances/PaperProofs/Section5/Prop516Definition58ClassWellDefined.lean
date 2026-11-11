/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section5.UIBHBOTDefinition
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass
import all DirectedDistances.PaperProofs.Section5.UIBHBOTD39Domain
import all DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass

/-! # Drawing independence for the Definition 5.8 assembly -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open MeasureTheory Set
open scoped Classical

private theorem exists_increasing_param
    (f g : unitInterval → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hr : Set.range f = Set.range g) (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧ ∀ t, f t = g (φ t) := by
  let ef : unitInterval ≃ₜ Set.range f :=
    (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorph
  let eg : unitInterval ≃ₜ Set.range g :=
    (hg.isClosedEmbedding hgi).isEmbedding.toHomeomorph
  let φ := (ef.trans (Homeomorph.setCongr hr)).trans eg.symm
  have hm (t : unitInterval) : g (φ t) = f t :=
    congrArg Subtype.val (eg.apply_symm_apply ((Homeomorph.setCongr hr) (ef t)))
  have hz : φ 0 = 0 := hgi ((hm 0).trans h0)
  have ho : φ 1 = 1 := hgi ((hm 1).trans h1)
  refine ⟨φ, φ.continuous.strictMono_of_inj_boundedOrder ?_ φ.injective,
    fun t => (hm t).symm⟩
  change φ 0 ≤ φ 1
  rw [hz, ho]
  exact zero_le_one

section Witnesses

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P P' : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (hp' : P'.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha' : ∀ d, (P'.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F F' : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hf' : F'.pos = uibhbotSeparationFuturePos W H h0)
  (hFim' : F'.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa' : ∀ d, (F'.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "G'" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P' hp' ha' F' hf' hFim' hFa'
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
local notation "M'" => uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin P' hp' ha' F' hf' hFim' hFa' hRpos
local notation "rho" => uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "rho'" => uibhbotAssemblyD39RootMark W H h0 hL hR hfin P' hp' ha' F' hf' hFim' hFa'

include hp hp' hf hf' in
private theorem assembly_pos_eq : (G).pos = (G').pos := by
  change uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P.pos) F.pos =
    uibhbotAssemblyPos W (uibhbotAssemblyHalfTurn ∘ P'.pos) F'.pos
  rw [hp, hp', hf, hf']

include ha ha' hFa hFa' in
private theorem assembly_arc_image_eq (d : WholePlaneDart W) :
    ((G).arc d).image = ((G').arc d).image := by
  change (uibhbotAssemblyArc W
    (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P.arc e)) F.arc d).image =
    (uibhbotAssemblyArc W
    (fun e => Polyline.mapPoints uibhbotAssemblyHalfTurn (P'.arc e)) F'.arc d).image
  unfold uibhbotAssemblyArc
  split
  · exact (hFa _).trans (hFa' _).symm
  · rw [Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _),
      Polyline.image_mapPoints _ _ (uibhbotAssemblyHalfTurn_affine _), ha, ha']

/-- Helper toward Proposition 5.16: all Definition 5.8 drawing witnesses
with their prescribed positions and arc images give geometrically isomorphic
rooted maps, using the identity on the plane, vertices, and geometric edges. -/
theorem uibhbotAssembly_drawing_independent :
    Nonempty (D39GeomRootedMapIsoV2 (M) (rho) (M') (rho')) := by
  have hpos := assembly_pos_eq W H h0 hL hR hfin P P' hp ha hp' ha'
    F F' hf hFim hFa hf' hFim' hFa'
  have him := assembly_arc_image_eq W H h0 hL hR hfin P P' hp ha hp' ha'
    F F' hf hFim hFa hf' hFim' hFa'
  have hparam (e : (G).GeometricEdge) :
      ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, (M).arc e t = (M').arc e (φ t) := by
    apply exists_increasing_param
    · exact ((M).arc e).continuous
    · exact ((M').arc e).continuous
    · exact ((G).arc e.out).toPath_injective ((G).arc_length _) ((G).arc_simple _)
    · exact ((G').arc e.out).toPath_injective ((G').arc_length _) ((G').arc_simple _)
    · change Set.range ((G).arc e.out).toPath = Set.range ((G').arc e.out).toPath
      rw [Polyline.range_toPath, Polyline.range_toPath, him]
    · rw [Path.source, Path.source]
      exact congrFun hpos _
    · rw [Path.target, Path.target]
      exact congrFun hpos _
  choose φ hmono hmatch using hparam
  refine ⟨{
    h := Homeomorph.refl ℂ
    orientationPreserving := orientationPreserving_refl
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    edgeFlip := fun _ => false
    edgeParam := φ
    edgeParam_mono := fun e _ => hmono e
    edgeParam_anti := by intro e he; cases he
    pos_map := fun v => congrFun hpos v
    arc_map := hmatch
    src_map := fun _ => rfl
    tgt_map := fun _ => rfl
    missing_map := fun _ => Iff.rfl
    orientation_map := by
      intro e he
      change (!e.out.2) = Bool.xor (!e.out.2) false
      cases e.out.2 <;> rfl
    root_edge_map := rfl
    root_bool_map := by rw [Bool.xor_false]; rfl
  }⟩

/-- Helper toward Proposition 5.16: every Definition 5.8 witness assembly
is isomorphic to the fixed canonical assembly for the same code. -/
theorem uibhbotAssembly_iso_canonical :
    Nonempty (D39GeomRootedMapIsoV2 (M) (rho)
      (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos)
      (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)) := by
  exact uibhbotAssembly_drawing_independent W H h0 hL hR hfin P
    (uibhbotD39PastCanonicalDrawing W hL hR hfin) hp ha
    (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
    F (uibhbotD39FutureCanonicalDrawing W H h0) hf hFim hFa
    (uibhbotD39FutureCanonicalDrawing_pos W H h0)
    (uibhbotD39FutureCanonicalDrawing_image W H h0)
    (uibhbotD39FutureCanonicalDrawing_arcImage W H h0) hRpos

/-- Helper toward Proposition 5.16: on the canonical domain event every
Definition 5.8 drawing witness assembly has the complete geometric domain. -/
theorem uibhbotAssembly_domain_of_canonicalDomainEvent
    (hW : uibhbotD39CanonicalDomainEvent W) : D39GeomDomain (M) (rho) := by
  let D := Classical.choice hW
  obtain ⟨iso⟩ := uibhbotAssembly_iso_canonical W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos
  exact iso.symm.domain_map D.domain

/-- Helper toward Proposition 5.16: any domain-packaged Definition 5.8
witness assembly represents exactly the selected canonical geometric class. -/
theorem uibhbotAssembly_class_eq_canonical
    (hW : uibhbotD39CanonicalDomainEvent W) (hd : D39GeomDomain (M) (rho)) :
    some (Quotient.mk d39DomainSetoid
      (⟨WholePlaneVertex W, (G).GeometricEdge, (M), (rho), hd⟩ : D39DomainRootedMap)) =
      uibhbotD39CanonicalClass W := by
  simp only [uibhbotD39CanonicalClass, dite_eq_left hW]
  apply congrArg some
  apply Quotient.sound
  exact uibhbotAssembly_iso_canonical W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos

/-- Helper toward Proposition 5.16: extracting the almost-surely defined
canonical option gives the geometric class of every Definition 5.8 witness. -/
theorem uibhbotAssembly_class_eq_canonical_get
    (hW : uibhbotD39CanonicalDomainEvent W) (hd : D39GeomDomain (M) (rho))
    (hs : (uibhbotD39CanonicalClass W).isSome) :
    Quotient.mk d39DomainSetoid
      (⟨WholePlaneVertex W, (G).GeometricEdge, (M), (rho), hd⟩ : D39DomainRootedMap) =
      (uibhbotD39CanonicalClass W).get hs := by
  have he := uibhbotAssembly_class_eq_canonical W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos hW hd
  simp only [← he, Option.get_some]

end Witnesses

/-- Helper toward Proposition 5.16: almost surely Definition 5.8 supplies
drawing witnesses whose rooted geometric class is the canonical class.
The domain proof is transported from the canonical assembly along the proved
drawing isomorphism. -/
theorem uibhbotCodeLawRel_ae_definition58_class_eq_canonical :
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
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
          h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
            (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n),
      let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
      let M := uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      let rho := uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa
      ∃ (hd : D39GeomDomain M rho) (hs : (uibhbotD39CanonicalClass W).isSome),
        Quotient.mk d39DomainSetoid
          (⟨WholePlaneVertex W, G.GeometricEdge, M, rho, hd⟩ : D39DomainRootedMap) =
            (uibhbotD39CanonicalClass W).get hs := by
  filter_upwards [DirectedDistances.Paper.Section5.def_uihbot,
    uibhbotCodeLawRel_ae_d39CanonicalDomainEvent,
    uibhbotCodeLawRel_ae_uibhbotD39CanonicalClass_isSome] with W hw hW hs
  rcases hw with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e, hrest⟩
  have hd := uibhbotAssembly_domain_of_canonicalDomainEvent W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos hW
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, hd, hs,
    uibhbotAssembly_class_eq_canonical_get W H h0 hL hR hfin
      P hp ha F hf hFim hFa hRpos hW hd hs⟩

end DirectedDistances.PaperProofs.Section5
end
