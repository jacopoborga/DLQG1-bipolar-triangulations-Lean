/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry4
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers51And52Complete
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer52FaceOrbits

/-! Helper toward Proposition 3.9: shifted closed regions and actual face incidence.

The closed-region route already supplies bounded faces with oriented incidence.
Its target complement is the union of the unbounded complementary components.
Identifying that union with one component, and comparing the edge-deleted
drawings required by Proposition 5.1 and Lemma 5.2, remain separate obligations. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open ShiftedStartGeometry Set Topology

private theorem closed_region_complement
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (hgraph : P.image ⊆ ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val) :
    (⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val)ᶜ =
      ⋃ F : {F : P.Face // P.IsUnbounded F}, F.val.val := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr (fun hx => hz (hgraph hx))
    have hF : P.IsUnbounded F := by
      by_contra hn
      exact hz (mem_iUnion.mpr ⟨⟨F, hn⟩, subset_closure hzF⟩)
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, hzF⟩
  · intro hz hclosed
    obtain ⟨F, hzF⟩ := mem_iUnion.mp hz
    obtain ⟨K, hzK⟩ := mem_iUnion.mp hclosed
    have hne : F.val ≠ K.val := fun he => K.property (he ▸ F.property)
    exact Set.disjoint_left.mp
      ((P.faces_disjoint hne).closure_right (P.face_open_frontier_subset_image hv F.val).1)
      hzF hzK

private theorem start_dart_injective (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n) :
    Function.Injective (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) := by
  intro a b hab
  have he := J.dart.injective hab
  exact Prod.ext (wholePlaneEdgeι_injective _ 0 (congrArg Prod.fst he))
    (congrArg (fun q : WholePlaneEdge (shiftWordInt W n) × Bool => q.2) he)

/-- Helper toward Proposition 3.9: the target closed region has precisely
the union of all unbounded complementary components as its complement.
This statement does not identify that union with a single face. -/
theorem inherited_closed_region_complement (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    (⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val)ᶜ =
      ⋃ F : {F : Q.Face // Q.IsUnbounded F}, F.val.val := by
  intro G Q
  obtain ⟨_, hQ, _⟩ := exists_closed_region_homeomorph W H h hpast n J hfin
  apply closed_region_complement Q _ hQ
  rintro ⟨v, d, hd, hdv⟩
  exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩

/-- Helper toward Proposition 3.9: the bounded-face equivalence preserves
each oriented dart. A transported dart borders an unbounded component exactly
when it is an external run dart; no exterior orientation premise is needed. -/
theorem exists_bounded_face_incidence (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ τ : {F : P.Face // ¬ P.IsUnbounded F} ≃ {F : Q.Face // ¬ Q.IsUnbounded F},
      (∀ (F : {F : P.Face // ¬ P.IsUnbounded F}) (a : ℕ × Bool)
        (d : retainedDarts W n univ),
        J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
        (Q.dartBorders d (τ F).val ↔ P.dartBorders a F.val)) ∧
      (∀ (a : ℕ × Bool) (d : retainedDarts W n univ),
        J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
        ((∃ F : Q.Face, Q.IsUnbounded F ∧ Q.dartBorders d F) ↔
          limitExternalDart u a)) := by
  classical
  intro u P G Q
  obtain ⟨_, τ, _, _, _, _, _, hd, _⟩ :=
    exists_bounded_face_equiv W H h hpast n J hfin
  have hinc (F : {F : P.Face // ¬ P.IsUnbounded F}) (a : ℕ × Bool)
      (d : retainedDarts W n univ)
      (ha : J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) :
      Q.dartBorders d (τ F).val ↔ P.dartBorders a F.val := by
    rw [hd]
    constructor
    · rintro ⟨b, hb, he⟩
      exact start_dart_injective W n J (he.trans ha.symm) ▸ hb
    · intro hb
      exact ⟨a, hb, ha⟩
  refine ⟨τ, hinc, ?_⟩
  intro a d ha
  obtain ⟨U, hU, huniq, hborder⟩ := monotoneFamilyDrawing_faceClassification_twoSided
    u hfin (start_boundary_hits W h n)
  have hv : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, e, he, hev⟩
    exact ⟨⟨e, he⟩, Subtype.ext hev⟩
  constructor
  · rintro ⟨F, hF, hdF⟩
    obtain ⟨A, haA, _⟩ := dart_borders_unique u hfin (start_boundary_hits W h n) a
    have hA : P.IsUnbounded A := by
      by_contra hn
      have he := Q.dartBorders_face_unique d F (τ ⟨A, hn⟩).val hdF
        ((hinc ⟨A, hn⟩ a d ha).mpr haA)
      exact (τ ⟨A, hn⟩).property (he ▸ hF)
    exact (hborder a).mp (huniq A hA ▸ haA)
  · intro haU
    obtain ⟨F, hdF, _⟩ := Q.dartBorders_existsUnique_of_locallyFiniteVertexImage32
      (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective Q hv) d
    refine ⟨F, ?_, hdF⟩
    by_contra hn
    let B := τ.symm ⟨F, hn⟩
    have hdB : Q.dartBorders d (τ B).val := by
      change Q.dartBorders d (τ (τ.symm ⟨F, hn⟩)).val
      rw [τ.apply_symm_apply]
      exact hdF
    have he := P.dartBorders_face_unique a B.val U ((hinc B a d ha).mp hdB)
      ((hborder a).mpr haU)
    exact B.property (he.symm ▸ hU)

/-- Helper toward Proposition 3.9: every bounded shifted face corresponds
to exactly one bounded actual region in every representative, with complete
open-region coverage and winding-left incidence on each prescribed dart. -/
theorem representative_bounded_face_regions (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let S := uibotWholePlaneSourceDomain W H G hp
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι (shiftWordInt W n) 0 e))
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp
        (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)))
    ∃ R : {F : P.Face // ¬ P.IsUnbounded F} → Set ℂ,
      Function.Injective R ∧
      Set.range R = {U | U ∈ intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u univ)
          (E '' univ)) ∧ Bornology.IsBounded U} ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, Bornology.IsBounded (R F)) ∧
      (∀ F d, (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d)) s) ↔
        P.dartBorders d F.val) := by
  classical
  intro u P G S V E D
  let Q := inheritedDrawing W H G n univ
  obtain ⟨τ, hinc, _⟩ := exists_bounded_face_incidence W H h hpast n J hfin
  let R := fun F : {F : P.Face // ¬ P.IsUnbounded F} => I.h '' (τ F).val.val
  have hbounded (F : {F : P.Face // ¬ P.IsUnbounded F}) : Bornology.IsBounded (R F) := by
    by_contra hn
    exact (τ F).property
      ((representative_external W H h hpast hp A I n univ (τ F).val).mp hn)
  have hrange := representative_faceRegions W H h hpast hp A I n J univ
  refine ⟨R, ?_, ?_, ?_, hbounded, ?_⟩
  · intro F K he
    apply τ.injective
    apply Subtype.ext
    apply Subtype.ext
    exact Set.image_injective.mpr I.h.injective he
  · ext U
    constructor
    · rintro ⟨F, rfl⟩
      refine ⟨?_, hbounded F⟩
      rw [hrange]
      exact ⟨(τ F).val, rfl⟩
    · rintro ⟨hU, hb⟩
      rw [hrange] at hU
      obtain ⟨F, rfl⟩ := hU
      have hF : ¬ Q.IsUnbounded F := fun hn =>
        ((representative_external W H h hpast hp A I n univ F).mpr hn) hb
      refine ⟨τ.symm ⟨F, hF⟩, ?_⟩
      change I.h '' (τ (τ.symm ⟨F, hF⟩)).val.val = I.h '' F.val
      rw [τ.apply_symm_apply]
  · intro F
    exact I.h.isOpenMap _ (inherited_face_isOpen W H G n univ (τ F).val)
  · intro F d
    let a : retainedDarts W n univ :=
      ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 d), by
        rw [retained_darts_eq_image W n J univ]
        exact ⟨d, mem_univ _, rfl⟩⟩
    exact (representative_face_side W H h hpast hp A I n univ a (τ F).val).trans
      (hinc F d a rfl)

/-- Helper toward Proposition 3.9: exterior incidence in every representative
is exactly the external-dart predicate. The existential region is an actual
unbounded complementary component, not an assumed exterior or an orbit label. -/
theorem representative_unbounded_incidence (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let S := uibotWholePlaneSourceDomain W H G hp
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι (shiftWordInt W n) 0 e))
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp
        (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)))
    ∀ d : ℕ × Bool,
      (∃ U : Set ℂ,
        U ∈ intrinsicConsumer51FaceRegions
          (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u univ)
            (E '' univ)) ∧
        ¬ Bornology.IsBounded U ∧
        ∀ s, LeftAtOn U (intrinsicFutureDartArc A (D d)) s) ↔
          limitExternalDart u d := by
  intro u G S V E D d
  let Q := inheritedDrawing W H G n univ
  let a : retainedDarts W n univ :=
    ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 d), by
      rw [retained_darts_eq_image W n J univ]
      exact ⟨d, mem_univ _, rfl⟩⟩
  obtain ⟨_, _, hext⟩ := exists_bounded_face_incidence W H h hpast n J hfin
  have hrange := representative_faceRegions W H h hpast hp A I n J univ
  constructor
  · rintro ⟨U, hU, hb, hi⟩
    rw [hrange] at hU
    obtain ⟨F, rfl⟩ := hU
    exact (hext d a rfl).mp ⟨F,
      (representative_external W H h hpast hp A I n univ F).mp hb,
      (representative_face_side W H h hpast hp A I n univ a F).mp hi⟩
  · intro hd
    obtain ⟨F, hF, haF⟩ := (hext d a rfl).mpr hd
    refine ⟨I.h '' F.val, ?_,
      (representative_external W H h hpast hp A I n univ F).mpr hF,
      (representative_face_side W H h hpast hp A I n univ a F).mpr haF⟩
    rw [hrange]
    exact ⟨F, rfl⟩

/-- Helper toward Proposition 3.9: the closed-region homeomorphism is a
homeomorphism between the complement of the unique source exterior and the
complement of the union of target unbounded components. It retains all arcs,
vertices, bounded open faces and bounded closed faces. -/
theorem exists_exterior_complement_homeomorph (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let B := {F : P.Face // ¬ P.IsUnbounded F}
    let C := {F : Q.Face // ¬ Q.IsUnbounded F}
    let X := ⋃ F : {F : Q.Face // Q.IsUnbounded F}, F.val.val
    ∃ (U : P.Face) (hP : P.image ⊆ U.valᶜ) (_hQ : Q.image ⊆ Xᶜ)
      (g : (U.valᶜ : Set ℂ) ≃ₜ (Xᶜ : Set ℂ)) (τ : B ≃ C),
      P.IsUnbounded U ∧ (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      IsOpen X ∧
      (∀ v, (g ⟨P.pos v, hP (Or.inl ⟨v, rfl⟩)⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (g ⟨(P.arc d).toPath t,
            hP (Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      (∀ F : B, g '' {x : ↥(U.valᶜ) | (x : ℂ) ∈ F.val.val} =
        {y : ↥(Xᶜ) | (y : ℂ) ∈ (τ F).val.val}) ∧
      (∀ F : B, g '' {x : ↥(U.valᶜ) | (x : ℂ) ∈ closure F.val.val} =
        {y : ↥(Xᶜ) | (y : ℂ) ∈ closure (τ F).val.val}) := by
  intro u P G Q B C X
  obtain ⟨hP, hQ, g, τ, hv, ha, hcl, hopen, _, _, _⟩ :=
    exists_closed_region_homeomorph W H h hpast n J hfin
  obtain ⟨U, hU, huniq, hsource⟩ :=
    closed_region_eq_compl_exterior u hfin (start_boundary_hits W h n)
  have htarget : (⋃ F : C, closure F.val.val) = Xᶜ := by
    have hc := inherited_closed_region_complement W H h hpast n J hfin
    change (⋃ F : C, closure F.val.val)ᶜ = X at hc
    rw [← hc, compl_compl]
  have hP' : P.image ⊆ U.valᶜ := hsource ▸ hP
  have hQ' : Q.image ⊆ Xᶜ := htarget ▸ hQ
  let g' : (U.valᶜ : Set ℂ) ≃ₜ (Xᶜ : Set ℂ) :=
    (Homeomorph.setCongr hsource.symm).trans (g.trans (Homeomorph.setCongr htarget))
  have hval (x : ↥(U.valᶜ)) : (g' x : ℂ) = (g ⟨x, hsource.symm ▸ x.property⟩ : ℂ) := rfl
  refine ⟨U, hP', hQ', g', τ, hU, huniq, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun F => inherited_face_isOpen W H G n univ F.val
  · intro v
    exact (hval _).trans (hv v)
  · intro d
    obtain ⟨φ, hm, hφ⟩ := ha d
    exact ⟨φ, hm, fun t => (hval _).trans (hφ t)⟩
  · intro F
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hh := (Set.ext_iff.mp (hopen F) (g ⟨x, hsource.symm ▸ x.property⟩)).mp
        ⟨⟨x, hsource.symm ▸ x.property⟩, hx, rfl⟩
      exact hh
    · intro hy
      obtain ⟨x, hx, he⟩ := (Set.ext_iff.mp (hopen F)
        ⟨y, htarget.symm ▸ y.property⟩).mpr hy
      refine ⟨⟨x, hsource ▸ x.property⟩, hx, Subtype.ext ?_⟩
      exact (hval _).trans (congrArg
        (fun z : (⋃ F : C, closure F.val.val) => (z : ℂ)) he)
  · intro F
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hh := (Set.ext_iff.mp (hcl F) (g ⟨x, hsource.symm ▸ x.property⟩)).mp
        ⟨⟨x, hsource.symm ▸ x.property⟩, hx, rfl⟩
      exact hh
    · intro hy
      obtain ⟨x, hx, he⟩ := (Set.ext_iff.mp (hcl F)
        ⟨y, htarget.symm ▸ y.property⟩).mpr hy
      refine ⟨⟨x, hsource ▸ x.property⟩, hx, Subtype.ext ?_⟩
      exact (hval _).trans (congrArg
        (fun z : (⋃ F : C, closure F.val.val) => (z : ℂ)) he)

private theorem restricted_image_iff_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (T : Set D)
    (hT : ∀ d, d ∈ T ↔ flip d ∈ T) (z : ℂ) :
    z ∈ (restrictDrawing P T hT).image ↔ ∃ d ∈ T, z ∈ (P.arc d).image := by
  have hv : Function.Surjective (restrictedVertex P T) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  rw [(restrictDrawing P T hT).image_eq_union_arcs hv]
  constructor
  · intro hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp hz
    exact ⟨d.val, d.property, hd⟩
  · rintro ⟨d, hd, hz⟩
    exact mem_iUnion.mpr ⟨⟨d, hd⟩, hz⟩

/-- Helper toward Proposition 3.9: one closed-region homeomorphism matches
every retained geometric edge set, including all its incident vertices. It
therefore restricts to a homeomorphism of the relative complements for every
edge set. Relative complements are not asserted to be full plane faces. -/
theorem exists_closed_region_restriction_homeomorphs (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    let Y := ⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val
    ∃ g : X ≃ₜ Y, ∀ K : Set ℕ,
      let P' := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
      let Q' := inheritedDrawing W H G n K
      (∀ x : X, (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image) ∧
      Nonempty ({x : X // (x : ℂ) ∉ P'.image} ≃ₜ {y : Y // (y : ℂ) ∉ Q'.image}) := by
  intro u P G Q X Y
  obtain ⟨hP, _, g, _, _, ha, _, _, _, _, _⟩ :=
    exists_closed_region_homeomorph W H h hpast n J hfin
  refine ⟨g, fun K => ?_⟩
  intro P' Q'
  have himage (x : X) : (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image := by
    constructor
    · intro hx
      obtain ⟨d, hd, hxd⟩ := (restricted_image_iff_arc G
        (retainedDarts W n K) (fun _ => Iff.rfl) _).mp hx
      rw [retained_darts_eq_image W n J K] at hd
      obtain ⟨a, haK, rfl⟩ := hd
      obtain ⟨φ, _, hφ⟩ := ha a
      have ht : (g x : ℂ) ∈ range
          (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath := by
        rw [Polyline.range_toPath]
        exact hxd
      obtain ⟨t, ht⟩ := ht
      let z : X := ⟨(P.arc a).toPath (φ.symm t), hP (Or.inr ⟨a, by
        rw [← Polyline.range_toPath]
        exact ⟨φ.symm t, rfl⟩⟩)⟩
      have hz : g z = g x := by
        apply Subtype.ext
        exact (hφ (φ.symm t)).trans (by rw [φ.apply_symm_apply]; exact ht)
      have hzx : (z : ℂ) = (x : ℂ) := congrArg Subtype.val (g.injective hz)
      apply (restricted_image_iff_arc P {d : ℕ × Bool | d.1 ∈ K}
        (fun _ => Iff.rfl) _).mpr
      refine ⟨a, haK, ?_⟩
      rw [← hzx, ← Polyline.range_toPath]
      exact ⟨φ.symm t, rfl⟩
    · intro hx
      obtain ⟨a, haK, hxa⟩ := (restricted_image_iff_arc P
        {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl) _).mp hx
      have ht : (x : ℂ) ∈ range (P.arc a).toPath := by
        rw [Polyline.range_toPath]
        exact hxa
      obtain ⟨t, ht⟩ := ht
      obtain ⟨φ, _, hφ⟩ := ha a
      apply (restricted_image_iff_arc G (retainedDarts W n K)
        (fun _ => Iff.rfl) _).mpr
      refine ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), ?_, ?_⟩
      · rw [retained_darts_eq_image W n J K]
        exact ⟨a, haK, rfl⟩
      · have he : (g x : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath (φ t) := by
          have hz : (⟨(P.arc a).toPath t,
              hP (Or.inr ⟨a, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : X) = x :=
            Subtype.ext ht
          exact hz ▸ hφ t
        rw [he, ← Polyline.range_toPath]
        exact ⟨φ t, rfl⟩
  exact ⟨himage, ⟨g.subtype (fun x => not_congr (himage x).symm)⟩⟩


/- EXACT REMAINING OBLIGATIONS (comments, not premises or declarations).

The exported incidence comparison classifies each full-run exterior dart
against an actual unbounded target component. It does not prove that all such
components coincide. The relative-complement homeomorphisms do not identify
components after adjoining the omitted exterior. Thus none of the complete
Proposition 5.1, Lemma 5.2, stopped face-orbit, or assembly targets below is
claimed proved. No new orientation hypothesis is introduced. In particular,
the full-run target exterior still requires this statement:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (n : ℤ) (J : WholePlaneStartIso W n)
  (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let Q := inheritedDrawing W H G n univ
  ∃ U : Q.Face, Q.IsUnbounded U ∧
    (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
    (⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val)ᶜ = U.val

The following complete targets are copied without changed binders or clauses
from ShiftedStartGeometry4.lean. Their numbering is retained for comparison.

2. Exact Proposition 5.1 comparison (ShiftedStartGeometry.lean:425).

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
  (n : ℤ) (J : WholePlaneStartIso W n),
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  ∀ (hflow : HasFlowLineHits u)
    (hhat : hatLimitFiniteIncidence u)
    (hprime : primedLimitFiniteIncidence u)
    (hb : BoundaryHitWitnesses u),
  ∀ K : Set ℕ,
    K = {e | MhatGeometricEdge u e} ∨ K = {e | primeGeomEdge u hprime hb e} →
    let U := shiftWordInt W n
    let S := uibotWholePlaneSourceDomain W H G hp
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp (J.dart (wholePlaneDartι U 0 d)))
    let P := monotoneFamilyDrawing u hhat (monotone_family_all u)
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let Q := restrictDrawing P T (fun _ => Iff.rfl)
    ∃ R : Q.Face → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u K) (E '' K)) ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
      (∀ d : T, intrinsicFutureRotation A (E '' K)
        (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)

3. Exact Lemma 5.2 analogue (ShiftedStartGeometry.lean:463).

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (k : ℤ),
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := fun i => w (t + i)
  ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
  let S := uibotWholePlaneSourceDomain W H G hp
  let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
  let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
  let D := fun d : ℕ × Bool => intrinsicFutureDartEquiv (A := S) I
    (uibotCut2SourceDartEquiv W H h hpast hp
      (wholePlaneDartι W 0 (kmswWindowEdgeMapInf w t d.1, d.2)))
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let T := {d : ℕ × Bool | MhatGeometricEdge u d.1}
  let Q := hatRealizedDrawing u hfin
  ∃ R : Q.Face → Set ℂ,
    Function.Injective R ∧
    Set.range R = intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
    (∀ F, IsOpen (R F)) ∧
    (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
    (∀ d : T, intrinsicFutureRotation A (Set.range E)
      (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
    (∀ (d : T) (F : Q.Face),
      (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)


4. Exact nonzero-stopping-time face-orbit comparison
(IntrinsicConsumer52FaceOrbits.lean:376). Every binder is retained.

  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
  ∀ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (k : ℤ),
    let t := boundaryHitTime (shiftedStream W 0) h k
    let u := fun i => shiftedStream W 0 (t + i)
    ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
    let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
    let D := intrinsicConsumer52HatDart W H h hpast hp A I t hτ
    ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
      (∀ q, IsOpen (R q)) ∧
      (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
        Quotient.mk _ d = q) ∧
      (∀ q, (¬ Bornology.IsBounded (R q)) ↔
        q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
        (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d)


5. Exact Lemma 5.2 assembly (IntrinsicConsumer52FaceOrbits.lean:419).

  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
    ∃ (H : WholePlaneRotationHypothesis W)
      (h : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
      Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
      ∃! C : IntrinsicFutureCut2 A,
        (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
        ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root,
        let t := intrinsicStageBoundaryTime W H h hLL G hp A I
        t 0 = 0 ∧
        ∀ k : ℤ,
          IsLeast {n : ℕ | C.x k = intrinsicStageActiveInitial A
            (intrinsicStageActiveEdges W H G hp A I) n} (t k) ∧
          t k = boundaryHitTime (shiftedStream W 0) h k ∧
          boundaryCodeStoppingTime k (shiftedCodePath W 0) = (t k : ℕ∞) ∧
          wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
            wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
          wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
            iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
          (fun i => boundaryFutureCode k W (i + 1)) =
            (fun i => shiftedStream W 0 (t k + i)) ∧
          (∃ hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)),
            hatLawCodes (boundaryFutureCode k W) =
              hatCodes (fun i => shiftedStream W 0 (t k + i)) hτ) ∧
          M0CutShiftContainment W H h hLL k ∧
          boundaryFutureRootedMapClause W h k ∧
          IntrinsicStageShiftContainment W A
            (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j))
            (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j))
            C.edges C.missing (C.x k) (t k) ∧
          ∃ (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)))
            (hfin : hatLimitFiniteIncidence (fun i => shiftedStream W 0 (t k + i))),
          let u := fun i => shiftedStream W 0 (t k + i)
          let V := intrinsicConsumer52HatVertex W H G hp A I (t k) hτ
          let E := intrinsicConsumer52HatEdge W H G hp A I (t k) hτ
          let D := intrinsicConsumer52HatDart W H h hpast hp A I (t k) hτ
          hatLawCodes (boundaryFutureCode k W) = hatCodes u hτ ∧
          hatRootedMapClause u hτ hfin ∧
          Function.Injective E ∧
          E 0 = (intrinsicStageActiveEdges W H G hp A I (t k)).val ∧
          (∀ e : ℕ, ∃ he : ¬ A.map.missing (E e),
            A.map.tail ⟨E e, he⟩ = V (edgeWest (hatCodes u hτ) e) ∧
            A.map.head ⟨E e, he⟩ = V (edgeEast (hatCodes u hτ) e)) ∧
          (∀ d, intrinsicFutureRotation A (Set.range E)
            (D (kmswInfRot (hatCodes u hτ) (hatCodes_finiteIncidence u hτ hfin) d))
            (D d)) ∧
          ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
            Function.Injective R ∧
            Set.range R = intrinsicConsumer51FaceRegions
              (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
            (∀ q, IsOpen (R q)) ∧
            (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
              Quotient.mk _ d = q) ∧
            (∀ q, (¬ Bornology.IsBounded (R q)) ↔
              q = Quotient.mk _ futureMapOuterDart) ∧
            (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
              (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d) -/

end DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute
