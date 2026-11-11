/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry
public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation6

/-! Helper toward Proposition 3.9: compatible geometry for shifted starts.

The drawing-image comparison below keeps all geometric edges, including missing
edges. Extending it to the whole plane remains a separate obligation. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open Set Topology

private theorem paste_arc_charts {ι : Type*} (S T : ι → Set ℂ)
    (hS : LocallyFinite S) (hT : LocallyFinite T)
    (hclS : ∀ i, IsClosed (S i)) (hclT : ∀ i, IsClosed (T i))
    (E : ∀ i, S i ≃ₜ T i)
    (heq : ∀ i j (x : S i) (y : S j),
      (E i x : ℂ) = (E j y : ℂ) ↔ (x : ℂ) = (y : ℂ)) :
    ∃ g : (⋃ i, S i) ≃ₜ (⋃ i, T i),
      ∀ i (x : S i),
        (g ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) := by
  classical
  let A := ⋃ i, S i
  let B := ⋃ i, T i
  have hmem (x : A) : ∃ i, (x : ℂ) ∈ S i := mem_iUnion.mp x.property
  let idx (x : A) := (hmem x).choose
  have hx (x : A) : (x : ℂ) ∈ S (idx x) := (hmem x).choose_spec
  let f (x : A) : B :=
    ⟨E (idx x) ⟨x, hx x⟩, mem_iUnion.mpr ⟨idx x, (E (idx x) _).property⟩⟩
  have hf (i : ι) (x : S i) :
      (f ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) :=
    (heq _ _ _ _).mpr rfl
  have hfi : Function.Injective f := by
    intro x y h
    have hh : (E (idx x) ⟨x, hx x⟩ : ℂ) = (E (idx y) ⟨y, hx y⟩ : ℂ) :=
      congrArg Subtype.val h
    exact Subtype.ext ((heq _ _ _ _).mp hh)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp y.property
    refine ⟨⟨(E i).symm ⟨y, hi⟩, mem_iUnion.mpr
      ⟨i, ((E i).symm ⟨y, hi⟩).property⟩⟩, ?_⟩
    exact Subtype.ext ((hf i _).trans
      (congrArg Subtype.val ((E i).apply_symm_apply _)))
  let a : ι → Set A := fun i => Subtype.val ⁻¹' S i
  let b : ι → Set B := fun i => Subtype.val ⁻¹' T i
  have ha : LocallyFinite a := hS.preimage_continuous continuous_subtype_val
  have hb : LocallyFinite b := hT.preimage_continuous continuous_subtype_val
  have hac : ⋃ i, a i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hbc : ⋃ i, b i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hfc : Continuous f := ha.continuous hac
      (fun i => (hclS i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun x : a i => (f x.val : ℂ)) =
        fun x => (E i ⟨x.val.val, x.property⟩ : ℂ) :=
      funext fun x => hf i ⟨x.val.val, x.property⟩
    rw [he]
    exact continuous_subtype_val.comp ((E i).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  have hinv (i : ι) (y : T i) :
      (e.symm ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ : ℂ) =
        ((E i).symm y : ℂ) := by
    have hh : e ⟨(E i).symm y,
        mem_iUnion.mpr ⟨i, ((E i).symm y).property⟩⟩ =
        ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ :=
      Subtype.ext ((hf i _).trans (congrArg Subtype.val ((E i).apply_symm_apply y)))
    exact congrArg Subtype.val ((congrArg e.symm hh).symm.trans (e.symm_apply_apply _))
  have hic : Continuous e.symm := hb.continuous hbc
      (fun i => (hclT i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun y : b i => (e.symm y.val : ℂ)) =
        fun y => ((E i).symm ⟨y.val.val, y.property⟩ : ℂ) :=
      funext fun y => hinv i ⟨y.val.val, y.property⟩
    change Continuous (fun y : b i => (e.symm y.val : ℂ))
    erw [he]
    exact continuous_subtype_val.comp ((E i).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  exact ⟨{ toEquiv := e, continuous_toFun := hfc, continuous_invFun := hic }, hf⟩

private theorem arc_family_locallyFinite
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) : LocallyFinite (fun d => (P.arc d).image) := by
  intro z
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
  simpa only [inter_comm] using P.locally_finite (Metric.ball z 1) Metric.isBounded_ball

private theorem start_dart_injective (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n) :
    Function.Injective (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) := by
  intro d e h
  have hh := J.dart.injective h
  change (wholePlaneEdgeι (shiftWordInt W n) 0 d.1, d.2) =
    (wholePlaneEdgeι (shiftWordInt W n) 0 e.1, e.2) at hh
  exact Prod.ext (wholePlaneEdgeι_injective _ 0 (congrArg Prod.fst hh))
    (congrArg (fun q : WholePlaneEdge (shiftWordInt W n) × Bool => q.2) hh)

private theorem start_dart_flip (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n) (d : ℕ × Bool) :
    J.dart (wholePlaneDartι (shiftWordInt W n) 0 (d.1, !d.2)) =
      wholePlaneDartFlip W (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) := by
  erw [J.dart_apply, J.dart_apply]
  rfl

/-- Helper toward Proposition 3.9: corresponding geometric edges at an
integer start admit one compatible family of charts. The resulting map is a
homeomorphism of the complete edge unions, with both named endpoints matched.
This is a drawing-image map; it does not yet extend over the plane's faces. -/
theorem exists_edge_union_homeomorph (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let U := shiftWordInt W n
    let u := shiftedStream U 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let D := fun d => J.dart (wholePlaneDartι U 0 d)
    let V := fun v => J.vertex (wholePlaneVertexι U 0 v)
    ∃ g : (⋃ e : ℕ, (P.arc (e, false)).image) ≃ₜ
        (⋃ e : ℕ, (G.arc (D (e, false))).image),
      (∀ e, g '' {x : (⋃ e : ℕ, (P.arc (e, false)).image) |
          (x : ℂ) ∈ (P.arc (e, false)).image} =
        {y : (⋃ e : ℕ, (G.arc (D (e, false))).image) |
          (y : ℂ) ∈ (G.arc (D (e, false))).image}) ∧
      ∀ (e : ℕ) (x : (P.arc (e, false)).image) (v : ℕ),
        (x : ℂ) = P.pos v →
        (g ⟨x, mem_iUnion.mpr ⟨e, x.property⟩⟩ : ℂ) = G.pos (V v) := by
  classical
  intro U u P D V
  let S := fun e : ℕ => (P.arc (e, false)).image
  let T := fun e : ℕ => (G.arc (D (e, false))).image
  have hV : Function.Injective V := J.vertex.injective.comp (wholePlaneVertexι_injective U 0)
  have hD : Function.Injective D := start_dart_injective W n J
  have hv (d : ℕ × Bool) : wholePlaneDartVertex W (D d) = V (kmswLimitDartVertex u d) := by
    exact (start_iso_dart_vertex W n J _).trans
      (congrArg J.vertex (wholePlaneDartVertex_ι U 0 d))
  have hs (e : ℕ) : (G.arc (D (e, false))).start = G.pos (V (edgeWest u e)) := by
    rw [G.arc_start, hv]
    rfl
  have ht (e : ℕ) : (G.arc (D (e, false))).finish = G.pos (V (edgeEast u e)) := by
    rw [G.arc_finish, ← start_dart_flip W n J (e, false), hv]
    rfl
  have hp0 (e : ℕ) : (P.arc (e, false)).start = P.pos (edgeWest u e) := P.arc_start _
  have hp1 (e : ℕ) : (P.arc (e, false)).finish = P.pos (edgeEast u e) := P.arc_finish _
  have hpne (e : ℕ) : (P.arc (e, false)).start ≠ (P.arc (e, false)).finish := by
    rw [P.arc_start, P.arc_finish]
    exact fun h => P.vert_ne_flip _ (P.pos_injective h)
  have hgne (e : ℕ) : (G.arc (D (e, false))).start ≠ (G.arc (D (e, false))).finish := by
    rw [G.arc_start, G.arc_finish]
    exact fun h => G.vert_ne_flip _ (G.pos_injective h)
  choose a ha0 ha1 using fun e => (P.arc (e, false)).exists_Icc_homeomorph_image
    (P.arc_simple _) (hpne e)
  choose b hb0 hb1 using fun e => (G.arc (D (e, false))).exists_Icc_homeomorph_image
    (G.arc_simple _) (hgne e)
  have hA (e f : ℕ) (hef : e ≠ f) :
      S e ∩ S f ⊆ {P.pos (edgeWest u e), P.pos (edgeEast u e)} := by
    intro z hz
    have hh := (P.arc_intersection_endpoints (e, false) (f, false)
      (fun h => hef (congrArg Prod.fst h).symm)
      (fun h => Bool.false_ne_true (congrArg Prod.snd h)) hz.1 hz.2).1
    rwa [hp0, hp1] at hh
  have hB (e f : ℕ) (hef : e ≠ f) :
      T e ∩ T f ⊆ {G.pos (V (edgeWest u e)), G.pos (V (edgeEast u e))} := by
    intro z hz
    have hne : D (f, false) ≠ D (e, false) :=
      fun h => hef (congrArg Prod.fst (hD h)).symm
    have hflip : D (f, false) ≠ wholePlaneDartFlip W (D (e, false)) := by
      rw [← start_dart_flip W n J (e, false)]
      exact fun h => Bool.false_ne_true (congrArg Prod.snd (hD h))
    have hh := (G.arc_intersection_endpoints _ _ hne hflip hz.1 hz.2).1
    rwa [hs, ht] at hh
  have hcollision := parameterized_arcs_collision_iff_of_vertices S T P.pos
    (fun v => G.pos (V v)) P.pos_injective (G.pos_injective.comp hV)
    (edgeWest u) (edgeEast u) a b
    (fun e => (ha0 e).trans (hp0 e)) (fun e => (ha1 e).trans (hp1 e))
    (fun e => (hb0 e).trans (hs e)) (fun e => (hb1 e).trans (ht e)) hA hB
  let E := fun e => (a e).symm.trans (b e)
  have heq (e f : ℕ) (x : S e) (y : S f) :
      (E e x : ℂ) = (E f y : ℂ) ↔ (x : ℂ) = (y : ℂ) := by
    change (b e ((a e).symm x) : ℂ) = (b f ((a f).symm y) : ℂ) ↔ _
    have hh := hcollision e f ((a e).symm x) ((a f).symm y)
    simpa only [Homeomorph.apply_symm_apply] using hh.symm
  obtain ⟨g, hg⟩ := paste_arc_charts S T
    ((arc_family_locallyFinite P).comp_injective (fun _ _ h => congrArg Prod.fst h))
    ((arc_family_locallyFinite G).comp_injective
      (hD.comp (fun _ _ h => congrArg Prod.fst h)))
    (fun e => (P.arc (e, false)).isCompact_image.isClosed)
    (fun e => (G.arc (D (e, false))).isCompact_image.isClosed) E heq
  refine ⟨g, ?_, ?_⟩
  · intro e
    change g '' {x : (⋃ i, S i) | (x : ℂ) ∈ S e} =
      {y : (⋃ i, T i) | (y : ℂ) ∈ T e}
    apply Set.ext
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (g x : ℂ) ∈ T e
      rw [show (g x : ℂ) = (E e ⟨x, hx⟩ : ℂ) from hg e ⟨x, hx⟩]
      exact (E e _).property
    · intro hy
      refine ⟨⟨(E e).symm ⟨y, hy⟩, mem_iUnion.mpr
        ⟨e, ((E e).symm ⟨y, hy⟩).property⟩⟩, ((E e).symm ⟨y, hy⟩).property, ?_⟩
      exact Subtype.ext ((hg e _).trans
        (congrArg Subtype.val ((E e).apply_symm_apply _)))
  · intro e x v hx
    rw [hg]
    have hend : (x : ℂ) = (P.arc (e, false)).start ∨
        (x : ℂ) = (P.arc (e, false)).finish := by
      by_contra hn
      exact P.interior_avoids_vertices (e, false) v
        (hx ▸ ⟨x.property, hn⟩)
    rcases hend with hx0 | hx1
    · have hax : x = a e ⟨-1, by norm_num⟩ := Subtype.ext (hx0.trans (ha0 e).symm)
      have hv0 : edgeWest u e = v := P.pos_injective ((hp0 e).symm.trans (hx0.symm.trans hx))
      change (b e ((a e).symm x) : ℂ) = _
      rw [hax, Homeomorph.symm_apply_apply, hb0, hs, hv0]
    · have hax : x = a e ⟨1, by norm_num⟩ := Subtype.ext (hx1.trans (ha1 e).symm)
      have hv1 : edgeEast u e = v := P.pos_injective ((hp1 e).symm.trans (hx1.symm.trans hx))
      change (b e ((a e).symm x) : ℂ) = _
      rw [hax, Homeomorph.symm_apply_apply, hb1, ht, hv1]

private theorem run_image_eq_forward_arcs (u : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence u) :
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    P.image = ⋃ e : ℕ, (P.arc (e, false)).image := by
  intro P
  rw [P.image_eq_union_arcs (kmswLimitDartVertex_surjective u hfin)]
  ext z
  constructor
  · intro hz
    obtain ⟨⟨e, b⟩, he⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨e, ?_⟩
    cases b
    · exact he
    · have hh := P.arc_image_flip (e, false)
      exact hh ▸ he
  · intro hz
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨(e, false), he⟩

private theorem inherited_image_eq_forward_arcs (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (J : WholePlaneStartIso W n) :
    (inheritedDrawing W H G n univ).image =
      ⋃ e : ℕ, (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 (e, false)))).image := by
  let Q := inheritedDrawing W H G n univ
  have hvert : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  change Q.image = _
  rw [Q.image_eq_union_arcs hvert]
  ext z
  constructor
  · intro hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp hz
    have hm := (Set.ext_iff.mp (retained_darts_eq_image W n J univ) d.val).mp d.property
    obtain ⟨⟨e, b⟩, _, he⟩ := hm
    change z ∈ (G.arc d.val).image at hd
    rw [← he] at hd
    refine mem_iUnion.mpr ⟨e, ?_⟩
    cases b
    · exact hd
    · have hh := (congrArg (fun q : WholePlaneDart W => (G.arc q).image)
        (start_dart_flip W n J (e, false))).trans (G.arc_image_flip _)
      exact hh ▸ hd
  · intro hz
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    have hm : J.dart (wholePlaneDartι (shiftWordInt W n) 0 (e, false)) ∈
        retainedDarts W n univ := by
      rw [retained_darts_eq_image W n J univ]
      exact ⟨(e, false), mem_univ _, rfl⟩
    exact mem_iUnion.mpr ⟨⟨_, hm⟩, he⟩

/-- Helper toward Proposition 3.9: a single homeomorphism of the shifted
drawing image onto the inherited drawing image matches every vertex and every
geometric dart with an increasing parameter. Continuity of its inverse follows
from local finiteness on the target side. No ambient extension is asserted. -/
theorem exists_drawing_image_homeomorph (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let U := shiftWordInt W n
    let u := shiftedStream U 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let Q := inheritedDrawing W H G n univ
    ∃ Φ : P.image ≃ₜ Q.image,
      (∀ v, (Φ ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι U 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (Φ ⟨(P.arc d).toPath t,
            Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι U 0 d))).toPath (φ t)) := by
  classical
  intro U u P Q
  let D := fun d => J.dart (wholePlaneDartι U 0 d)
  let V := fun v => J.vertex (wholePlaneVertexι U 0 v)
  let S := fun e : ℕ => (P.arc (e, false)).image
  let T := fun e : ℕ => (G.arc (D (e, false))).image
  obtain ⟨g, hg, hgv⟩ := exists_edge_union_homeomorph W H G n J hfin
  have hS : P.image = ⋃ e, S e := run_image_eq_forward_arcs u hfin
  have hT : Q.image = ⋃ e, T e := inherited_image_eq_forward_arcs W H G n J
  let Φ : P.image ≃ₜ Q.image :=
    (Homeomorph.setCongr hS).trans (g.trans (Homeomorph.setCongr hT.symm))
  have hv (v : ℕ) : (Φ ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) = G.pos (V v) := by
    have hm : P.pos v ∈ ⋃ e, S e := hS ▸ (Or.inl ⟨v, rfl⟩ : P.pos v ∈ P.image)
    obtain ⟨e, he⟩ := mem_iUnion.mp hm
    exact hgv e ⟨P.pos v, he⟩ v rfl
  have harc (d : ℕ × Bool) :
      Φ '' {x : P.image | (x : ℂ) ∈ (P.arc d).image} =
        {y : Q.image | (y : ℂ) ∈ (G.arc (D d)).image} := by
    rcases d with ⟨e, b⟩
    have hh := hg e
    have hfalse :
        Φ '' {x : P.image | (x : ℂ) ∈ (P.arc (e, false)).image} =
          {y : Q.image | (y : ℂ) ∈ (G.arc (D (e, false))).image} := by
      apply Set.ext
      intro y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hm : g ((Homeomorph.setCongr hS) x) ∈
            {y : (⋃ e, T e) | (y : ℂ) ∈ T e} :=
          hh ▸ ⟨(Homeomorph.setCongr hS) x, hx, rfl⟩
        exact hm
      · intro hy
        have hm : (Homeomorph.setCongr hT) y ∈
            g '' {x : (⋃ e, S e) | (x : ℂ) ∈ S e} := hh.symm ▸ hy
        obtain ⟨x, hx, hxy⟩ := hm
        refine ⟨(Homeomorph.setCongr hS.symm) x, hx, ?_⟩
        exact Subtype.ext (congrArg (fun x : (⋃ e, T e) => (x : ℂ)) hxy)
    cases b
    · exact hfalse
    · have hpflip := P.arc_image_flip (e, false)
      have hgflip := G.arc_image_flip (D (e, false))
      rw [← start_dart_flip W n J (e, false)] at hgflip
      change (P.arc (e, true)).image = (P.arc (e, false)).image at hpflip
      change (G.arc (D (e, true))).image = (G.arc (D (e, false))).image at hgflip
      rw [hpflip, hgflip]
      exact hfalse
  refine ⟨Φ, hv, ?_⟩
  intro d
  have hm (t : unitInterval) : (P.arc d).toPath t ∈ P.image :=
    Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩
  let f (t : unitInterval) : ℂ := Φ ⟨(P.arc d).toPath t, hm t⟩
  have hf : Continuous f := continuous_subtype_val.comp
    (Φ.continuous.comp ((P.arc d).toPath.continuous.subtype_mk hm))
  have hfi : Function.Injective f := by
    intro s t h
    apply (P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d)
    exact congrArg Subtype.val (Φ.injective (Subtype.ext h))
  have hdv : wholePlaneDartVertex W (D d) = V (kmswLimitDartVertex u d) :=
    (start_iso_dart_vertex W n J _).trans
      (congrArg J.vertex (wholePlaneDartVertex_ι U 0 d))
  have hf0 : f 0 = (G.arc (D d)).start := by
    change (Φ ⟨(P.arc d).toPath 0, hm 0⟩ : ℂ) = _
    simp only [Path.source, P.arc_start]
    exact (hv _).trans (congrArg G.pos hdv).symm |>.trans (G.arc_start _).symm
  have hf1 : f 1 = (G.arc (D d)).finish := by
    change (Φ ⟨(P.arc d).toPath 1, hm 1⟩ : ℂ) = _
    simp only [Path.target, P.arc_finish]
    have hh := (start_iso_dart_vertex W n J
      (wholePlaneDartι U 0 (d.1, !d.2))).trans
      (congrArg J.vertex (wholePlaneDartVertex_ι U 0 (d.1, !d.2)))
    rw [start_dart_flip W n J d] at hh
    exact (hv _).trans (congrArg G.pos hh).symm |>.trans (G.arc_finish _).symm
  let γ : Path (G.arc (D d)).start (G.arc (D d)).finish :=
    ⟨⟨f, hf⟩, hf0, hf1⟩
  have hrange : Set.range γ = Set.range (G.arc (D d)).toPath := by
    rw [Polyline.range_toPath]
    apply Set.ext
    intro z
    constructor
    · rintro ⟨t, rfl⟩
      have hh : Φ ⟨(P.arc d).toPath t, hm t⟩ ∈
          {y : Q.image | (y : ℂ) ∈ (G.arc (D d)).image} :=
        harc d ▸ ⟨⟨(P.arc d).toPath t, hm t⟩,
          (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩, rfl⟩
      exact hh
    · intro hz
      have hzQ : z ∈ Q.image := by
        have hdret : D d ∈ retainedDarts W n univ := by
          rw [retained_darts_eq_image W n J univ]
          exact ⟨d, mem_univ _, rfl⟩
        exact Or.inr ⟨⟨D d, hdret⟩, hz⟩
      have hh : (⟨z, hzQ⟩ : Q.image) ∈
          Φ '' {x : P.image | (x : ℂ) ∈ (P.arc d).image} := (harc d).symm ▸ hz
      obtain ⟨x, hx, hxy⟩ := hh
      rw [← Polyline.range_toPath] at hx
      obtain ⟨t, ht⟩ := hx
      refine ⟨t, ?_⟩
      have he : (⟨(P.arc d).toPath t, hm t⟩ : P.image) = x := Subtype.ext ht
      change (Φ ⟨(P.arc d).toPath t, hm t⟩ : ℂ) = z
      rw [he]
      exact congrArg Subtype.val hxy
  obtain ⟨φ, h0, h1, hφ⟩ := exists_path_reparam_of_injective_range_eq
    (G.arc (D d)).toPath γ
    ((G.arc (D d)).toPath_injective (G.arc_length _) (G.arc_simple _)) hfi hrange
  refine ⟨φ, φ.continuous.strictMono_of_inj_boundedOrder
    (by change φ 0 ≤ φ 1; rw [h0, h1]; exact zero_le_one) φ.injective, ?_⟩
  intro t
  exact congrArg (fun p : Path (G.arc (D d)).start (G.arc (D d)).finish => p t) hφ

/-- Helper toward Proposition 3.9: the zero-start instance of the ambient
comparison holds for every start isomorphism, since its run-zero embeddings are
fixed and the glued drawing retains these exact positions and polylines. -/
theorem exists_ambient_homeomorph_zero (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (J : WholePlaneStartIso W 0)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W 0) 0)) :
    let U := shiftWordInt W 0
    let u := shiftedStream U 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∃ Φ : ℂ ≃ₜ ℂ, OrientationPreserving Φ ∧
      (∀ v, Φ (P.pos v) = G.pos (J.vertex (wholePlaneVertexι U 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          Φ ((P.arc d).toPath t) =
            (G.arc (J.dart (wholePlaneDartι U 0 d))).toPath (φ t)) := by
  intro U u P G
  have hu : u = shiftedStream W 0 := by
    funext i
    simp only [u, U, shiftedStream, shiftWordInt, Int.add_zero]
  have hpos_congr (a b : ℕ → Fin 3) (hab : a = b)
      (ha : hatLimitFiniteIncidence a) (hb : hatLimitFiniteIncidence b) :
      (monotoneFamilyDrawing a ha (monotone_family_all a)).pos =
        (monotoneFamilyDrawing b hb (monotone_family_all b)).pos := by
    subst b
    rfl
  have harc_congr (a b : ℕ → Fin 3) (hab : a = b)
      (ha : hatLimitFiniteIncidence a) (hb : hatLimitFiniteIncidence b) :
      (monotoneFamilyDrawing a ha (monotone_family_all a)).arc =
        (monotoneFamilyDrawing b hb (monotone_family_all b)).arc := by
    subst b
    rfl
  have hvertex (v : ℕ) : J.vertex (wholePlaneVertexι U 0 v) = wholePlaneVertexι W 0 v := by
    rw [J.iota_vertex]
    simp only [lemma38StartVertexι, le_refl, ite_true, Int.natAbs_zero]
  have hdart (d : ℕ × Bool) :
      J.dart (wholePlaneDartι U 0 d) = wholePlaneDartι W 0 d := by
    erw [J.dart_apply, J.iota_edge]
    simp only [lemma38StartEdgeι, le_refl, ite_true, Int.natAbs_zero]
    rfl
  have hp (v : ℕ) : G.pos (J.vertex (wholePlaneVertexι U 0 v)) = P.pos v := by
    rw [hvertex]
    change (WholePlanePastGlueData.gluedPos W h hpast H) (wholePlaneVertexι W 0 v) = _
    rw [WholePlanePastGlueData.gluedPos_runZero]
    exact (congrFun (hpos_congr u _ hu hfin (H.1 0)) v).symm
  have ha (d : ℕ × Bool) : G.arc (J.dart (wholePlaneDartι U 0 d)) = P.arc d := by
    rw [hdart]
    change (WholePlanePastGlueData.gluedArc W h hpast H) (wholePlaneDartι W 0 d) = _
    rw [WholePlanePastGlueData.gluedArc_runZero]
    exact (congrFun (harc_congr u _ hu hfin (H.1 0)) d).symm
  refine ⟨Homeomorph.refl ℂ, orientationPreserving_refl, fun v => (hp v).symm, ?_⟩
  intro d
  refine ⟨Homeomorph.refl unitInterval, fun _ _ hlt => hlt, ?_⟩
  intro t
  rw [ha]
  rfl














































































































end DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry
