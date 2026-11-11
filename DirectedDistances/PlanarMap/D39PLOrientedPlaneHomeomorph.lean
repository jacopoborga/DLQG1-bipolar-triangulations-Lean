/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLOuterChart3
public import DirectedDistances.PlanarMap.D39WindingDegree
public import DirectedDistances.PlanarMap.D39PLFaceWalkWinding2

/- # Face-preserving plane extensions

belong to the sole coordinator. No numbered paper result is claimed here. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set Topology

namespace PLDrawing

/-- Helper toward Proposition 5.16: deleting the drawing from the closure
of a complementary face recovers that face, including for the exterior. -/
theorem closure_face_diff_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (F : P.Face) : closure F.val \ P.image = F.val := by
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    by_contra hxf
    have hfront : x ∈ frontier F.val := by
      rw [frontier, (P.face_open_frontier_subset_image hvert F).1.interior_eq]
      exact ⟨hx, hxf⟩
    exact hxi ((P.face_open_frontier_subset_image hvert F).2 hfront)
  · intro hx
    exact ⟨subset_closure hx, P.face_subset_compl F hx⟩

end PLDrawing

/-- Helper toward Proposition 5.16: logarithmic lift increments depend only
on the path's underlying function, with arbitrary endpoint casts. -/
theorem hasLiftIncrement_congr_fun {a b a' b' w c : ℂ}
    (γ : Path a b) (δ : Path a' b') (heq : ∀ t, γ t = δ t) :
    HasLiftIncrement γ w c ↔ HasLiftIncrement δ w c := by
  constructor
  · rintro ⟨φ, hφ, hi⟩
    exact ⟨φ, fun t => (hφ t).trans (congrArg (fun x => x - w) (heq t)), hi⟩
  · rintro ⟨φ, hφ, hi⟩
    exact ⟨φ, fun t => (hφ t).trans (congrArg (fun x => x - w) (heq t).symm), hi⟩

/-- Helper toward Proposition 5.16: every logarithmic lift of a concatenated
path splits into lifts of the two traversals, with additive increments. -/
theorem hasLiftIncrement_trans_iff {a b c w v : ℂ}
    (γ : Path a b) (δ : Path b c) :
    HasLiftIncrement (γ.trans δ) w v ↔
      ∃ v₁ v₂ : ℂ, HasLiftIncrement γ w v₁ ∧ HasLiftIncrement δ w v₂ ∧
        v = v₁ + v₂ := by
  constructor
  · rintro ⟨φ, hφ, hi⟩
    let lo : C(unitInterval, unitInterval) :=
      ⟨fun t => ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩,
        by fun_prop⟩
    let hiParam : C(unitInterval, unitInterval) :=
      ⟨fun t => ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩,
        by fun_prop⟩
    have hlo (t : unitInterval) : (γ.trans δ) (lo t) = γ t := by
      rw [← Path.extend_extends', Path.extend_trans_of_le_half γ δ
        (by change (t : ℝ) / 2 ≤ 1 / 2; linarith [t.2.2])]
      change γ.extend (2 * ((t : ℝ) / 2)) = γ t
      rw [show 2 * ((t : ℝ) / 2) = (t : ℝ) by ring, Path.extend_extends']
    have hhi (t : unitInterval) : (γ.trans δ) (hiParam t) = δ t := by
      rw [← Path.extend_extends', Path.extend_trans_of_half_le γ δ
        (by change 1 / 2 ≤ ((t : ℝ) + 1) / 2; linarith [t.2.1])]
      change δ.extend (2 * (((t : ℝ) + 1) / 2) - 1) = δ t
      rw [show 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ) by ring,
        Path.extend_extends']
    refine ⟨φ (lo 1) - φ (lo 0), φ (hiParam 1) - φ (hiParam 0),
      ⟨φ.comp lo, fun t => (hφ (lo t)).trans (congrArg (fun x => x - w) (hlo t)), rfl⟩,
      ⟨φ.comp hiParam,
        fun t => (hφ (hiParam t)).trans (congrArg (fun x => x - w) (hhi t)), rfl⟩, ?_⟩
    have hlo0 : lo 0 = 0 := by apply Subtype.ext; norm_num [lo]
    have hhi1 : hiParam 1 = 1 := by apply Subtype.ext; norm_num [hiParam]
    have hmid : lo 1 = hiParam 0 := by apply Subtype.ext; norm_num [lo, hiParam]
    rw [hlo0, hhi1, ← hmid, ← hi]
    ring
  · rintro ⟨v₁, v₂, h₁, h₂, rfl⟩
    exact hasLiftIncrement_trans h₁ h₂

/-- Helper toward Proposition 5.16: splitting the first segment of a list
traversal splits its logarithmic lift increment after a continuous map. -/
theorem hasLiftIncrement_listPath_cons_cons_iff
    (F : C(ℂ, ℂ)) (w a b c : ℂ) (l : List ℂ) (v : ℂ) :
    HasLiftIncrement ((Polyline.listPath a (b :: c :: l)).map F.continuous) w v ↔
      ∃ v₁ v₂ : ℂ,
        HasLiftIncrement ((Path.segment a b).map F.continuous) w v₁ ∧
        HasLiftIncrement ((Polyline.listPath b (c :: l)).map F.continuous) w v₂ ∧
        v = v₁ + v₂ := by
  have heq := Path.map_trans (Path.segment a b) (Polyline.listPath b (c :: l))
    F.continuous
  exact (hasLiftIncrement_congr_fun _ _
    (fun t => congrArg (fun p => p t) heq)).trans (hasLiftIncrement_trans_iff _ _)

/-- Helper toward Proposition 5.16: concatenating nonempty vertex lists
adds lift increments even though the recursive traversal schedules differ. -/
theorem hasLiftIncrement_listPath_append_iff
    (F : C(ℂ, ℂ)) (w : ℂ) (a : ℂ) (l m : List ℂ)
    (hl : l ≠ []) (hm : m ≠ []) (v : ℂ) :
    HasLiftIncrement ((Polyline.listPath a (l ++ m)).map F.continuous) w v ↔
      ∃ v₁ v₂ : ℂ,
        HasLiftIncrement ((Polyline.listPath a l).map F.continuous) w v₁ ∧
        HasLiftIncrement
          ((Polyline.listPath ((a :: l).getLast (by simp)) m).map F.continuous) w v₂ ∧
        v = v₁ + v₂ := by
  induction l generalizing a v with
  | nil => exact (hl rfl).elim
  | cons b l ih =>
    cases l with
    | nil =>
      cases m with
      | nil => exact (hm rfl).elim
      | cons c m =>
        exact hasLiftIncrement_listPath_cons_cons_iff F w a b c m v
    | cons c l =>
      change HasLiftIncrement
        ((Polyline.listPath a (b :: c :: (l ++ m))).map F.continuous) w v ↔
        ∃ v₁ v₂ : ℂ,
          HasLiftIncrement
            ((Polyline.listPath a (b :: c :: l)).map F.continuous) w v₁ ∧
          HasLiftIncrement
            ((Polyline.listPath ((b :: c :: l).getLast (by simp)) m).map F.continuous)
              w v₂ ∧ v = v₁ + v₂
      constructor
      · intro hv
        obtain ⟨s, t, hs, ht, hst⟩ :=
          (hasLiftIncrement_listPath_cons_cons_iff F w a b c (l ++ m) v).mp hv
        obtain ⟨t₁, t₂, ht₁, ht₂, htt⟩ := (ih b (by simp) t).mp ht
        exact ⟨s + t₁, t₂,
          (hasLiftIncrement_listPath_cons_cons_iff F w a b c l _).mpr
            ⟨s, t₁, hs, ht₁, rfl⟩, ht₂,
          by rw [hst, htt, add_assoc]⟩
      · rintro ⟨v₁, v₂, h₁, h₂, hv⟩
        obtain ⟨s, t, hs, ht, hst⟩ :=
          (hasLiftIncrement_listPath_cons_cons_iff F w a b c l v₁).mp h₁
        have htail := (ih b (by simp) (t + v₂)).mpr ⟨t, v₂, ht, h₂, rfl⟩
        apply (hasLiftIncrement_listPath_cons_cons_iff F w a b c (l ++ m) v).mpr
        exact ⟨s, t + v₂, hs, htail, by rw [hv, hst, add_assoc]⟩

/-- Helper toward Proposition 5.16: closed-face concatenation preserves the
sum of the two logarithmic lift increments, before or after a continuous map. -/
theorem hasLiftIncrement_boundaryConcat_iff
    (F : C(ℂ, ℂ)) (p q : Polyline)
    (hp : 2 ≤ p.points.length) (hq : 2 ≤ q.points.length)
    (hjoin : p.finish = q.start) (w v : ℂ) :
    HasLiftIncrement ((p.boundaryConcat q).toPath.map F.continuous) w v ↔
      ∃ v₁ v₂ : ℂ,
        HasLiftIncrement (p.toPath.map F.continuous) w v₁ ∧
        HasLiftIncrement (q.toPath.map F.continuous) w v₂ ∧ v = v₁ + v₂ := by
  rcases p with ⟨pp, hpp⟩
  rcases q with ⟨qq, hqq⟩
  cases pp with
  | nil => exact (hpp rfl).elim
  | cons a l =>
    cases qq with
    | nil => exact (hqq rfl).elim
    | cons b m =>
      have hl : l ≠ [] := by intro he; simp [he] at hp
      have hm : m ≠ [] := by intro he; simp [he] at hq
      have hab : (a :: l).getLast (by simp) = b := hjoin
      subst b
      have h := hasLiftIncrement_listPath_append_iff F w a l m hl hm v
      exact h

namespace D39FiniteBall

variable {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)
  (hconn : ∀ d e : B.D, Relation.EqvGen
    (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)

include hconn

/-- Helper toward Proposition 5.16: gluing all the closed face extensions
retains their images as well as the prescribed values on the drawing. -/
theorem exists_plane_homeomorph_mapping_closed_faces
    (f : B.PLImageHomeomorph vert P P')
    (extensions : ∀ O : D39BallFaceCycleOrbit B,
      ∃ H : closure (B.plOrbitFace vert P hvert O).val ≃ₜ
          closure (B.plOrbitFace vert P' hvert O).val,
        ∀ (x : closure (B.plOrbitFace vert P hvert O).val)
          (hx : (x : ℂ) ∈ P.image),
          (H x : ℂ) = (f.toHomeomorph ⟨x, hx⟩ : ℂ)) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ x : P.image, H x = (f.toHomeomorph x : ℂ)) ∧
      (∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      ∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val := by
  classical
  have : Finite (D39BallFaceCycleOrbit B) := Finite.of_injective
    (fun O : D39BallFaceCycleOrbit B => O.val) Subtype.val_injective
  choose E hE using extensions
  have hE' (O) := B.plOrbitFace_homeomorph_symm_agrees vert P P' hvert hconn
    f O (E O) (hE O)
  let s : Option (D39BallFaceCycleOrbit B) → Set ℂ
    | none => P.image
    | some O => closure (B.plOrbitFace vert P hvert O).val
  let t : Option (D39BallFaceCycleOrbit B) → Set ℂ
    | none => P'.image
    | some O => closure (B.plOrbitFace vert P' hvert O).val
  let e : ∀ i, s i ≃ₜ t i
    | none => f.toHomeomorph
    | some O => E O
  have hs : ∀ i, IsClosed (s i) := by
    rintro (_ | O)
    · exact P.isCompact_image.isClosed
    · exact isClosed_closure
  have ht : ∀ i, IsClosed (t i) := by
    rintro (_ | O)
    · exact P'.isCompact_image.isClosed
    · exact isClosed_closure
  have hagree : ∀ i j (x : ℂ) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : ℂ) = (e j ⟨x, hj⟩ : ℂ) := by
    rintro (_ | O) (_ | Q) x hi hj
    · rfl
    · exact (hE Q ⟨x, hj⟩ hi).symm
    · exact hE O ⟨x, hi⟩ hj
    · by_cases heq : O = Q
      · subst Q; rfl
      have hne : B.plOrbitFace vert P hvert O ≠ B.plOrbitFace vert P hvert Q :=
        fun h => heq (B.plOrbitFace_injective vert P hvert hconn h)
      have hx := P.closure_face_inter_subset_image hvert _ _ hne ⟨hi, hj⟩
      exact (hE O ⟨x, hi⟩ hx).trans (hE Q ⟨x, hj⟩ hx).symm
  have hagree' : ∀ i j (y : ℂ) (hi : y ∈ t i) (hj : y ∈ t j),
      ((e i).symm ⟨y, hi⟩ : ℂ) = ((e j).symm ⟨y, hj⟩ : ℂ) := by
    rintro (_ | O) (_ | Q) y hi hj
    · rfl
    · exact (hE' Q ⟨y, hj⟩ hi).symm
    · exact hE' O ⟨y, hi⟩ hj
    · by_cases heq : O = Q
      · subst Q; rfl
      have hne : B.plOrbitFace vert P' hvert O ≠ B.plOrbitFace vert P' hvert Q :=
        fun h => heq (B.plOrbitFace_injective vert P' hvert hconn h)
      have hy := P'.closure_face_inter_subset_image hvert _ _ hne ⟨hi, hj⟩
      exact (hE' O ⟨y, hi⟩ hy).trans (hE' Q ⟨y, hj⟩ hy).symm
  obtain ⟨G, hG⟩ := exists_homeomorph_iUnion_closed_sets s t hs ht e hagree hagree'
  have hsU : (⋃ i, s i) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ P.image
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨F, hxF⟩ := (P.faces_cover_compl x).mpr hx
      obtain ⟨O, rfl⟩ := B.plOrbitFace_surjective vert P hvert F
      exact mem_iUnion.mpr ⟨some O, subset_closure hxF⟩
  have htU : (⋃ i, t i) = univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ P'.image
    · exact mem_iUnion.mpr ⟨none, hy⟩
    · obtain ⟨F, hyF⟩ := (P'.faces_cover_compl y).mpr hy
      obtain ⟨O, rfl⟩ := B.plOrbitFace_surjective vert P' hvert F
      exact mem_iUnion.mpr ⟨some O, subset_closure hyF⟩
  let a := (Homeomorph.setCongr hsU).trans (Homeomorph.Set.univ ℂ)
  let b := (Homeomorph.setCongr htU).trans (Homeomorph.Set.univ ℂ)
  let H : ℂ ≃ₜ ℂ := a.symm.trans (G.trans b)
  have hH (x : P.image) : H x = (f.toHomeomorph x : ℂ) := hG none x
  have hface (O) (x : closure (B.plOrbitFace vert P hvert O).val) :
      H x = (E O x : ℂ) := hG (some O) x
  have hclosed (O) : H '' closure (B.plOrbitFace vert P hvert O).val =
      closure (B.plOrbitFace vert P' hvert O).val := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hface O ⟨x, hx⟩]
      exact (E O ⟨x, hx⟩).property
    · intro hy
      refine ⟨(E O).symm ⟨y, hy⟩, ((E O).symm ⟨y, hy⟩).property, ?_⟩
      rw [hface O, (E O).apply_symm_apply]
  have himage : H '' P.image = P'.image := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hH ⟨x, hx⟩]
      exact (f.toHomeomorph ⟨x, hx⟩).property
    · intro hy
      refine ⟨f.toHomeomorph.symm ⟨y, hy⟩,
        (f.toHomeomorph.symm ⟨y, hy⟩).property, ?_⟩
      rw [hH, f.toHomeomorph.apply_symm_apply]
  refine ⟨H, hH, ?_, hclosed, ?_⟩
  · intro d
    rw [← f.arc_image d]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxi : x ∈ P.image := Or.inr ⟨d, hx⟩
      exact ⟨⟨x, hxi⟩, hx, (hH ⟨x, hxi⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hH x⟩
  · intro O
    rw [← P.closure_face_diff_image hvert, ← P'.closure_face_diff_image hvert,
      Set.image_sdiff H.injective, hclosed O, himage]

/-- Helper toward Proposition 5.16: simple whole orbit boundaries give a
plane extension preserving every labeled arc, closed face, and open face. -/
theorem exists_plane_homeomorph_of_simple_orbit_boundaries_mapping_faces
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hsimple : ∀ O : D39BallFaceCycleOrbit B,
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ x : P.image, H x = (f.toHomeomorph x : ℂ)) ∧
      (∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      ∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val := by
  apply B.exists_plane_homeomorph_mapping_closed_faces vert P P' hvert hconn f
  intro O
  by_cases hO : O = O_ext
  · subst O
    obtain ⟨q, q', hcl, hc, hq, hcl', hc', hq'⟩ := hsimple O_ext
    obtain ⟨E, hE⟩ := B.exists_outer_face_extension_of_polygonOutsideExtension
      vert P P' hvert hconn f O_ext hext q q' hcl hc hq hcl' hc' hq'
      polygonOutsideExtension_holds
    refine ⟨E, ?_⟩
    intro x hx
    exact hE x ((P.closure_face_inter_image_eq_frontier hvert _) ▸ ⟨x.property, hx⟩)
  · exact B.exists_all_bounded_plOrbitFace_homeomorphs vert P P' hvert hconn
      f O_ext hext (fun O _ => hsimple O) O hO

omit [Finite V] hconn hvert in
/-- Helper toward Proposition 5.16: an extension of the drawing map takes
each oriented dart traversal to its counterpart by a strictly increasing,
endpoint-fixing homeomorphism of the parameter interval. -/
theorem exists_arc_reparam_of_plane_extension
    (f : B.PLImageHomeomorph vert P P') (H : ℂ ≃ₜ ℂ)
    (hH : ∀ x : P.image, H x = (f.toHomeomorph x : ℂ))
    (harc : ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image)
    (d : B.D) :
    ∃ φ : unitInterval ≃ₜ unitInterval,
      φ 0 = 0 ∧ φ 1 = 1 ∧ StrictMono φ ∧
      ∀ u : unitInterval, H ((P.arc d).toPath u) = (P'.arc d).toPath (φ u) := by
  let γ : unitInterval → ℂ := fun u => H ((P.arc d).toPath u)
  let δ := (P'.arc d).toPath
  have hγc : Continuous γ := H.continuous.comp (P.arc d).toPath.continuous
  have hγi : Function.Injective γ :=
    H.injective.comp ((P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d))
  have hδi : Function.Injective δ :=
    (P'.arc d).toPath_injective (P'.arc_length d) (P'.arc_simple d)
  have hrange : Set.range γ = Set.range δ := by
    change Set.range (H ∘ (P.arc d).toPath) = Set.range (P'.arc d).toPath
    rw [Set.range_comp, Polyline.range_toPath, Polyline.range_toPath, harc d]
  let eγ : unitInterval ≃ₜ Set.range γ :=
    (hγc.isClosedEmbedding hγi).isEmbedding.toHomeomorph
  let eδ : unitInterval ≃ₜ Set.range δ :=
    (δ.continuous.isClosedEmbedding hδi).isEmbedding.toHomeomorph
  let φ : unitInterval ≃ₜ unitInterval :=
    (eγ.trans (Homeomorph.setCongr hrange)).trans eδ.symm
  have hmatch (u : unitInterval) : δ (φ u) = γ u := by
    exact congrArg Subtype.val
      (eδ.apply_symm_apply ((Homeomorph.setCongr hrange) (eγ u)))
  have hpos (v : V) : H (P.pos v) = P'.pos v :=
    (hH ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩).trans (f.vertex_image v)
  have h0 : φ 0 = 0 := by
    apply hδi
    rw [hmatch]
    change H ((P.arc d).toPath 0) = (P'.arc d).toPath 0
    rw [Path.source, Path.source, P.arc_start, P'.arc_start, hpos]
  have h1 : φ 1 = 1 := by
    apply hδi
    rw [hmatch]
    change H ((P.arc d).toPath 1) = (P'.arc d).toPath 1
    rw [Path.target, Path.target, P.arc_finish, P'.arc_finish, hpos]
  refine ⟨φ, h0, h1, ?_, fun u => (hmatch u).symm⟩
  apply φ.continuous.strictMono_of_inj_boundedOrder ?_ φ.injective
  change φ 0 ≤ φ 1
  rw [h0, h1]
  exact zero_le_one

omit [Finite V] hconn hvert in
/-- Helper toward Proposition 5.16: the logarithmic increment on an
oriented dart is unchanged by its prescribed plane extension. -/
theorem hasLiftIncrement_map_arc_iff
    (f : B.PLImageHomeomorph vert P P') (H : ℂ ≃ₜ ℂ)
    (hH : ∀ x : P.image, H x = (f.toHomeomorph x : ℂ))
    (harc : ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image)
    (d : B.D) (w v : ℂ) :
    HasLiftIncrement ((P.arc d).toPath.map H.continuous) w v ↔
      HasLiftIncrement (P'.arc d).toPath w v := by
  obtain ⟨φ, h0, h1, _, hmatch⟩ :=
    B.exists_arc_reparam_of_plane_extension vert P P' f H hH harc d
  have hi0 : φ.symm 0 = 0 := by
    apply φ.injective
    rw [φ.apply_symm_apply, h0]
  have hi1 : φ.symm 1 = 1 := by
    apply φ.injective
    rw [φ.apply_symm_apply, h1]
  constructor
  · rintro ⟨ψ, hψ, hinc⟩
    refine ⟨ψ.comp ⟨φ.symm, φ.symm.continuous⟩, ?_, ?_⟩
    · intro t
      change Complex.exp (ψ (φ.symm t)) = (P'.arc d).toPath t - w
      rw [hψ]
      change H ((P.arc d).toPath (φ.symm t)) - w = _
      rw [hmatch, φ.apply_symm_apply]
    · change ψ (φ.symm 1) - ψ (φ.symm 0) = v
      rw [hi0, hi1]
      exact hinc
  · rintro ⟨ψ, hψ, hinc⟩
    refine ⟨ψ.comp ⟨φ, φ.continuous⟩, ?_, ?_⟩
    · intro t
      change Complex.exp (ψ (φ t)) = H ((P.arc d).toPath t) - w
      rw [hψ, hmatch]
    · change ψ (φ 1) - ψ (φ 0) = v
      rw [h0, h1]
      exact hinc

omit [Finite V] hconn hvert in
/-- Helper toward Proposition 5.16: corresponding finite face walks have
the same logarithmic increment after applying the drawing's plane extension.
No simplicity or equal subdivision schedule is needed for this comparison. -/
theorem hasLiftIncrement_map_faceWalkPolyline_iff
    (f : B.PLImageHomeomorph vert P P') (H : ℂ ≃ₜ ℂ)
    (hH : ∀ x : P.image, H x = (f.toHomeomorph x : ℂ))
    (harc : ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image)
    (d : B.D) (n : ℕ) (w v : ℂ) :
    HasLiftIncrement ((faceWalkPolyline B vert P d n).toPath.map H.continuous) w v ↔
      HasLiftIncrement (faceWalkPolyline B vert P' d n).toPath w v := by
  induction n generalizing v with
  | zero => exact B.hasLiftIncrement_map_arc_iff vert P P' f H hH harc d w v
  | succ n ih =>
    let e := (B.map.faceSucc : B.D → B.D)^[n + 1] d
    have hsource := hasLiftIncrement_boundaryConcat_iff (⟨H, H.continuous⟩ : C(ℂ, ℂ))
      (faceWalkPolyline B vert P d n) (P.arc e)
      (B.faceWalkPolyline_points_length_ge_two vert P d n) (P.arc_length e)
      (finish_faceWalkPolyline_eq_next_start B vert P d n) w v
    have htarget := hasLiftIncrement_boundaryConcat_iff (ContinuousMap.id ℂ)
      (faceWalkPolyline B vert P' d n) (P'.arc e)
      (B.faceWalkPolyline_points_length_ge_two vert P' d n) (P'.arc_length e)
      (finish_faceWalkPolyline_eq_next_start B vert P' d n) w v
    refine hsource.trans (Iff.trans ?_ htarget.symm)
    apply exists_congr
    intro v₁
    apply exists_congr
    intro v₂
    exact (ih v₁).and
      ((B.hasLiftIncrement_map_arc_iff vert P P' f H hH harc e w v₂).and Iff.rfl)

omit [Finite V] hconn hvert in
/-- Helper toward Proposition 5.16: the mapped full-period loop has exactly
the winding of the target full-period loop in the same dart order. -/
theorem hasWinding_map_fullPeriod_faceWalkPolyline_iff
    (f : B.PLImageHomeomorph vert P P') (H : ℂ ≃ₜ ℂ)
    (hH : ∀ x : P.image, H x = (f.toHomeomorph x : ℂ))
    (harc : ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image)
    (d : B.D) (w : ℂ) (k : ℤ) :
    HasWinding
      (((faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).toPath.cast
          rfl (faceWalkPolyline_closed B vert P d)).map H.continuous) w k ↔
      HasWinding
        ((faceWalkPolyline B vert P' d
          (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).toPath.cast
            rfl (faceWalkPolyline_closed B vert P' d)) w k := by
  exact B.hasLiftIncrement_map_faceWalkPolyline_iff vert P P' f H hH harc d _ w
    (2 * Real.pi * Complex.I * k)

omit [Finite V] in
/-- Helper toward Proposition 5.16: a bounded target face gives winding one
for the mapped full-period walk, using the same dart order in both drawings. -/
theorem hasWinding_map_fullPeriod_faceWalkPolyline_one
    (f : B.PLImageHomeomorph vert P P') (H : ℂ ≃ₜ ℂ)
    (hH : ∀ x : P.image, H x = (f.toHomeomorph x : ℂ))
    (harc : ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image)
    (O : D39BallFaceCycleOrbit B)
    (hb' : Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val)
    (d : B.D) (hd : d ∈ O.val)
    (hc' : (faceWalkPolyline B vert P' d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple)
    (z : ℂ) (hz : H z ∈ (B.plOrbitFace vert P' hvert O).val) :
    HasWinding
      (((faceWalkPolyline B vert P d
        (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).toPath.cast
          rfl (faceWalkPolyline_closed B vert P d)).map H.continuous) (H z) 1 := by
  apply (B.hasWinding_map_fullPeriod_faceWalkPolyline_iff vert P P'
    f H hH harc d (H z) 1).mpr
  apply (B.faceWalkPolyline_fullPeriod_hasWinding_iff_angleSum_eq_one vert P' hvert
    hconn O hb' d hd (faceWalkPolyline_closed B vert P' d) hc' (H z) hz).mpr
  exact B.faceWalkPolyline_fullPeriod_angleSum_eq_one_of_isBounded vert P' hvert
    hconn O hb' d hd (faceWalkPolyline_closed B vert P' d) hc' (H z) hz

omit [Finite V] in
/-- Helper toward Proposition 5.16: the mapped bounded face walk and its
target traversal are freely homotopic in the complement of the mapped face
point. The logarithmic-increment comparison avoids subdivision assumptions. -/
theorem exists_freeHomotopy_map_fullPeriod_faceWalkPolyline
    (f : B.PLImageHomeomorph vert P P') (H : ℂ ≃ₜ ℂ)
    (hH : ∀ x : P.image, H x = (f.toHomeomorph x : ℂ))
    (harc : ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image)
    (hface : ∀ O : D39BallFaceCycleOrbit B,
      H '' (B.plOrbitFace vert P hvert O).val = (B.plOrbitFace vert P' hvert O).val)
    (O : D39BallFaceCycleOrbit B)
    (hb' : Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val)
    (d : B.D) (hd : d ∈ O.val)
    (hc' : (faceWalkPolyline B vert P' d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple)
    (z : ℂ) (hz : z ∈ (B.plOrbitFace vert P hvert O).val) :
    let L := ((faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).toPath.cast
        rfl (faceWalkPolyline_closed B vert P d)).map H.continuous
    let L' := (faceWalkPolyline B vert P' d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).toPath.cast
        rfl (faceWalkPolyline_closed B vert P' d)
    ∃ G : C(unitInterval × unitInterval, ℂ),
      (∀ s, G (0, s) = L s) ∧ (∀ s, G (1, s) = L' s) ∧
      (∀ u, G (u, 1) = G (u, 0)) ∧ (∀ u s, G (u, s) ≠ H z) := by
  have hz' : H z ∈ (B.plOrbitFace vert P' hvert O).val :=
    hface O ▸ Set.mem_image_of_mem H hz
  have hw := B.hasWinding_map_fullPeriod_faceWalkPolyline_one vert P P' hvert
    hconn f H hH harc O hb' d hd hc' z hz'
  have hw' := (B.hasWinding_map_fullPeriod_faceWalkPolyline_iff vert P P'
    f H hH harc d (H z) 1).mp hw
  exact exists_freeHomotopy_of_hasWinding hw hw'

omit [Finite V] in
/-- Helper toward Proposition 5.16: one bounded orbit with simple full-period
walks certifies that the prescribed face-preserving extension preserves
orientation. Simplicity here concerns the actual walks, not just their images. -/
theorem orientationPreserving_of_simple_fullPeriod_faceWalks
    (f : B.PLImageHomeomorph vert P P') (H : ℂ ≃ₜ ℂ)
    (hH : ∀ x : P.image, H x = (f.toHomeomorph x : ℂ))
    (harc : ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image)
    (hface : ∀ O : D39BallFaceCycleOrbit B,
      H '' (B.plOrbitFace vert P hvert O).val = (B.plOrbitFace vert P' hvert O).val)
    (O : D39BallFaceCycleOrbit B)
    (hb : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val)
    (hb' : Bornology.IsBounded (B.plOrbitFace vert P' hvert O).val)
    (d : B.D) (hd : d ∈ O.val)
    (hc : (faceWalkPolyline B vert P d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple)
    (hc' : (faceWalkPolyline B vert P' d
      (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)).IsCyclicSimple) :
    OrientationPreserving H := by
  obtain ⟨z, hzoffImage, hzface⟩ := (B.plOrbitFace vert P hvert O).property
  have hz : z ∈ (B.plOrbitFace vert P hvert O).val := by
    rw [hzface]
    exact mem_connectedComponentIn hzoffImage
  let q := faceWalkPolyline B vert P d
    (Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d - 1)
  let L := q.toPath.cast rfl (faceWalkPolyline_closed B vert P d)
  have hzoff : z ∉ Set.range L := by
    change z ∉ Set.range q.toPath
    rw [Polyline.range_toPath,
      B.faceWalkPolyline_image_eq_plOrbitBoundary vert P O d hd]
    exact fun h => P.face_subset_compl _ hz (B.plOrbitBoundary_subset_image vert P O h)
  have hw : HasWinding L z 1 := by
    apply (B.faceWalkPolyline_fullPeriod_hasWinding_iff_angleSum_eq_one vert P hvert
      hconn O hb d hd (faceWalkPolyline_closed B vert P d) hc z hz).mpr
    exact B.faceWalkPolyline_fullPeriod_angleSum_eq_one_of_isBounded vert P hvert
      hconn O hb d hd (faceWalkPolyline_closed B vert P d) hc z hz
  have hz' : H z ∈ (B.plOrbitFace vert P' hvert O).val :=
    hface O ▸ Set.mem_image_of_mem H hz
  have hwmap : HasWinding (L.map H.continuous) (H z) 1 :=
    B.hasWinding_map_fullPeriod_faceWalkPolyline_one vert P P' hvert hconn
      f H hH harc O hb' d hd hc' z hz'
  intro a M w hwM k
  exact orientationPreserving_of_hasWinding_one H L z hzoff hw hwmap M w hwM k

end D39FiniteBall
end DirectedDistances.PlanarMap










































































