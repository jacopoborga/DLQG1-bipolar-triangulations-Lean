/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso15
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation12

/-! Helper toward Proposition 5.16. Uniqueness and identification of topological -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

attribute [local instance] Classical.propDecidable

private theorem radial_inter_eq_zero {u v z : ℂ}
    (harg : Complex.arg u ≠ Complex.arg v)
    (hu : ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ z = (a : ℂ) * u)
    (hv : ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 ∧ z = (b : ℂ) * v) : z = 0 := by
  by_contra hz
  obtain ⟨a, ha, _, hza⟩ := hu
  obtain ⟨b, hb, _, hzb⟩ := hv
  have ha0 : 0 < a := by
    by_contra h
    have : a = 0 := le_antisymm (le_of_not_gt h) ha
    exact hz (by simp [this] at hza; exact hza)
  have hb0 : 0 < b := by
    by_contra h
    have : b = 0 := le_antisymm (le_of_not_gt h) hb
    exact hz (by simp [this] at hzb; exact hzb)
  have heq := congrArg Complex.arg (hza.symm.trans hzb)
  rw [Complex.arg_real_mul u ha0, Complex.arg_real_mul v hb0] at heq
  exact harg heq

private theorem centers_eq_of_two_inclusions
    (H K : ℂ ≃ₜ ℂ) (A B A' B' : Set ℂ) (u v u' v' : ℂ)
    (hA : H '' A = {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * u})
    (hB : H '' B = {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * v})
    (hA' : K '' A' = {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * u'})
    (hB' : K '' B' = {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * v'})
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (harg : Complex.arg u' ≠ Complex.arg v') : H.symm 0 = K.symm 0 := by
  have hzero (S : Set ℂ) (w : ℂ)
      (hS : H '' S = {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * w}) :
      H.symm 0 ∈ S := by
    have hz : (0 : ℂ) ∈ H '' S := by
      rw [hS]
      exact ⟨0, le_rfl, zero_le_one, by simp⟩
    obtain ⟨p, hp, hp0⟩ := hz
    have : H.symm 0 = p := by rw [← hp0, H.symm_apply_apply]
    exact this ▸ hp
  have hKA : K (H.symm 0) ∈ K '' A' :=
    ⟨H.symm 0, hAA' (hzero A u hA), rfl⟩
  have hKB : K (H.symm 0) ∈ K '' B' :=
    ⟨H.symm 0, hBB' (hzero B v hB), rfl⟩
  rw [hA'] at hKA
  rw [hB'] at hKB
  have hz := radial_inter_eq_zero harg hKA hKB
  apply K.injective
  simpa only [K.apply_symm_apply] using hz

private theorem straightener_centers_eq_of_three
    {D : Type*} {star : Set D} {arc : D → I → ℂ}
    (H K : ℂ ≃ₜ ℂ) (dir dir' : D → ℂ)
    (harg : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (harg' : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir' x) = Complex.arg (dir' y) → x = y)
    (hs : ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      H '' (arc x '' Set.Icc (0 : I) t) =
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir x})
    (hs' : ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      K '' (arc x '' Set.Icc (0 : I) t) =
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir' x})
    (a b c : D) (ha : a ∈ star) (hb : b ∈ star) (hc : c ∈ star)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : H.symm 0 = K.symm 0 := by
  obtain ⟨ta, _, _, hta⟩ := hs a ha
  obtain ⟨tb, _, _, htb⟩ := hs b hb
  obtain ⟨tc, _, _, htc⟩ := hs c hc
  obtain ⟨ta', _, _, hta'⟩ := hs' a ha
  obtain ⟨tb', _, _, htb'⟩ := hs' b hb
  obtain ⟨tc', _, _, htc'⟩ := hs' c hc
  have hsub {x : D} {s t : I} (hst : s ≤ t) :
      arc x '' Set.Icc (0 : I) s ⊆ arc x '' Set.Icc (0 : I) t :=
    Set.image_mono (Set.Icc_subset_Icc le_rfl hst)
  by_cases hta_le : ta ≤ ta'
  · by_cases htb_le : tb ≤ tb'
    · exact centers_eq_of_two_inclusions H K _ _ _ _ _ _ _ _
        hta htb hta' htb' (hsub hta_le) (hsub htb_le)
        (fun h => hab (harg' a ha b hb h))
    · by_cases htc_le : tc ≤ tc'
      · exact centers_eq_of_two_inclusions H K _ _ _ _ _ _ _ _
          hta htc hta' htc' (hsub hta_le) (hsub htc_le)
          (fun h => hac (harg' a ha c hc h))
      · exact (centers_eq_of_two_inclusions K H _ _ _ _ _ _ _ _
          htb' htc' htb htc (hsub (le_of_not_ge htb_le))
          (hsub (le_of_not_ge htc_le)) (fun h => hbc (harg b hb c hc h))).symm
  · by_cases htb_le : tb' ≤ tb
    · exact (centers_eq_of_two_inclusions K H _ _ _ _ _ _ _ _
        hta' htb' hta htb (hsub (le_of_not_ge hta_le)) (hsub htb_le)
        (fun h => hab (harg a ha b hb h))).symm
    · by_cases htc_le : tc' ≤ tc
      · exact (centers_eq_of_two_inclusions K H _ _ _ _ _ _ _ _
          hta' htc' hta htc (hsub (le_of_not_ge hta_le)) (hsub htc_le)
          (fun h => hac (harg a ha c hc h))).symm
      · exact centers_eq_of_two_inclusions H K _ _ _ _ _ _ _ _
          htb htc htb' htc' (hsub (le_of_not_ge htb_le))
          (hsub (le_of_not_ge htc_le)) (fun h => hbc (harg' b hb c hc h))

private theorem radial_image_of_subset (K : ℂ ≃ₜ ℂ) (u v : ℂ)
    (hK0 : K 0 = 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hsub : K '' {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * u} ⊆
      {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * v}) :
    ∃ r : ℝ, 0 < r ∧
      K '' {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * u} =
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ r ∧ z = (s : ℂ) * v} := by
  let f : I → ℂ := fun t => K ((t : ℂ) * u)
  have him : f '' Set.Icc (0 : I) 1 =
      K '' {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * u} := by
    ext z
    constructor
    · rintro ⟨t, _, rfl⟩
      exact ⟨(t : ℂ) * u, ⟨t, t.property.1, t.property.2, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨s, hs0, hs1, rfl⟩, rfl⟩
      exact ⟨⟨s, hs0, hs1⟩, ⟨hs0, hs1⟩, rfl⟩
  obtain ⟨r, hr, heq⟩ := d39_continuous_radial_prefix_is_initial_segment f v
    (by dsimp [f]; fun_prop) hv (by simp [f, hK0])
    (fun t ht => hsub (by rw [← him]; exact ⟨t, ht, rfl⟩)) (by
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      intro h
      have : K u = K 0 := by simpa [f, hK0] using h
      exact hu (K.injective this))
  exact ⟨r, hr, him ▸ heq⟩

private theorem matched_radial_segments_of_same_arcs
    {D : Type*} {star : Set D} {arc : D → I → ℂ}
    (H K : ℂ ≃ₜ ℂ) (dir dir' : D → ℂ)
    (hcenter : H.symm 0 = K.symm 0)
    (hdir : ∀ x ∈ star, dir x ≠ 0 ∧ dir' x ≠ 0)
    (hs : ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      H '' (arc x '' Set.Icc (0 : I) t) =
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir x})
    (hs' : ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      K '' (arc x '' Set.Icc (0 : I) t) =
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir' x}) :
    ∀ x ∈ star, ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      (H.symm.trans K) ''
        {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * dir x} =
        {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * dir' x} := by
  intro x hx
  obtain ⟨t, _, _, ht⟩ := hs x hx
  obtain ⟨t', _, _, ht'⟩ := hs' x hx
  have hmap (F G : ℂ ≃ₜ ℂ) (A : Set ℂ) :
      (F.symm.trans G) '' (F '' A) = G '' A := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨F a, ⟨a, ha, rfl⟩, by simp⟩
  rcases le_total t t' with hle | hle
  · have hsub : (H.symm.trans K) ''
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir x} ⊆
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir' x} := by
      rw [← ht, hmap, ← ht']
      exact Set.image_mono (Set.image_mono (Set.Icc_subset_Icc le_rfl hle))
    obtain ⟨s, hs0, heq⟩ := radial_image_of_subset (H.symm.trans K)
      (dir x) (dir' x) (by change K (H.symm 0) = 0; rw [hcenter]; simp)
      (hdir x hx).1 (hdir x hx).2 hsub
    exact ⟨1, s, zero_lt_one, hs0, heq⟩
  · have hsub : (K.symm.trans H) ''
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir' x} ⊆
        {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir x} := by
      rw [← ht', hmap, ← ht]
      exact Set.image_mono (Set.image_mono (Set.Icc_subset_Icc le_rfl hle))
    obtain ⟨r, hr0, heq⟩ := radial_image_of_subset (K.symm.trans H)
      (dir' x) (dir x) (by change H (K.symm 0) = 0; rw [← hcenter]; simp)
      (hdir x hx).2 (hdir x hx).1 hsub
    refine ⟨r, 1, hr0, zero_lt_one, ?_⟩
    rw [← heq]
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa using hw
    · intro hz
      refine ⟨(K.symm.trans H) z, ⟨z, hz, rfl⟩, ?_⟩
      simp

/-- Helper toward Proposition 5.16. For fixed arcs and a fixed star, the
topological counterclockwise successor is unique. For three distinct darts,
nested prefixes force the two straightening centers to agree; stars with at
most two darts are handled directly by the successor alternatives. -/
theorem d39TopologicalCcwSuccessor_unique
    {D : Type*} {star : Set D} {arc : D → I → ℂ} {d e f : D}
    (he : D39TopologicalCcwSuccessor star arc d e)
    (hf : D39TopologicalCcwSuccessor star arc d f) : e = f := by
  classical
  rcases he with ⟨H, hH, dir, hdir, harg, hsucc, hs⟩
  rcases hf with ⟨K, hK, dir', hdir', harg', hsucc', hs'⟩
  have hsuccData := hsucc
  have hsuccData' := hsucc'
  obtain ⟨_, hd, heStar, heCase⟩ := hsuccData
  obtain ⟨_, _, hfStar, hfCase⟩ := hsuccData'
  rcases heCase with ⟨hed, hsingle⟩ | ⟨hed, _⟩
  · have hfd : f = d := by simpa only [hsingle, Set.mem_singleton_iff] using hfStar
    exact hed.trans hfd.symm
  rcases hfCase with ⟨hfd, hsingle⟩ | ⟨hfd, _⟩
  · have hed' : e = d := by simpa only [hsingle, Set.mem_singleton_iff] using heStar
    exact hed'.trans hfd.symm
  by_contra hef
  have hcenter := straightener_centers_eq_of_three H K dir dir' harg harg'
    hs hs' d e f hd heStar hfStar (Ne.symm hed) (Ne.symm hfd) hef
  have hsegments := matched_radial_segments_of_same_arcs H K dir dir'
    hcenter (fun x hx => ⟨hdir x hx, hdir' x hx⟩) hs hs'
  have hK0 : (H.symm.trans K) 0 = 0 := by
    change K (H.symm 0) = 0
    rw [hcenter, K.apply_symm_apply]
  exact hef (d39_CcwSuccessor_eq_of_radial_segment_transport (H.symm.trans K)
    (OrientationPreserving.trans (OrientationPreserving.symm hH) hK) hK0
    (fun x hx => ⟨hdir x hx, hdir' x hx⟩) harg harg' hsegments hsucc hsucc')

/-- Helper toward Proposition 5.16. Changing arc values outside the star
does not change its topological successor witnesses. -/
theorem d39TopologicalCcwSuccessor_congr_arc
    {D : Type*} {star : Set D} {arc arc' : D → I → ℂ} {d e : D}
    (harc : ∀ q ∈ star, arc q = arc' q)
    (h : D39TopologicalCcwSuccessor star arc d e) :
    D39TopologicalCcwSuccessor star arc' d e := by
  rcases h with ⟨H, hH, dir, hdir, harg, hsucc, hs⟩
  refine ⟨H, hH, dir, hdir, harg, hsucc, ?_⟩
  intro q hq
  rw [← harc q hq]
  exact hs q hq

/-- Helper toward Proposition 5.16. Restricting the ambient carrier to a
set containing the successor darts preserves the topological successor. -/
theorem d39TopologicalCcwSuccessor_subtype
    {D : Type*} {star S : Set D} {arc : D → I → ℂ}
    (d e : S)
    (h : D39TopologicalCcwSuccessor star arc d.1 e.1) :
    D39TopologicalCcwSuccessor {q : S | q.1 ∈ star}
      (fun q => arc q.1) d e := by
  rcases h with ⟨H, hH, dir, hdir, harg, hsucc, hs⟩
  rcases hsucc with ⟨hfinite, hd, he, hcase⟩
  refine ⟨H, hH, (fun q => dir q.1), (fun q hq => hdir q.1 hq), ?_,
    ?_, ?_⟩
  · intro q hq p hp heq
    exact Subtype.ext (harg q.1 hq p.1 hp heq)
  · refine ⟨hfinite.preimage Subtype.val_injective.injOn, hd, he, ?_⟩
    rcases hcase with ⟨hed, hsingle⟩ | ⟨hed, hmin⟩
    · refine Or.inl ⟨Subtype.ext hed, ?_⟩
      ext q
      simp only [Set.mem_ofPred_eq, hsingle, Set.mem_singleton_iff]
      exact Subtype.val_injective.eq_iff
    · refine Or.inr ⟨fun h => hed (congrArg Subtype.val h), ?_⟩
      intro q hq hqd
      exact hmin q.1 hq (fun h => hqd (Subtype.ext h))
  · intro q hq
    exact hs q.1 hq

/-- Helper toward Proposition 5.16. The represented target dart of the
ball equivalence has exactly the mapped edge identity and endpoint-order bit. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_dart_map
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (q : {q : M.core.D // q ∈ d39BallDarts M r}) :
    let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
      ⟨(x.dartEquiv q.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x r q.1).mp q.2⟩
    y.dartEquiv
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e q).1 =
      ((e.edgeEquiv a).1, Bool.xor (x.dartEquiv q.1).2 (e.edgeFlip a)) := by
  dsimp only
  change y.dartEquiv (y.dartEquiv.symm _) = _
  exact y.dartEquiv.apply_symm_apply _

/-- Helper toward Proposition 5.16. The geometric ball homeomorphism maps
each represented dart arc to the represented image dart arc with its actual
increasing interval reparameterization. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_arc_map
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (q : {q : M.core.D // q ∈ d39BallDarts M r}) (t : I) :
    let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
      ⟨(x.dartEquiv q.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x r q.1).mp q.2⟩
    e.h (d39DrawingDartArc B x.toD39DrawingRepresentationData q.1 t) =
      d39DrawingDartArc C y.toD39DrawingRepresentationData
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e q).1
        (d39GeomBallIsoV2DartParam e a (x.dartEquiv q.1).2 t) := by
  dsimp only
  have hpair := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_dart_map
    x y e q
  have hm := d39GeomBallIsoV2_arc_map_dart e
    ⟨(x.dartEquiv q.1).1,
      (d39DrawingRepresentationData3_ballDarts_iff x r q.1).mp q.2⟩
    (x.dartEquiv q.1).2 t
  unfold d39DrawingDartArc
  rw [hpair]
  simpa only [ite_apply] using hm

/-- Helper toward Proposition 5.16. The ball-dart equivalence preserves and
reflects equality of the original ambient vertex classes. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_iff
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (q d : {q : M.core.D // q ∈ d39BallDarts M r}) :
    rootedLocallyFiniteVertexClass N.core.rot
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e q).1 =
      rootedLocallyFiniteVertexClass N.core.rot
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 ↔
    rootedLocallyFiniteVertexClass M.core.rot q.1 =
      rootedLocallyFiniteVertexClass M.core.rot d.1 := by
  have hq := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_map
    x y e q
  have hd := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_map
    x y e d
  constructor
  · intro h
    have hy := congrArg y.vertexEquiv h
    rw [hq, hd] at hy
    have hv := e.vertexEquiv.injective (Subtype.ext hy)
    exact x.vertexEquiv.injective (congrArg Subtype.val hv)
  · intro h
    apply y.vertexEquiv.injective
    rw [hq, hd]
    apply congrArg (fun v => (e.vertexEquiv v).1)
    exact Subtype.ext (congrArg x.vertexEquiv h)

/-- Helper toward Proposition 5.16. If the source star is retained, its
ball rotation is a topological successor for the actual target arcs on the
retained target star, indexed by target ball darts. -/
theorem d39DrawingRepresentationData3_geomBallIso_topological_successor_on_ball
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hball : ∀ q : M.core.D,
      rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d.1 →
      (x.dartEquiv q).1 ∈ d39GeomBallEdges B.map B.root r) :
    let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
    D39TopologicalCcwSuccessor
      {q : {q : N.core.D // q ∈ d39BallDarts N r} |
        rootedLocallyFiniteVertexClass N.core.rot q.1 =
          rootedLocallyFiniteVertexClass N.core.rot (E d).1}
      (fun q => d39DrawingDartArc C y.toD39DrawingRepresentationData q.1)
      (E d) (E ((d39BallMap M r).rot d)) := by
  classical
  dsimp only
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  let star : Set M.core.D := {q | rootedLocallyFiniteVertexClass M.core.rot q =
    rootedLocallyFiniteVertexClass M.core.rot d.1}
  have hsub : star ⊆ d39BallDarts M r :=
    (d39DrawingRepresentationData3_star_subset_ballDarts_iff_geomBall x d.1).mpr hball
  have hrot : M.core.rot d.1 ∈ star :=
    Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left
  have hnext : ((d39BallMap M r).rot d).1 = M.core.rot d.1 :=
    DirectedDistances.PaperProofs.Section3.d39BallMap_rot_of_mem M r d.2 (hsub hrot)
  have hsource : D39TopologicalCcwSuccessor
      {q : {q : M.core.D // q ∈ d39BallDarts M r} | q.1 ∈ star}
      (fun q => d39DrawingDartArc B x.toD39DrawingRepresentationData q.1)
      d ((d39BallMap M r).rot d) := by
    apply d39TopologicalCcwSuccessor_subtype
    rw [hnext]
    exact x.rotation_topological_successor d.1
  let param (q : {q : M.core.D // q ∈ d39BallDarts M r}) : I ≃ₜ I :=
    d39GeomBallIsoV2DartParam e
      ⟨(x.dartEquiv q.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x r q.1).mp q.2⟩
      (x.dartEquiv q.1).2
  have htransport := d39TopologicalCcwSuccessor_map_orientedHomeomorph
    {q : {q : M.core.D // q ∈ d39BallDarts M r} | q.1 ∈ star}
    (fun q => d39DrawingDartArc B x.toD39DrawingRepresentationData q.1)
    (fun q => d39DrawingDartArc C y.toD39DrawingRepresentationData (E q).1)
    param d ((d39BallMap M r).rot d) e.h e.orientationPreserving
    (fun q _ => d39GeomBallIsoV2DartParam_strictMono e _ _)
    (fun q _ t => d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_arc_map
      x y e q t) hsource
  have hindexed := (d39TopologicalCcwSuccessor_map_equiv_iff E _ _ _ _).mpr htransport
  have himage : E '' {q : {q : M.core.D // q ∈ d39BallDarts M r} | q.1 ∈ star} =
      {q : {q : N.core.D // q ∈ d39BallDarts N r} |
        rootedLocallyFiniteVertexClass N.core.rot q.1 =
          rootedLocallyFiniteVertexClass N.core.rot (E d).1} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_iff
        x y e p d).mpr hp
    · intro hq
      refine ⟨E.symm q, ?_, E.apply_symm_apply q⟩
      apply (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_iff
        x y e (E.symm q) d).mp
      change rootedLocallyFiniteVertexClass N.core.rot (E (E.symm q)).1 = _
      rw [E.apply_symm_apply]
      exact hq
  rw [himage] at hindexed
  simpa only [E.apply_symm_apply] using hindexed

private theorem exists_ccw_successor {D : Type*} (star : Set D)
    (dir : D → ℂ) (hfin : star.Finite) {d : D} (hd : d ∈ star) :
    ∃ e, CcwSuccessor star dir d e := by
  classical
  by_cases h : ∃ e ∈ star, e ≠ d
  · obtain ⟨e, he, hmin⟩ := Set.exists_min_image {e ∈ star | e ≠ d}
      (fun e => ccwTurn (dir d) (dir e))
      (hfin.subset (fun _ hx => hx.1)) (by simpa only [Set.nonempty_def,
        Set.mem_ofPred_eq] using h)
    exact ⟨e, hfin, hd, he.1, Or.inr ⟨he.2, fun f hf hfd => hmin f ⟨hf, hfd⟩⟩⟩
  · refine ⟨d, hfin, hd, hd, Or.inl ⟨rfl, ?_⟩⟩
    ext e
    constructor
    · intro he
      exact Set.mem_singleton_iff.mpr (by by_contra hne; exact h ⟨e, he, hne⟩)
    · intro he
      exact (Set.mem_singleton_iff.mp he) ▸ hd

private theorem angle_cut_iterate {D : Type*} (rot : Equiv.Perm D)
    (star : Set D) (dir : D → ℂ) (d f : D)
    (hpow : ∀ n : ℕ, (rot ^ n) d ∈ star)
    (harg : ∀ x ∈ star, ∀ y ∈ star, (dir x).arg = (dir y).arg → x = y)
    (hsucc : ∀ x ∈ star, CcwSuccessor star dir x (rot x))
    (hperiod : ∃ k : ℕ, 0 < k ∧ (rot ^ k) d = d)
    (hf : f ∈ star) (hfd : f ≠ d) :
    ∃ n : ℕ, 0 < n ∧ (rot ^ n) d = f ∧
      ∀ j : ℕ, 0 < j → j < n →
        ccwTurn (dir d) (dir ((rot ^ j) d)) < ccwTurn (dir d) (dir f) := by
  classical
  let turn := ccwTurn (dir d) (dir f)
  let q : ℕ → Prop := fun n => 0 < n ∧ turn ≤ ccwTurn (dir d) (dir ((rot ^ n) d))
  have hd : d ∈ star := by simpa using hpow 0
  have hturnlt : turn < 2 * Real.pi := by
    apply lt_of_le_of_ne (ccwTurn_le_two_pi _ _)
    intro h
    exact hfd (harg f hf d hd ((ccwTurn_eq_two_pi_iff _ _).mp h).symm)
  have hex : ∃ n, q n := by
    obtain ⟨k, hk, hkd⟩ := hperiod
    refine ⟨k, hk, ?_⟩
    rw [hkd, (ccwTurn_eq_two_pi_iff _ _).mpr rfl]
    exact hturnlt.le
  let n := Nat.find hex
  have hn : 0 < n ∧ turn ≤ ccwTurn (dir d) (dir ((rot ^ n) d)) := Nat.find_spec hex
  have hbelow : ∀ j : ℕ, 0 < j → j < n →
      ccwTurn (dir d) (dir ((rot ^ j) d)) < turn := by
    intro j hj hjn
    exact lt_of_not_ge (fun h => Nat.find_min hex hjn ⟨hj, h⟩)
  refine ⟨n, hn.1, ?_, hbelow⟩
  by_cases hn1 : n = 1
  · have hrot := hsucc d hd
    rcases hrot with ⟨_, _, _, hcase⟩
    rcases hcase with ⟨_, hsingle⟩ | ⟨_, hmin⟩
    · exact (hfd (by simpa only [hsingle, Set.mem_singleton_iff] using hf)).elim
    · have hle := hmin f hf hfd
      have hn' : turn ≤ ccwTurn (dir d) (dir (rot d)) := by
        simpa only [hn1, pow_one] using hn.2
      have heq := ccwTurn_left_injective (le_antisymm hle hn')
      have hval : rot d = f := harg _ (hpow 1) f hf heq
      simpa only [hn1, pow_one] using hval
  · have hnlarge : 1 < n := by have := hn.1; omega
    let j := n - 1
    have hj : 0 < j := by dsimp [j]; omega
    have hjn : j < n := by dsimp [j]; omega
    have hb := hbelow j hj hjn
    have hnext : (rot ^ n) d = rot ((rot ^ j) d) := by
      have hn' : n = j + 1 := by dsimp [j]; omega
      rw [hn', pow_succ', Equiv.Perm.mul_apply]
    by_cases heq : turn = ccwTurn (dir d) (dir ((rot ^ n) d))
    · exact harg _ (hpow n) f hf (ccwTurn_left_injective heq.symm)
    · have habove : turn < ccwTurn (dir d) (dir ((rot ^ n) d)) :=
        lt_of_le_of_ne hn.2 heq
      have hbetween : ccwTurn (dir ((rot ^ j) d)) (dir f) <
          ccwTurn (dir ((rot ^ j) d)) (dir ((rot ^ n) d)) := by
        have hcompf := ccwTurn_comp_add hb
        have hcompn := ccwTurn_comp_add (lt_trans hb habove)
        linarith
      have hneq : f ≠ (rot ^ j) d := by
        intro h
        dsimp only [turn] at hb
        rw [h] at hb
        exact (lt_irrefl _) hb
      have hrot := hsucc ((rot ^ j) d) (hpow j)
      rcases hrot with ⟨_, _, _, hcase⟩
      rcases hcase with ⟨heqd, hsingle⟩ | ⟨_, hmin⟩
      · exact (hneq (by simpa only [hsingle, Set.mem_singleton_iff] using hf)).elim
      · have hle := hmin f hf hneq
        rw [hnext] at hbetween
        exact ((not_lt_of_ge hle) hbetween).elim

private theorem ccw_successor_of_first_return {D : Type*}
    (rot : Equiv.Perm D) (star S : Set D) (dir : D → ℂ) (d r : D)
    (hpow : ∀ n : ℕ, (rot ^ n) d ∈ star)
    (harg : ∀ x ∈ star, ∀ y ∈ star, (dir x).arg = (dir y).arg → x = y)
    (hsucc : ∀ x ∈ star, CcwSuccessor star dir x (rot x))
    (hperiod : ∃ k : ℕ, 0 < k ∧ (rot ^ k) d = d)
    (hdS : d ∈ S) (k : ℕ) (hk : 0 < k) (hret : (rot ^ k) d = r)
    (hrS : r ∈ S)
    (hmin : ∀ j : ℕ, 0 < j → j < k → (rot ^ j) d ∉ S) :
    CcwSuccessor {x | x ∈ S ∧ x ∈ star} dir d r := by
  classical
  have hd : d ∈ star := by simpa using hpow 0
  have hr : r ∈ star := hret ▸ hpow k
  have hfin : {x | x ∈ S ∧ x ∈ star}.Finite :=
    (hsucc d hd).1.subset (fun _ hx => hx.2)
  have hcut := angle_cut_iterate rot star dir d
  by_cases hrd : r = d
  · refine ⟨hfin, ⟨hdS, hd⟩, ⟨hrS, hr⟩, Or.inl ⟨hrd, ?_⟩⟩
    ext f
    constructor
    · rintro ⟨hfS, hf⟩
      apply Set.mem_singleton_iff.mpr
      by_contra hfd
      obtain ⟨n, hn, hnf, hbefore⟩ := hcut f hpow harg hsucc hperiod hf hfd
      have hnk : n < k := by
        by_contra h
        rcases eq_or_lt_of_le (le_of_not_gt h) with heq | hlt
        · exact hfd (hnf.symm.trans (heq ▸ hret.trans hrd))
        · have hb := hbefore k hk hlt
          rw [hret, hrd, (ccwTurn_eq_two_pi_iff _ _).mpr rfl] at hb
          exact (not_lt_of_ge (ccwTurn_le_two_pi _ _)) hb
      exact hmin n hn hnk (hnf ▸ hfS)
    · intro hf
      exact (Set.mem_singleton_iff.mp hf) ▸ ⟨hdS, hd⟩
  · obtain ⟨n, hn, hnr, hbefore⟩ := hcut r hpow harg hsucc hperiod hr hrd
    have hnk : n = k := by
      apply le_antisymm
      · by_contra h
        have hb := hbefore k hk (lt_of_not_ge h)
        rw [hret] at hb
        exact (lt_irrefl _) hb
      · by_contra h
        exact hmin n hn (lt_of_not_ge h) (hnr ▸ hrS)
    refine ⟨hfin, ⟨hdS, hd⟩, ⟨hrS, hr⟩, Or.inr ⟨hrd, ?_⟩⟩
    intro f hf hfd
    by_contra hle
    have hbetween : ccwTurn (dir d) (dir f) < ccwTurn (dir d) (dir r) :=
      lt_of_not_ge hle
    obtain ⟨m, hm, hmf, hmBefore⟩ := hcut f hpow harg hsucc hperiod hf.2 hfd
    have hmn : m < n := by
      by_contra h
      rcases eq_or_lt_of_le (le_of_not_gt h) with heq | hlt
      · have hfr : f = r := hmf.symm.trans (heq ▸ hnr)
        rw [hfr] at hbetween
        exact (lt_irrefl _) hbetween
      · have hb := hmBefore n hn hlt
        rw [hnr] at hb
        exact (not_lt_of_ge hb.le) hbetween
    exact hmin m hm (by omega) (hmf ▸ hf.1)

/-- Helper toward Proposition 5.16. A represented ball rotation is the
topological successor on the retained part of its ambient vertex star. The
least-positive-return definition keeps darts omitted from the ball out of
the resulting successor comparison. -/
theorem d39DrawingRepresentationData3_ball_rotation_topological_successor
    {N : D39RootedMap} {C : D39DomainRootedMapV2} (r : ℕ)
    (y : D39DrawingRepresentationData3 N C)
    (d : {d : N.core.D // d ∈ d39BallDarts N r}) :
    D39TopologicalCcwSuccessor
      {q : {q : N.core.D // q ∈ d39BallDarts N r} |
        rootedLocallyFiniteVertexClass N.core.rot q.1 =
          rootedLocallyFiniteVertexClass N.core.rot d.1}
      (fun q => d39DrawingDartArc C y.toD39DrawingRepresentationData q.1)
      d ((d39BallMap N r).rot d) := by
  classical
  let star : Set N.core.D := {q | rootedLocallyFiniteVertexClass N.core.rot q =
    rootedLocallyFiniteVertexClass N.core.rot d.1}
  obtain ⟨H, hH, dir, hdir, harg, hsuccD, hs⟩ :=
    y.rotation_topological_successor d.1
  have hsucc : ∀ q ∈ star, CcwSuccessor star dir q (N.core.rot q) := by
    intro q hq
    obtain ⟨f, hf⟩ := exists_ccw_successor star dir hsuccD.1 hq
    have hfTopo : D39TopologicalCcwSuccessor star
        (d39DrawingDartArc C y.toD39DrawingRepresentationData) q f :=
      ⟨H, hH, dir, hdir, harg, hf, hs⟩
    have hy := y.rotation_topological_successor q
    have hstar : {p | rootedLocallyFiniteVertexClass N.core.rot p =
        rootedLocallyFiniteVertexClass N.core.rot q} = star := by
      ext p
      change _ = rootedLocallyFiniteVertexClass N.core.rot q ↔
        _ = rootedLocallyFiniteVertexClass N.core.rot d.1
      rw [show rootedLocallyFiniteVertexClass N.core.rot q =
        rootedLocallyFiniteVertexClass N.core.rot d.1 from hq]
    rw [hstar] at hy
    have heq := d39TopologicalCcwSuccessor_unique hfTopo hy
    exact heq ▸ hf
  have hpow : ∀ n : ℕ, (N.core.rot ^ n) d.1 ∈ star := by
    intro n
    exact Quotient.sound (Equiv.Perm.sameCycle_pow_left.mpr Equiv.Perm.SameCycle.rfl)
  let S := d39BallDarts N r
  let hreturn : ∀ q : S, ∃ k : ℕ, 0 < k ∧ (N.core.rot ^ k) q.1 ∈ S := by
    intro q
    obtain ⟨k, hk, hkd⟩ := d39RotationReturn N q.1
    exact ⟨k, hk, by rw [hkd]; exact q.2⟩
  let k := cyclicFirstReturnTime N.core.rot S hreturn d
  have hk := cyclicFirstReturnTime_spec N.core.rot S hreturn d
  have hret : (N.core.rot ^ k) d.1 = ((d39BallMap N r).rot d).1 :=
    (firstReturn_spec N.core.rot S hreturn d).1.symm
  have hccw := ccw_successor_of_first_return N.core.rot star (S : Set N.core.D)
    dir d.1 ((d39BallMap N r).rot d).1 hpow harg hsucc (d39RotationReturn N d.1)
    d.2 k hk.1 hret ((d39BallMap N r).rot d).2 hk.2.2
  have htopo : D39TopologicalCcwSuccessor {q | q ∈ S ∧ q ∈ star}
      (d39DrawingDartArc C y.toD39DrawingRepresentationData)
      d.1 ((d39BallMap N r).rot d).1 :=
    ⟨H, hH, dir, (fun q hq => hdir q hq.2),
      (fun q hq p hp h => harg q hq.2 p hp.2 h), hccw,
      (fun q hq => hs q hq.2)⟩
  have hsub := d39TopologicalCcwSuccessor_subtype d ((d39BallMap N r).rot d) htopo
  have hstar : {q : {q : N.core.D // q ∈ d39BallDarts N r} |
      q.1 ∈ S ∧ q.1 ∈ star} = {q | q.1 ∈ star} := by
    ext q
    exact and_iff_right q.2
  change D39TopologicalCcwSuccessor
    {q : {q : N.core.D // q ∈ d39BallDarts N r} | q.1 ∈ S ∧ q.1 ∈ star}
    (fun q => d39DrawingDartArc C y.toD39DrawingRepresentationData q.1)
    d ((d39BallMap N r).rot d) at hsub
  rw [hstar] at hsub
  exact hsub

/-- Helper toward Proposition 5.16. If the full source star is retained,
the geometric ball dart equivalence commutes with the induced ball rotations. -/
theorem d39DrawingRepresentationData3_geomBallIso_rotation_comm_when_star_in_ball
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (hr : 0 < r) (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hball : ∀ q : M.core.D,
      rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d.1 →
      (x.dartEquiv q).1 ∈ d39GeomBallEdges B.map B.root r) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
        ((d39BallMap M r).rot d) =
      (d39BallMap N r).rot
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d) := by
  exact d39TopologicalCcwSuccessor_unique
    (d39DrawingRepresentationData3_geomBallIso_topological_successor_on_ball
      x y e d hball)
    (d39DrawingRepresentationData3_ball_rotation_topological_successor r y _)

end DirectedDistances.PaperProofs.Section5

end
