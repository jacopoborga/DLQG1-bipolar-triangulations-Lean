module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.KMSW.KMSWLeftZeroStep

import Mathlib.Analysis.Convex.PathConnected

/-! # The initial KMSW plane drawing -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
abbrev KMSWStage0Vertex (w : ℕ → Fin 3) := Fin (kmswStage w 0).nextVertex

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
@[expose] def kmswStage0Vertex (w : ℕ → Fin 3)
    (d : StageDart (kmswStage w 0).nextEdge) : KMSWStage0Vertex w :=
  ⟨stageEndpoint (kmswStage w 0) d, by
    cases hb : d.2 <;> simp [stageEndpoint, kmswStage, kmswInit, hb]⟩

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
@[expose] def kmswStage0Arc (b : Bool) : Polyline :=
  ⟨if b then [1, 0] else [0, 1], by cases b <;> simp⟩

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
theorem kmswStage0Arc_simple (b : Bool) : (kmswStage0Arc b).IsSimple := by
  cases b <;> refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by simp [kmswStage0Arc] at hi; omega
    subst i
    norm_num [kmswStage0Arc, Polyline.point, Polyline.start]
  · intro i hi
    simp [kmswStage0Arc] at hi
  · intro i j hi hj hij
    simp [kmswStage0Arc] at hi hj
    omega
  · intro i hi
    have hi0 : i = 0 := by simp [kmswStage0Arc] at hi; omega
    subst i
    norm_num [kmswStage0Arc, Polyline.point, Polyline.start]
  · intro i hi
    simp [kmswStage0Arc] at hi
  · intro i j hi hj hij
    simp [kmswStage0Arc] at hi hj
    omega

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
theorem kmswStage0Vertex_injective (w : ℕ → Fin 3) :
    Function.Injective (kmswStage0Vertex w) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hij : i = j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    simp [kmswStage, kmswInit] at hi hj
    omega
  have hb : b = c := by
    have hv := congrArg Fin.val h
    change (if b then 1 else 0 : ℕ) = (if c then 1 else 0) at hv
    cases b <;> cases c <;> simp_all
  exact Prod.ext hij hb

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
@[expose] noncomputable def kmswStage0Drawing (w : ℕ → Fin 3) :
    PLDrawing (StageDart (kmswStage w 0).nextEdge) (KMSWStage0Vertex w)
      (edgeFlip _) (stageRot w 0) (kmswStage0Vertex w) where
  flip_involutive := by rintro ⟨i, b⟩; cases b <;> rfl
  flip_ne := by
    rintro ⟨i, b⟩ h
    have hb := congrArg Prod.snd h
    cases b <;> cases hb
  vert_rotation := by intro d; rfl
  pos := fun v => (v.val : ℂ)
  pos_injective := by
    intro v u h
    apply Fin.ext
    change (v.val : ℂ) = (u.val : ℂ) at h
    exact_mod_cast h
  arc := fun d => kmswStage0Arc d.2
  arc_simple := fun d => kmswStage0Arc_simple d.2
  arc_length := by rintro ⟨i, b⟩; cases b <;> simp [kmswStage0Arc]
  arc_start := by
    rintro ⟨i, b⟩
    cases b <;> simp [kmswStage0Arc, Polyline.start, kmswStage0Vertex,
      stageEndpoint, kmswStage, kmswInit]
  arc_finish := by
    rintro ⟨i, b⟩
    change (kmswStage0Arc b).finish = ((kmswStage0Vertex w (i, !b)).val : ℂ)
    cases b <;> simp [kmswStage0Arc, Polyline.finish, kmswStage0Vertex,
      stageEndpoint, kmswStage, kmswInit]
  arc_flip := by rintro ⟨i, b⟩; cases b <;> rfl
  interior_disjoint := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hne hflip
    have hij : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      simp [kmswStage, kmswInit] at hi hj
      omega
    subst j
    cases b <;> cases c <;> simp_all [edgeFlip]
  interior_avoids_vertices := by
    rintro ⟨i, b⟩ v
    change Fin 2 at v
    fin_cases v <;> cases b <;>
      simp [kmswStage0Arc, Polyline.interior, Polyline.start, Polyline.finish]
  locally_finite := by intro K _; exact Set.toFinite _
  initial_nonzero := by
    rintro ⟨i, b⟩
    cases b <;> norm_num [kmswStage0Arc, Polyline.initialDirection, Polyline.point, Polyline.start]
  initial_arg_injective := by
    intro d e h _
    exact kmswStage0Vertex_injective w h
  rotation_agreement := by
    intro d
    have hs : {e | kmswStage0Vertex w e = kmswStage0Vertex w d} = {d} := by
      ext e
      exact ⟨fun h => kmswStage0Vertex_injective w h, fun h => h ▸ rfl⟩
    change CcwSuccessor _ _ d d
    rw [hs]
    exact ⟨Set.finite_singleton d, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

private theorem twoPoint_image (a b : ℂ) :
    (⟨[a, b], by simp⟩ : Polyline).image = segment ℝ a b := by
  ext z
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · have hza : z = a := hz
      subst z
      exact left_mem_segment ℝ a b
    · have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
      subst i
      exact hz
  · intro hz
    exact Or.inr ⟨0, by change 1 < 2; omega, hz⟩

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
theorem kmswStage0Drawing_image (w : ℕ → Fin 3) :
    (kmswStage0Drawing w).image = segment ℝ (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨⟨e, b⟩, hz⟩)
    · change Fin 2 at v
      fin_cases v
      · simpa only [kmswStage0Drawing, Nat.cast_zero] using
          left_mem_segment ℝ (0 : ℂ) 1
      · simpa only [kmswStage0Drawing, Nat.cast_one] using
          right_mem_segment ℝ (0 : ℂ) 1
    · change z ∈ (kmswStage0Arc b).image at hz
      cases b
      · exact (Set.ext_iff.mp (twoPoint_image 0 1) z).mp hz
      · have hz' : z ∈ segment ℝ (1 : ℂ) 0 :=
          (Set.ext_iff.mp (twoPoint_image 1 0) z).mp hz
        rwa [segment_symm] at hz'
  · intro hz
    refine Or.inr ⟨(⟨0, by simp [kmswStage, kmswInit]⟩, false), ?_⟩
    exact (Set.ext_iff.mp (twoPoint_image 0 1) z).mpr hz

private theorem segment_location {z : ℂ} (hz : z ∈ segment ℝ (0 : ℂ) 1) :
    z.im = 0 ∧ 0 ≤ z.re := by
  rcases hz with ⟨a, b, _ha, hb, _hab, rfl⟩
  simpa using hb

private def exteriorRegion : Set ℂ :=
  ({z | 0 < z.im} ∪ {z | z.re < 0}) ∪ {z | z.im < 0}

private theorem exteriorRegion_pathConnected : IsPathConnected exteriorRegion := by
  have hu : IsPathConnected {z : ℂ | 0 < z.im} :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm).isPathConnected
      ⟨Complex.I, by norm_num⟩
  have hl : IsPathConnected {z : ℂ | z.re < 0} :=
    ((convex_Iio (0 : ℝ)).linear_preimage Complex.reLm).isPathConnected
      ⟨-1, by norm_num⟩
  have hd : IsPathConnected {z : ℂ | z.im < 0} :=
    ((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm).isPathConnected
      ⟨-Complex.I, by norm_num⟩
  have hul : IsPathConnected ({z : ℂ | 0 < z.im} ∪ {z | z.re < 0}) :=
    hu.union hl ⟨-1 + Complex.I, by norm_num, by norm_num⟩
  exact hul.union hd ⟨-1 - Complex.I, Or.inr (by norm_num), by norm_num⟩

private theorem exteriorRegion_avoids (w : ℕ → Fin 3) :
    exteriorRegion ⊆ (kmswStage0Drawing w).imageᶜ := by
  intro z hz hmem
  rw [kmswStage0Drawing_image] at hmem
  obtain ⟨hi, hr⟩ := segment_location hmem
  rcases hz with (hu | hl) | hd
  · exact (ne_of_gt hu) hi
  · exact (not_lt_of_ge hr) hl
  · exact (ne_of_lt hd) hi

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
theorem kmswStage0Drawing_far_not_mem (w : ℕ → Fin 3) :
    (2 * Complex.I : ℂ) ∉ (kmswStage0Drawing w).image := by
  apply exteriorRegion_avoids w
  exact Or.inl (Or.inl (by norm_num))

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result.
The complementary component of the far point. -/
@[expose] noncomputable def kmswStage0FarFace (w : ℕ → Fin 3) :
    (kmswStage0Drawing w).Face :=
  ⟨connectedComponentIn (kmswStage0Drawing w).imageᶜ (2 * Complex.I),
    2 * Complex.I, kmswStage0Drawing_far_not_mem w, rfl⟩

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result.
Both initial left wedges border the far face. -/
theorem kmswStage0Drawing_dartBorders_far (w : ℕ → Fin 3)
    (d : StageDart (kmswStage w 0).nextEdge) :
    (kmswStage0Drawing w).dartBorders d (kmswStage0FarFace w) := by
  have hregion : exteriorRegion ⊆ (kmswStage0FarFace w).val :=
    exteriorRegion_pathConnected.isConnected.isPreconnected.subset_connectedComponentIn
      (Or.inl (Or.inl (by norm_num))) (exteriorRegion_avoids w)
  refine ⟨1, by norm_num, ?_⟩
  intro t ε ht _htδ hε _hεδ
  apply hregion
  rcases d with ⟨e, b⟩
  cases b
  · apply Or.inl ∘ Or.inl
    change 0 < ((kmswStage0Arc false).start + (t : ℂ) *
      ((kmswStage0Arc false).initialDirection + (ε : ℂ) * Complex.I *
        (kmswStage0Arc false).initialDirection)).im
    simpa [kmswStage0Arc, Polyline.start, Polyline.initialDirection, Polyline.point]
      using mul_pos ht hε
  · apply Or.inr
    change ((kmswStage0Arc true).start + (t : ℂ) *
      ((kmswStage0Arc true).initialDirection + (ε : ℂ) * Complex.I *
        (kmswStage0Arc true).initialDirection)).im < 0
    simpa [kmswStage0Arc, Polyline.start, Polyline.initialDirection, Polyline.point]
      using neg_neg_of_pos (mul_pos ht hε)

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 1); not a paper result. -/
theorem kmswStage0Drawing_outer (w : ℕ → Fin 3)
    (d : StageDart (kmswStage w 0).nextEdge) :
    (kmswStageDirectedMap w 0).IsOuter d :=
  kmswZeroStepStage_outerDarts w d

end DirectedDistances.KMSW
