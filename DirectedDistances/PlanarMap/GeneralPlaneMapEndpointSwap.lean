/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapInvariance

/-! # Endpoint-storage invariance for general plane maps

Helper toward Definitions 1.1 / 3.1. Reversing selected parameterizations
changes stored endpoint order while preserving each geometric edge and, after
changing the orientation bit, its directed endpoints. -/

public section

namespace DirectedDistances.PlanarMap

open Set
open unitInterval

variable {V E : Type*}

/-- The central symmetry of the unit interval preserves the open parameter
interval. Helper toward Definitions 1.1 / 3.1. -/
theorem symm_mem_openParams_iff {t : I} :
    σ t ∈ openParams ↔ t ∈ openParams := by
  simp only [openParams, Set.mem_setOf_eq, unitInterval.coe_symm_eq]
  constructor <;> intro h <;> constructor <;>
    linarith [t.property.1, t.property.2]

/-- Reversing a path preserves the image of its open parameter interval.
Helper toward Definitions 1.1 / 3.1. -/
theorem path_symm_openParams_image {x y : ℂ} (γ : Path x y) :
    γ.symm '' openParams = γ '' openParams := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨σ t, symm_mem_openParams_iff.mpr ht, ?_⟩
    rfl
  · rintro ⟨t, ht, rfl⟩
    refine ⟨σ t, symm_mem_openParams_iff.mpr ht, ?_⟩
    change γ (σ (σ t)) = γ t
    exact congrArg γ (unitInterval.symm_symm t)

/-! The arc term with its endpoints cast to the selected storage order. -/
@[expose] noncomputable def PlaneGraphDrawing.endpointSwapArc
    (D : PlaneGraphDrawing V E) (swap : E → Bool) (e : E) :
    Path (D.pos (if swap e then D.tgt e else D.src e))
      (D.pos (if swap e then D.src e else D.tgt e)) :=
  if h : swap e = true then
    (D.arc e).symm.cast (by simp [h]) (by simp [h])
  else
    (D.arc e).cast (by simp [h]) (by simp [h])

/-- Pointwise description of the reparameterized arc. Helper toward
Definitions 1.1 / 3.1. -/
theorem endpointSwapArc_apply (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (e : E) (t : I) :
    D.endpointSwapArc swap e t =
      if swap e then D.arc e (σ t) else D.arc e t := by
  by_cases h : swap e = true
  · simp [PlaneGraphDrawing.endpointSwapArc, h, Path.cast_coe, Path.symm]
  · simp [PlaneGraphDrawing.endpointSwapArc, h, Path.cast_coe]

/-- Reverse the stored endpoint order and path parameterization on the
selected edges. Helper toward Definitions 1.1 / 3.1. -/
@[expose] noncomputable def PlaneGraphDrawing.endpointSwap (D : PlaneGraphDrawing V E)
    (swap : E → Bool) : PlaneGraphDrawing V E where
  src e := if swap e then D.tgt e else D.src e
  tgt e := if swap e then D.src e else D.tgt e
  pos := D.pos
  pos_injective := D.pos_injective
  arc e := D.endpointSwapArc swap e
  arc_injOn := by
    intro e x hx y hy hxy
    by_cases h : swap e = true
    · have hxy' : D.arc e (σ x) = D.arc e (σ y) := by
        simpa [endpointSwapArc_apply, h] using hxy
      have hs := D.arc_injOn e (symm_mem_openParams_iff.mpr hx)
        (symm_mem_openParams_iff.mpr hy) hxy'
      exact unitInterval.symm_involutive.injective hs
    · have hxy' : D.arc e x = D.arc e y := by simpa [endpointSwapArc_apply, h] using hxy
      exact D.arc_injOn e hx hy hxy'
  openArc_disjoint := by
    intro e f hef
    have hOpen (g : E) :
        (D.endpointSwapArc swap g) '' openParams = D.openArc g := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        by_cases h : swap g = true
        · exact ⟨σ t, symm_mem_openParams_iff.mpr ht,
            by simpa [endpointSwapArc_apply, h]⟩
        · exact ⟨t, ht, by simpa [endpointSwapArc_apply, h]⟩
      · rintro ⟨t, ht, rfl⟩
        by_cases h : swap g = true
        · exact ⟨σ t, symm_mem_openParams_iff.mpr ht,
            by simpa [endpointSwapArc_apply, h, unitInterval.symm_symm]⟩
        · exact ⟨t, ht, by simpa [endpointSwapArc_apply, h]⟩
    rw [hOpen e, hOpen f]
    exact D.openArc_disjoint e f hef
  openArc_avoids := by
    intro e v
    have hOpen : (D.endpointSwapArc swap e) '' openParams = D.openArc e := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        by_cases h : swap e = true
        · exact ⟨σ t, symm_mem_openParams_iff.mpr ht,
            by simpa [endpointSwapArc_apply, h]⟩
        · exact ⟨t, ht, by simpa [endpointSwapArc_apply, h]⟩
      · rintro ⟨t, ht, rfl⟩
        by_cases h : swap e = true
        · exact ⟨σ t, symm_mem_openParams_iff.mpr ht,
            by simpa [endpointSwapArc_apply, h, unitInterval.symm_symm]⟩
        · exact ⟨t, ht, by simpa [endpointSwapArc_apply, h]⟩
    rw [hOpen]
    exact D.openArc_avoids e v

@[simp]
theorem endpointSwap_pos (D : PlaneGraphDrawing V E) (swap : E → Bool) (v : V) :
    (D.endpointSwap swap).pos v = D.pos v := rfl

@[simp]
theorem endpointSwap_src (D : PlaneGraphDrawing V E) (swap : E → Bool) (e : E) :
    (D.endpointSwap swap).src e = if swap e then D.tgt e else D.src e := rfl

@[simp]
theorem endpointSwap_tgt (D : PlaneGraphDrawing V E) (swap : E → Bool) (e : E) :
    (D.endpointSwap swap).tgt e = if swap e then D.src e else D.tgt e := rfl

@[simp]
theorem endpointSwap_arc_apply (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (e : E) (t : I) :
    (D.endpointSwap swap).arc e t =
      if swap e then D.arc e (σ t) else D.arc e t := by
  change D.endpointSwapArc swap e t = _
  exact endpointSwapArc_apply D swap e t

/-- Complete edge images are independent of endpoint storage. Helper toward
Definitions 1.1 / 3.1. -/
theorem endpointSwap_arc_range (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (e : E) :
    Set.range ((D.endpointSwap swap).arc e) = Set.range (D.arc e) := by
  by_cases h : swap e = true
  · ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨σ t, ?_⟩
      have ht' : D.arc e (σ t) = z := by
        have hEq := endpointSwap_arc_apply D swap e t
        have ht'' := hEq.symm.trans ht
        simpa [h] using ht''
      exact ht'
    · rintro ⟨t, ht⟩
      refine ⟨σ t, ?_⟩
      have hEq := endpointSwap_arc_apply D swap e (σ t)
      have hPoint : (D.endpointSwap swap).arc e (σ t) = D.arc e t := by
        simpa [h] using hEq
      exact hPoint.trans ht
  · ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨t, ht⟩
      have hPoint : (D.endpointSwap swap).arc e t = D.arc e t := by
        simpa [h] using endpointSwap_arc_apply D swap e t
      exact ⟨t, hPoint.symm.trans ht⟩
    · rintro ⟨t, ht⟩
      have hPoint : (D.endpointSwap swap).arc e t = D.arc e t := by
        simpa [h] using endpointSwap_arc_apply D swap e t
      exact ⟨t, hPoint.trans ht⟩

/-- Open edge images are independent of endpoint storage. Helper toward
Definitions 1.1 / 3.1. -/
theorem endpointSwap_openArc (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (e : E) :
    (D.endpointSwap swap).openArc e = D.openArc e := by
  by_cases h : swap e = true
  · ext z
    constructor
    · rintro ⟨t, ht, hz⟩
      refine ⟨σ t, symm_mem_openParams_iff.mpr ht, ?_⟩
      have hEq := endpointSwap_arc_apply D swap e t
      have hPoint : (D.endpointSwap swap).arc e t = D.arc e (σ t) := by
        simpa [h] using hEq
      exact hPoint.symm.trans hz
    · rintro ⟨t, ht, hz⟩
      refine ⟨σ t, symm_mem_openParams_iff.mpr ht, ?_⟩
      have hEq := endpointSwap_arc_apply D swap e (σ t)
      have hPoint : (D.endpointSwap swap).arc e (σ t) = D.arc e t := by
        simpa [h] using hEq
      exact hPoint.trans hz
  · ext z
    constructor
    · rintro ⟨t, ht, hz⟩
      have hPoint : (D.endpointSwap swap).arc e t = D.arc e t := by
        simpa [h] using endpointSwap_arc_apply D swap e t
      exact ⟨t, ht, hPoint.symm.trans hz⟩
    · rintro ⟨t, ht, hz⟩
      have hPoint : (D.endpointSwap swap).arc e t = D.arc e t := by
        simpa [h] using endpointSwap_arc_apply D swap e t
      exact ⟨t, ht, hPoint.trans hz⟩

/-- The whole drawing image is unchanged by endpoint storage swaps. Helper
toward Definitions 1.1 / 3.1. -/
theorem endpointSwap_image (D : PlaneGraphDrawing V E) (swap : E → Bool) :
    (D.endpointSwap swap).image = D.image := by
  classical
  unfold PlaneGraphDrawing.image
  simp only [endpointSwap_pos]
  exact congrArg (fun s : Set ℂ => Set.range D.pos ∪ s)
    (Set.iUnion_congr fun e => endpointSwap_arc_range D swap e)

/-- A face is carried to the same subset of the plane after endpoint storage
swaps. Helper toward Definitions 1.1 / 3.1. -/
@[expose] def PlaneGraphDrawing.endpointSwapFace (D : PlaneGraphDrawing V E)
    (swap : E → Bool) (F : D.Face) : (D.endpointSwap swap).Face := by
  refine ⟨F.val, ?_⟩
  rcases F.property with ⟨z, hz, hF⟩
  refine ⟨z, ?_, ?_⟩
  · simpa [endpointSwap_image] using hz
  · simpa [endpointSwap_image] using hF

@[simp]
theorem endpointSwapFace_val (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (F : D.Face) : (D.endpointSwapFace swap F).val = F.val := rfl

/-- Unbounded-face status is independent of endpoint storage. Helper toward
Definitions 1.1 / 3.1. -/
theorem endpointSwap_isExternal_iff (D : PlaneGraphDrawing V E)
    (swap : E → Bool) (F : D.Face) :
    (D.endpointSwap swap).IsExternal (D.endpointSwapFace swap F) ↔ D.IsExternal F := Iff.rfl

/-- Edge multiplicities are independent of endpoint storage. Helper toward
Definitions 1.1 / 3.1. -/
theorem endpointSwap_faceMult (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (e : E) (F : D.Face) :
    D.faceMult e F = (D.endpointSwap swap).faceMult e (D.endpointSwapFace swap F) := by
  unfold PlaneGraphDrawing.faceMult
  rw [endpointSwap_openArc, endpointSwap_arc_range, endpointSwapFace_val]

/-- Face degrees are independent of endpoint storage. Helper toward
Definitions 1.1 / 3.1. -/
theorem endpointSwap_faceDegree (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (F : D.Face) :
    D.faceDegree F = (D.endpointSwap swap).faceDegree (D.endpointSwapFace swap F) := by
  classical
  unfold PlaneGraphDrawing.faceDegree
  apply iSup_congr
  intro s
  apply Finset.sum_congr rfl
  intro e he
  exact endpointSwap_faceMult D swap e F

/-- Faces correspond by their unchanged subsets of the plane. Helper toward
Definitions 1.1 / 3.1. -/
@[expose] noncomputable def PlaneGraphDrawing.endpointSwapFaceEquiv
    (D : PlaneGraphDrawing V E) (swap : E → Bool) :
    D.Face ≃ (D.endpointSwap swap).Face where
  toFun := D.endpointSwapFace swap
  invFun F := by
    refine ⟨F.val, ?_⟩
    rcases F.property with ⟨z, hz, hF⟩
    refine ⟨z, ?_, ?_⟩
    · simpa [endpointSwap_image] using hz
    · simpa [endpointSwap_image] using hF
  left_inv F := by apply Subtype.ext; rfl
  right_inv F := by apply Subtype.ext; rfl

/-- Internal-face status is unchanged by endpoint storage. Helper toward
Definition 1.1. -/
theorem endpointSwap_isInternal_iff (D : PlaneGraphDrawing V E)
    (swap : E → Bool) (F : D.Face) :
    (D.endpointSwap swap).IsInternal (D.endpointSwapFace swap F) ↔ D.IsInternal F := by
  simp [PlaneGraphDrawing.IsInternal, endpointSwap_isExternal_iff]

/-- Orient a swapped drawing so each directed edge keeps the same geometric
tail and head. Helper toward Definition 1.1. -/
@[expose] noncomputable def DirectedPlaneMap.endpointSwap
    (M : DirectedPlaneMap V E) (swap : E → Bool) : DirectedPlaneMap V E :=
  { toPlaneGraphDrawing := M.toPlaneGraphDrawing.endpointSwap swap
    forward := fun e => if swap e then !(M.forward e) else M.forward e }

namespace DirectedPlaneMap

variable {M : DirectedPlaneMap V E}

/-- Tail vertices are unchanged by a storage swap and the matching bit flip.
Helper toward Definition 1.1. -/
theorem endpointSwap_tail (M : DirectedPlaneMap V E) (swap : E → Bool) (e : E) :
    (M.endpointSwap swap).tail e = M.tail e := by
  by_cases hs : swap e = true <;> by_cases hf : M.forward e = true <;>
    simp [DirectedPlaneMap.endpointSwap, PlaneGraphDrawing.endpointSwap, hs, hf,
      DirectedPlaneMap.tail]

/-- Head vertices are unchanged by a storage swap and the matching bit flip.
Helper toward Definition 1.1. -/
theorem endpointSwap_head (M : DirectedPlaneMap V E) (swap : E → Bool) (e : E) :
    (M.endpointSwap swap).head e = M.head e := by
  by_cases hs : swap e = true <;> by_cases hf : M.forward e = true <;>
    simp [DirectedPlaneMap.endpointSwap, PlaneGraphDrawing.endpointSwap, hs, hf,
      DirectedPlaneMap.head]

/-- The directed step relation is unchanged by endpoint storage. Helper toward
Definition 1.1. -/
theorem endpointSwap_step_iff (M : DirectedPlaneMap V E) (swap : E → Bool)
    (u w : V) :
    (M.endpointSwap swap).step u w ↔ M.step u w := by
  rw [(M.endpointSwap swap).step_iff, M.step_iff]
  constructor
  · rintro ⟨e, ht, hh⟩
    exact ⟨e, by simpa [endpointSwap_tail] using ht,
      by simpa [endpointSwap_head] using hh⟩
  · rintro ⟨e, ht, hh⟩
    exact ⟨e, by simpa [endpointSwap_tail] using ht,
      by simpa [endpointSwap_head] using hh⟩

/-- Acyclicity is unchanged by endpoint storage. Helper toward Definition 1.1. -/
theorem endpointSwap_isAcyclic_iff (M : DirectedPlaneMap V E) (swap : E → Bool) :
    (M.endpointSwap swap).IsAcyclic ↔ M.IsAcyclic := by
  have hstep : (M.endpointSwap swap).step = M.step := by
    funext u w
    exact propext (endpointSwap_step_iff M swap u w)
  rw [(M.endpointSwap swap).isAcyclic_iff, M.isAcyclic_iff, hstep]

 
theorem endpointSwap_isSource_iff (M : DirectedPlaneMap V E) (swap : E → Bool)
    (v : V) : (M.endpointSwap swap).IsSource v ↔ M.IsSource v := by
  simp [DirectedPlaneMap.IsSource, endpointSwap_head]

/-- Sink status is unchanged by endpoint storage. Helper toward Definition 1.1. -/
theorem endpointSwap_isSink_iff (M : DirectedPlaneMap V E) (swap : E → Bool)
    (v : V) : (M.endpointSwap swap).IsSink v ↔ M.IsSink v := by
  simp [DirectedPlaneMap.IsSink, endpointSwap_tail]

/-- Bipolarity is unchanged by endpoint storage. Helper toward Definition 1.1. -/
theorem endpointSwap_isBipolar_iff (M : DirectedPlaneMap V E)
    (swap : E → Bool) : (M.endpointSwap swap).IsBipolar ↔ M.IsBipolar := by
  rw [M.isBipolar_iff, (M.endpointSwap swap).isBipolar_iff]
  have hSource :
      Subsingleton {v : V // (M.endpointSwap swap).IsSource v} ↔
        Subsingleton {v : V // M.IsSource v} := by
    constructor
    · intro h
      exact ⟨fun x y => Subtype.ext <| congrArg
        (fun z : {v : V // (M.endpointSwap swap).IsSource v} => z.1)
        (h.elim ⟨x.1, (endpointSwap_isSource_iff M swap x.1).mpr x.2⟩
          ⟨y.1, (endpointSwap_isSource_iff M swap y.1).mpr y.2⟩)⟩
    · intro h
      exact ⟨fun x y => Subtype.ext <| congrArg
        (fun z : {v : V // M.IsSource v} => z.1)
        (h.elim ⟨x.1, (endpointSwap_isSource_iff M swap x.1).mp x.2⟩
          ⟨y.1, (endpointSwap_isSource_iff M swap y.1).mp y.2⟩)⟩
  have hSink :
      Subsingleton {v : V // (M.endpointSwap swap).IsSink v} ↔
        Subsingleton {v : V // M.IsSink v} := by
    constructor
    · intro h
      exact ⟨fun x y => Subtype.ext <| congrArg
        (fun z : {v : V // (M.endpointSwap swap).IsSink v} => z.1)
        (h.elim ⟨x.1, (endpointSwap_isSink_iff M swap x.1).mpr x.2⟩
          ⟨y.1, (endpointSwap_isSink_iff M swap y.1).mpr y.2⟩)⟩
    · intro h
      exact ⟨fun x y => Subtype.ext <| congrArg
        (fun z : {v : V // M.IsSink v} => z.1)
        (h.elim ⟨x.1, (endpointSwap_isSink_iff M swap x.1).mp x.2⟩
          ⟨y.1, (endpointSwap_isSink_iff M swap y.1).mp y.2⟩)⟩
  simp only [endpointSwap_isAcyclic_iff, hSource, hSink]

end DirectedPlaneMap

/-- Endpoint storage swaps preserve the missing-edge tags and their external
face witnesses. Helper toward Definition 3.1. -/
@[expose] noncomputable def PlaneMapWithMissing.endpointSwap
    (D : PlaneMapWithMissing V E) (swap : E → Bool) : PlaneMapWithMissing V E :=
  { toPlaneGraphDrawing := D.toPlaneGraphDrawing.endpointSwap swap
    missing := D.missing
    missing_on_external := by
      intro e he
      rcases D.missing_on_external e he with ⟨F, hF, hcl⟩
      refine ⟨D.toPlaneGraphDrawing.endpointSwapFace swap F,
        (endpointSwap_isExternal_iff D.toPlaneGraphDrawing swap F).mpr hF, ?_⟩
      change Set.range ((D.toPlaneGraphDrawing.endpointSwap swap).arc e) ⊆
        closure (D.toPlaneGraphDrawing.endpointSwapFace swap F).val
      rw [endpointSwap_arc_range D.toPlaneGraphDrawing swap e,
        endpointSwapFace_val]
      exact hcl }

@[simp]
theorem endpointSwap_missing (D : PlaneMapWithMissing V E) (swap : E → Bool)
    (e : E) : (D.endpointSwap swap).missing e ↔ D.missing e := Iff.rfl

/-- The missing-edge external-face condition is unchanged by endpoint storage.
Helper toward Definition 3.1. -/
theorem endpointSwap_missingOnExternal_iff (D : PlaneMapWithMissing V E)
    (swap : E → Bool) (e : E) :
    (D.missing e → ∃ F : D.toPlaneGraphDrawing.Face,
      D.toPlaneGraphDrawing.IsExternal F ∧ Set.range (D.arc e) ⊆ closure F.val) ↔
    ((D.endpointSwap swap).missing e →
      ∃ F' : (D.endpointSwap swap).toPlaneGraphDrawing.Face,
        (D.endpointSwap swap).toPlaneGraphDrawing.IsExternal F' ∧
          Set.range ((D.endpointSwap swap).arc e) ⊆ closure F'.val) := by
  constructor
  · intro _ hm
    exact (D.endpointSwap swap).missing_on_external e hm
  · intro _ hm
    exact D.missing_on_external e hm

/-- Reverse stored endpoints only on present edges, flipping their stored
orientation bits while leaving all missing edges unoriented. Helper toward
Definition 3.1. -/
@[expose] noncomputable def DirectedPlaneMapWithMissing.endpointSwap
    (M : DirectedPlaneMapWithMissing V E) (swap : E → Bool) :
    DirectedPlaneMapWithMissing V E :=
  { toPlaneMapWithMissing := M.toPlaneMapWithMissing.endpointSwap swap
    forward := fun e => if swap e.val then !(M.forward e) else M.forward e }

namespace DirectedPlaneMapWithMissing

variable {M : DirectedPlaneMapWithMissing V E}

theorem endpointSwap_tail (M : DirectedPlaneMapWithMissing V E)
    (swap : E → Bool) (e : {e : E // ¬ M.toPlaneMapWithMissing.missing e}) :
    (M.endpointSwap swap).tail e = M.tail e := by
  by_cases hs : swap e.val = true <;> by_cases hf : M.forward e = true <;>
    simp [DirectedPlaneMapWithMissing.endpointSwap, PlaneMapWithMissing.endpointSwap,
      PlaneGraphDrawing.endpointSwap, hs, hf, DirectedPlaneMapWithMissing.tail]

theorem endpointSwap_head (M : DirectedPlaneMapWithMissing V E)
    (swap : E → Bool) (e : {e : E // ¬ M.toPlaneMapWithMissing.missing e}) :
    (M.endpointSwap swap).head e = M.head e := by
  by_cases hs : swap e.val = true <;> by_cases hf : M.forward e = true <;>
    simp [DirectedPlaneMapWithMissing.endpointSwap, PlaneMapWithMissing.endpointSwap,
      PlaneGraphDrawing.endpointSwap, hs, hf, DirectedPlaneMapWithMissing.head]

theorem endpointSwap_step_iff (M : DirectedPlaneMapWithMissing V E)
    (swap : E → Bool) (u w : V) :
    (M.endpointSwap swap).step u w ↔ M.step u w := by
  rw [(M.endpointSwap swap).step_iff, M.step_iff]
  constructor <;> rintro ⟨e, ht, hh⟩
  · exact ⟨e, (endpointSwap_tail M swap e).symm.trans ht,
      (endpointSwap_head M swap e).symm.trans hh⟩
  · exact ⟨e, (endpointSwap_tail M swap e).trans ht,
      (endpointSwap_head M swap e).trans hh⟩

theorem endpointSwap_isAcyclic_iff (M : DirectedPlaneMapWithMissing V E)
    (swap : E → Bool) :
    (M.endpointSwap swap).IsAcyclic ↔ M.IsAcyclic := by
  have hstep : (M.endpointSwap swap).step = M.step := by
    funext u w
    exact propext (endpointSwap_step_iff M swap u w)
  rw [(M.endpointSwap swap).isAcyclic_iff, M.isAcyclic_iff, hstep]

end DirectedPlaneMapWithMissing

/-- Bipolar triangulation, including every internal face degree, is unchanged
by endpoint storage. Helper toward Definition 1.1. -/
theorem endpointSwap_isBipolarTriangulation_iff
    (M : DirectedPlaneMap V E) (swap : E → Bool) :
    (M.endpointSwap swap).IsBipolarTriangulation ↔ M.IsBipolarTriangulation := by
  rw [M.isBipolarTriangulation_iff, (M.endpointSwap swap).isBipolarTriangulation_iff]
  constructor
  · rintro ⟨hb, htri⟩
    refine ⟨M.endpointSwap_isBipolar_iff swap |>.mp hb, ?_⟩
    intro F hInternal
    let F' := M.toPlaneGraphDrawing.endpointSwapFace swap F
    have hInternal' : (M.toPlaneGraphDrawing.endpointSwap swap).IsInternal F' := by
        simpa [F'] using
        (endpointSwap_isInternal_iff M.toPlaneGraphDrawing swap F).mpr hInternal
    calc
      M.toPlaneGraphDrawing.faceDegree F =
          (M.toPlaneGraphDrawing.endpointSwap swap).faceDegree F' := by
            simpa [F'] using endpointSwap_faceDegree M.toPlaneGraphDrawing swap F
      _ = 3 := htri F' hInternal'
  · rintro ⟨hb, htri⟩
    refine ⟨M.endpointSwap_isBipolar_iff swap |>.mpr hb, ?_⟩
    intro F' hInternal'
    let e := M.toPlaneGraphDrawing.endpointSwapFaceEquiv swap
    let F := e.symm F'
    have hF : e F = F' := e.apply_symm_apply F'
    have hInternal : M.toPlaneGraphDrawing.IsInternal F := by
      apply (endpointSwap_isInternal_iff M.toPlaneGraphDrawing swap F).mp
      have hInternalEq := hInternal'
      rw [← hF] at hInternalEq
      change (M.toPlaneGraphDrawing.endpointSwap swap).IsInternal
        (M.toPlaneGraphDrawing.endpointSwapFace swap F) at hInternalEq
      exact hInternalEq
    calc
      (M.toPlaneGraphDrawing.endpointSwap swap).faceDegree F' =
          (M.toPlaneGraphDrawing.endpointSwap swap).faceDegree (e F) :=
            congrArg _ hF.symm
      _ = M.toPlaneGraphDrawing.faceDegree F :=
            (endpointSwap_faceDegree M.toPlaneGraphDrawing swap F).symm
      _ = 3 := htri F hInternal

/-- A plane-map equivalence followed by arbitrary endpoint storage swaps.
Its `homeo` fields retain the full edge-image data, so arbitrary endpoint-
fixing reparameterizations are covered. Helper toward Definition 1.1. -/
structure DirectedPlaneMap.HomeoEndpointSwapEquiv
    (M : DirectedPlaneMap V E) (M' : DirectedPlaneMap V' E') where
  homeo : DirectedPlaneMap.HomeoEquiv M M'
  swap : E' → Bool

namespace DirectedPlaneMap.HomeoEndpointSwapEquiv

variable {M : DirectedPlaneMap V E} {M' : DirectedPlaneMap V' E'}

theorem isAcyclic_map_iff (e : DirectedPlaneMap.HomeoEndpointSwapEquiv M M') :
    M.IsAcyclic ↔ (M'.endpointSwap e.swap).IsAcyclic :=
  e.homeo.isAcyclic_map_iff.trans
    (DirectedPlaneMap.endpointSwap_isAcyclic_iff M' e.swap).symm

theorem isBipolar_map_iff (e : DirectedPlaneMap.HomeoEndpointSwapEquiv M M') :
    M.IsBipolar ↔ (M'.endpointSwap e.swap).IsBipolar :=
  e.homeo.isBipolar_map_iff.trans
    (DirectedPlaneMap.endpointSwap_isBipolar_iff M' e.swap).symm

theorem isBipolarTriangulation_map_iff
    (e : DirectedPlaneMap.HomeoEndpointSwapEquiv M M') :
    M.IsBipolarTriangulation ↔ (M'.endpointSwap e.swap).IsBipolarTriangulation :=
  e.homeo.isBipolarTriangulation_map_iff.trans
    (endpointSwap_isBipolarTriangulation_iff M' e.swap).symm

end DirectedPlaneMap.HomeoEndpointSwapEquiv

/-- A missing-edge drawing equivalence followed by endpoint storage swaps.
Helper toward Definition 3.1. -/
structure PlaneMapWithMissing.HomeoEndpointSwapEquiv
    (D : PlaneMapWithMissing V E) (D' : PlaneMapWithMissing V' E') where
  homeo : PlaneMapWithMissing.HomeoEquiv D D'
  swap : E' → Bool

namespace PlaneMapWithMissing.HomeoEndpointSwapEquiv

variable {D : PlaneMapWithMissing V E} {D' : PlaneMapWithMissing V' E'}

theorem missingOnExternal_map_iff
    (e : PlaneMapWithMissing.HomeoEndpointSwapEquiv D D') (f : E) :
    (D.missing f → ∃ F : D.toPlaneGraphDrawing.Face,
      D.toPlaneGraphDrawing.IsExternal F ∧ Set.range (D.arc f) ⊆ closure F.val) ↔
    ((D'.endpointSwap e.swap).missing (e.homeo.drawing.σE f) →
      ∃ F' : (D'.endpointSwap e.swap).toPlaneGraphDrawing.Face,
        (D'.endpointSwap e.swap).toPlaneGraphDrawing.IsExternal F' ∧
          Set.range ((D'.endpointSwap e.swap).arc (e.homeo.drawing.σE f)) ⊆
            closure F'.val) := by
  exact (e.homeo.missing_on_external_map_iff f).trans
    (endpointSwap_missingOnExternal_iff D' e.swap (e.homeo.drawing.σE f))

end PlaneMapWithMissing.HomeoEndpointSwapEquiv

/-- A homeomorphism equivalence preserving missing tags and the orientation
bits of present edges, followed by endpoint storage swaps and matching bit
flips. Helper toward Definition 3.1. -/
structure DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv
    (M : DirectedPlaneMapWithMissing V E)
    (M' : DirectedPlaneMapWithMissing V' E') where
  homeo : DirectedPlaneMapWithMissing.HomeoEquiv M M'
  swap : E' → Bool

namespace DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv

variable {M : DirectedPlaneMapWithMissing V E}
  {M' : DirectedPlaneMapWithMissing V' E'}

/-- Missing tags are unchanged by the combined equivalence.
Helper toward Definition 3.1. -/
theorem missing_map (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M')
    (f : E) :
    (M'.endpointSwap e.swap).toPlaneMapWithMissing.missing
      (e.homeo.drawing.drawing.σE f) ↔ M.toPlaneMapWithMissing.missing f :=
  (endpointSwap_missing M'.toPlaneMapWithMissing e.swap _).trans
    (e.homeo.drawing.missing_map f)

/-- Present edges correspond bijectively, including after endpoint swaps.
Helper toward Definition 3.1. -/
@[expose] noncomputable def presentEdgeEquiv
    (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M') :
    {f : E // ¬ M.toPlaneMapWithMissing.missing f} ≃
      {f : E' // ¬ (M'.endpointSwap e.swap).toPlaneMapWithMissing.missing f} :=
  e.homeo.presentEdgeEquiv

/-- The forward bit flips precisely on the selected present edges.
Helper toward Definition 3.1. -/
theorem forward_map (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M')
    (f : {f : E // ¬ M.toPlaneMapWithMissing.missing f}) :
    (M'.endpointSwap e.swap).forward (e.presentEdgeEquiv f) =
      if e.swap (e.homeo.drawing.drawing.σE f.val) then
        !(M.forward f) else M.forward f := by
  have hf : M'.forward (e.homeo.presentEdgeEquiv f) = M.forward f :=
    e.homeo.forward_map f
  change (if e.swap (e.homeo.drawing.drawing.σE f.val) then
    !(M'.forward (e.homeo.presentEdgeEquiv f)) else
      M'.forward (e.homeo.presentEdgeEquiv f)) = _
  rw [hf]

/-- Present-edge tails are transported by the vertex equivalence.
Helper toward Definition 3.1. -/
theorem tail_map (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M')
    (f : {f : E // ¬ M.toPlaneMapWithMissing.missing f}) :
    (M'.endpointSwap e.swap).tail (e.presentEdgeEquiv f) =
      e.homeo.drawing.drawing.σV (M.tail f) :=
  (DirectedPlaneMapWithMissing.endpointSwap_tail M' e.swap
    (e.homeo.presentEdgeEquiv f)).trans (e.homeo.tail_map f)

/-- Present-edge heads are transported by the vertex equivalence.
Helper toward Definition 3.1. -/
theorem head_map (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M')
    (f : {f : E // ¬ M.toPlaneMapWithMissing.missing f}) :
    (M'.endpointSwap e.swap).head (e.presentEdgeEquiv f) =
      e.homeo.drawing.drawing.σV (M.head f) :=
  (DirectedPlaneMapWithMissing.endpointSwap_head M' e.swap
    (e.homeo.presentEdgeEquiv f)).trans (e.homeo.head_map f)

/-- Transport an external-face witness through the homeomorphism and retain
its subset of the plane under endpoint swaps. Helper toward Definition 3.1. -/
theorem externalFaceClosure_map
    (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M')
    (f : E) (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F)
    (hcl : Set.range (M.toPlaneMapWithMissing.arc f) ⊆ closure F.val) :
    ∃ F' : (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F' ∧
        Set.range ((M'.endpointSwap e.swap).toPlaneMapWithMissing.arc
          (e.homeo.drawing.drawing.σE f)) ⊆ closure F'.val := by
  obtain ⟨G, hG, hclG⟩ := e.homeo.drawing.externalFaceClosure_map f F hF hcl
  refine ⟨M'.toPlaneMapWithMissing.toPlaneGraphDrawing.endpointSwapFace e.swap G,
    (endpointSwap_isExternal_iff _ _ _).mpr hG, ?_⟩
  change Set.range ((M'.toPlaneMapWithMissing.toPlaneGraphDrawing.endpointSwap
    e.swap).arc _) ⊆ closure G.val
  rw [endpointSwap_arc_range]
  exact hclG

/-- The external-face closure condition is invariant, with witnesses
transported in both directions. Helper toward Definition 3.1. -/
theorem externalFaceClosure_map_iff
    (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M') (f : E) :
    (∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F ∧
        Set.range (M.toPlaneMapWithMissing.arc f) ⊆ closure F.val) ↔
    (∃ F' : (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F' ∧
        Set.range ((M'.endpointSwap e.swap).toPlaneMapWithMissing.arc
          (e.homeo.drawing.drawing.σE f)) ⊆ closure F'.val) := by
  constructor
  · rintro ⟨F, hF, hcl⟩
    exact e.externalFaceClosure_map f F hF hcl
  · rintro ⟨F', hF', hcl'⟩
    let fe := M'.toPlaneMapWithMissing.toPlaneGraphDrawing.endpointSwapFaceEquiv e.swap
    let G := fe.symm F'
    have hG : fe G = F' := fe.apply_symm_apply F'
    rw [← hG] at hF' hcl'
    have hExternal : M'.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal G :=
      (endpointSwap_isExternal_iff _ _ G).mp hF'
    have hClosure : Set.range (M'.toPlaneMapWithMissing.arc
        (e.homeo.drawing.drawing.σE f)) ⊆ closure G.val := by
      change Set.range
        ((M'.toPlaneMapWithMissing.toPlaneGraphDrawing.endpointSwap e.swap).arc
          (e.homeo.drawing.drawing.σE f)) ⊆ closure G.val at hcl'
      rw [endpointSwap_arc_range] at hcl'
      exact hcl'
    exact (e.homeo.drawing.externalFaceClosure_map_iff f).mpr
      ⟨G, hExternal, hClosure⟩

/-- The Definition 3.1 missing-edge condition is invariant, by transporting
its tag and external-face witness. Helper toward Definition 3.1. -/
theorem missing_on_external_map_iff
    (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M') (f : E) :
    (M.toPlaneMapWithMissing.missing f →
      ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F ∧
          Set.range (M.toPlaneMapWithMissing.arc f) ⊆ closure F.val) ↔
    ((M'.endpointSwap e.swap).toPlaneMapWithMissing.missing
        (e.homeo.drawing.drawing.σE f) →
      ∃ F' : (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F' ∧
          Set.range ((M'.endpointSwap e.swap).toPlaneMapWithMissing.arc
            (e.homeo.drawing.drawing.σE f)) ⊆ closure F'.val) := by
  constructor
  · intro h hm
    exact (e.externalFaceClosure_map_iff f).mp (h ((e.missing_map f).mp hm))
  · intro h hm
    exact (e.externalFaceClosure_map_iff f).mpr (h ((e.missing_map f).mpr hm))

/-- Directed steps using present edges are invariant.
Helper toward Definition 3.1. -/
theorem step_map_iff (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M')
    (u w : V) :
    M.step u w ↔ (M'.endpointSwap e.swap).step
      (e.homeo.drawing.drawing.σV u) (e.homeo.drawing.drawing.σV w) :=
  (e.homeo.step_map_iff u w).trans
    (DirectedPlaneMapWithMissing.endpointSwap_step_iff M' e.swap _ _).symm

/-- Acyclicity on present edges is invariant.
Helper toward Definition 3.1. -/
theorem isAcyclic_map_iff
    (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M') :
    M.IsAcyclic ↔ (M'.endpointSwap e.swap).IsAcyclic :=
  e.homeo.isAcyclic_map_iff.trans
    (DirectedPlaneMapWithMissing.endpointSwap_isAcyclic_iff M' e.swap).symm

/-- Every Definition 3.1 predicate is invariant under the combined equivalence.
Helper toward Definition 3.1. -/
theorem definition31_invariant
    (e : DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv M M') :
    (∀ f, (M'.endpointSwap e.swap).toPlaneMapWithMissing.missing
      (e.homeo.drawing.drawing.σE f) ↔ M.toPlaneMapWithMissing.missing f) ∧
    (∀ f, (M.toPlaneMapWithMissing.missing f →
      ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        M.toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F ∧
          Set.range (M.toPlaneMapWithMissing.arc f) ⊆ closure F.val) ↔
      ((M'.endpointSwap e.swap).toPlaneMapWithMissing.missing
          (e.homeo.drawing.drawing.σE f) →
        ∃ F' : (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          (M'.endpointSwap e.swap).toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F' ∧
            Set.range ((M'.endpointSwap e.swap).toPlaneMapWithMissing.arc
              (e.homeo.drawing.drawing.σE f)) ⊆ closure F'.val)) ∧
    (∀ u w, M.step u w ↔ (M'.endpointSwap e.swap).step
      (e.homeo.drawing.drawing.σV u) (e.homeo.drawing.drawing.σV w)) ∧
    (M.IsAcyclic ↔ (M'.endpointSwap e.swap).IsAcyclic) :=
  ⟨e.missing_map, e.missing_on_external_map_iff, e.step_map_iff, e.isAcyclic_map_iff⟩

end DirectedPlaneMapWithMissing.HomeoEndpointSwapEquiv

end DirectedDistances.PlanarMap

end

