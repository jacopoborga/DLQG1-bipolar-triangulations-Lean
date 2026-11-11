/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMap









public section

namespace DirectedDistances.PlanarMap

variable {V E V' E' : Type*}

/-- A drawing equivalence transports vertices, edges, positions, endpoints,
and the geometric images of complete and open edges. Endpoints are transported
in the stored `src`/`tgt` order. -/
structure PlaneGraphDrawing.HomeoEquiv
    (D : PlaneGraphDrawing V E) (D' : PlaneGraphDrawing V' E') where
  h : ℂ ≃ₜ ℂ
  σV : V ≃ V'
  σE : E ≃ E'
  pos_map : ∀ v, D'.pos (σV v) = h (D.pos v)
  src_map : ∀ e, D'.src (σE e) = σV (D.src e)
  tgt_map : ∀ e, D'.tgt (σE e) = σV (D.tgt e)
  arc_range_map : ∀ e, Set.range (D'.arc (σE e)) = h '' Set.range (D.arc e)
  openArc_map : ∀ e, h '' D.openArc e = D'.openArc (σE e)

/-- A directed drawing equivalence also transports the orientation of every edge. -/
structure DirectedPlaneMap.HomeoEquiv
    (M : DirectedPlaneMap V E) (M' : DirectedPlaneMap V' E') where
  drawing : PlaneGraphDrawing.HomeoEquiv M.toPlaneGraphDrawing M'.toPlaneGraphDrawing
  forward_map : ∀ e, M'.forward (drawing.σE e) = M.forward e

/-- A missing-edge drawing equivalence transports the missing-edge tags. -/
structure PlaneMapWithMissing.HomeoEquiv
    (D : PlaneMapWithMissing V E) (D' : PlaneMapWithMissing V' E') where
  drawing : PlaneGraphDrawing.HomeoEquiv D.toPlaneGraphDrawing D'.toPlaneGraphDrawing
  missing_map : ∀ e, D'.missing (drawing.σE e) ↔ D.missing e

/-- A directed missing-edge equivalence also transports the orientations on
present edges. -/
structure DirectedPlaneMapWithMissing.HomeoEquiv
    (M : DirectedPlaneMapWithMissing V E)
    (M' : DirectedPlaneMapWithMissing V' E') where
  drawing : PlaneMapWithMissing.HomeoEquiv
    M.toPlaneMapWithMissing M'.toPlaneMapWithMissing
  forward_map : ∀ e : {e : E // ¬ M.toPlaneMapWithMissing.missing e},
    M'.forward ⟨drawing.drawing.σE e.val,
      by simpa [drawing.missing_map] using e.property⟩ = M.forward e

namespace PlaneGraphDrawing.HomeoEquiv

open scoped Topology

variable {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}

/-- The inverse of a drawing equivalence. -/
@[expose] noncomputable def symm (e : PlaneGraphDrawing.HomeoEquiv D D') :
    PlaneGraphDrawing.HomeoEquiv D' D where
  h := e.h.symm
  σV := e.σV.symm
  σE := e.σE.symm
  pos_map := by
    intro v
    have hv := e.pos_map (e.σV.symm v)
    simpa using (congrArg e.h.symm hv).symm
  src_map := by
    intro f
    have hf := e.src_map (e.σE.symm f)
    simpa using (congrArg e.σV.symm hf).symm
  tgt_map := by
    intro f
    have hf := e.tgt_map (e.σE.symm f)
    simpa using (congrArg e.σV.symm hf).symm
  arc_range_map := by
    intro f
    have hf := e.arc_range_map (e.σE.symm f)
    rw [e.σE.apply_symm_apply] at hf
    simpa [Set.image_image] using
      (congrArg (fun s : Set ℂ => e.h.symm '' s) hf).symm
  openArc_map := by
    intro f
    have hf := e.openArc_map (e.σE.symm f)
    rw [e.σE.apply_symm_apply] at hf
    simpa [Set.image_image] using
      (congrArg (fun s : Set ℂ => e.h.symm '' s) hf).symm

/-- The drawing image is carried to the drawing image by the homeomorphism. -/
theorem image_map (e : PlaneGraphDrawing.HomeoEquiv D D') :
    e.h '' D.image = D'.image := by
  classical
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Set.range D.pos ∪ ⋃ f, Set.range (D.arc f) at hx
    rcases hx with hxv | hxe
    · rcases hxv with ⟨v, rfl⟩
      apply Or.inl
      exact ⟨e.σV v, e.pos_map v⟩
    · rcases Set.mem_iUnion.mp hxe with ⟨f, hf⟩
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨e.σE f, ?_⟩
      rw [e.arc_range_map f]
      exact ⟨_, hf, rfl⟩
  · intro hz
    change z ∈ Set.range D'.pos ∪ ⋃ f, Set.range (D'.arc f) at hz
    rcases hz with hzv | hze
    · rcases hzv with ⟨v', rfl⟩
      refine ⟨D.pos (e.σV.symm v'), Or.inl ⟨e.σV.symm v', rfl⟩, ?_⟩
      simpa using (e.pos_map (e.σV.symm v')).symm
    · rcases Set.mem_iUnion.mp hze with ⟨f', hf'⟩
      let f := e.σE.symm f'
      have hmem : e.h.symm z ∈ Set.range (D.arc f) := by
        have : z ∈ Set.range (D'.arc (e.σE f)) := by
          change z ∈ Set.range (D'.arc (e.σE (e.σE.symm f')))
          rw [e.σE.apply_symm_apply]
          exact hf'
        rw [e.arc_range_map f] at this
        rcases this with ⟨y, hy, rfl⟩
        simpa using hy
      refine ⟨e.h.symm z, Or.inr (Set.mem_iUnion.mpr ⟨f, hmem⟩), ?_⟩
      exact e.h.apply_symm_apply z

/-- Homeomorphisms of the complex plane preserve boundedness: closures of
bounded sets are compact in `ℂ`. -/
theorem isBounded_image (e : PlaneGraphDrawing.HomeoEquiv D D')
    {s : Set ℂ} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (e.h '' s) := by
  have hc : IsCompact (closure s) := hs.isCompact_closure
  have hc' : IsCompact (e.h '' closure s) := hc.image e.h.continuous
  exact hc'.isBounded.subset (Set.image_mono subset_closure)

/-- Boundedness is invariant under the drawing homeomorphism. -/
theorem isBounded_image_iff (e : PlaneGraphDrawing.HomeoEquiv D D')
    (s : Set ℂ) :
    Bornology.IsBounded (e.h '' s) ↔ Bornology.IsBounded s := by
  constructor
  · intro hs
    have hs' := e.symm.isBounded_image (s := e.h '' s) (by simpa using hs)
    change Bornology.IsBounded (e.h.symm '' (e.h '' s)) at hs'
    have himage : e.h.symm '' (e.h '' s) = s := by
      rw [Set.image_image]
      simp
    rw [himage] at hs'
    exact hs'
  · exact e.isBounded_image

/-- The face induced by a drawing equivalence is the image of the original
face. -/
@[expose] def faceMap (e : PlaneGraphDrawing.HomeoEquiv D D') (F : D.Face) : D'.Face :=
  ⟨e.h '' F.val, by
    rcases F.property with ⟨z, hz, hF⟩
    refine ⟨e.h z, ?_, ?_⟩
    · intro hz'
      apply hz
      have hx : e.h z ∈ e.h '' D.image := by rw [e.image_map]; exact hz'
      rcases hx with ⟨x, hx, hxz⟩
      exact e.h.injective hxz ▸ hx
    · have hc : e.h '' D.imageᶜ = D'.imageᶜ := by
        rw [← e.image_map, e.h.image_compl]
      rw [hF]
      rw [← hc]
      exact e.h.image_connectedComponentIn hz⟩

@[simp]
theorem faceMap_val (e : PlaneGraphDrawing.HomeoEquiv D D') (F : D.Face) :
    (e.faceMap F).val = e.h '' F.val := rfl

/-- Faces correspond bijectively under a drawing equivalence. -/
@[expose] noncomputable def faceEquiv (e : PlaneGraphDrawing.HomeoEquiv D D') : D.Face ≃ D'.Face where
  toFun := e.faceMap
  invFun := e.symm.faceMap
  left_inv F := by
    apply Subtype.ext
    change e.h.symm '' (e.h '' F.val) = F.val
    ext x
    simp
  right_inv F' := by
    apply Subtype.ext
    change e.h '' (e.h.symm '' F'.val) = F'.val
    ext x
    simp

/-- External faces are preserved by a drawing equivalence. -/
theorem isExternal_faceMap_iff (e : PlaneGraphDrawing.HomeoEquiv D D')
    (F : D.Face) :
    D'.IsExternal (e.faceMap F) ↔ D.IsExternal F := by
  rw [D'.isExternal_iff, D.isExternal_iff]
  simpa [e.faceMap_val] using (e.isBounded_image_iff F.val).not

end PlaneGraphDrawing.HomeoEquiv

namespace PlaneGraphDrawing.HomeoEquiv

open scoped Topology

variable {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}

/-- Neighbourhood membership is preserved by the homeomorphism. -/
theorem mem_nhds_image_iff (e : PlaneGraphDrawing.HomeoEquiv D D')
    (x : ℂ) (s : Set ℂ) :
    s ∈ 𝓝 x ↔ e.h '' s ∈ 𝓝 (e.h x) := by
  rw [← e.h.map_nhds_eq x]
  exact (Filter.image_mem_map_iff e.h.injective).symm

/-- Edge multiplicity is invariant under drawing equivalence. -/
theorem faceMult_map (e : PlaneGraphDrawing.HomeoEquiv D D')
    (f : E) (F : D.Face) :
    D.faceMult f F = D'.faceMult (e.σE f) (e.faceMap F) := by
  classical
  let A := D.openArc f
  let A' := D'.openArc (e.σE f)
  let B := F.val ∪ Set.range (D.arc f)
  let B' := (e.faceMap F).val ∪ Set.range (D'.arc (e.σE f))
  have hB : e.h '' B = B' := by
    change e.h '' (F.val ∪ Set.range (D.arc f)) =
      (e.faceMap F).val ∪ Set.range (D'.arc (e.σE f))
    rw [Set.image_union, e.faceMap_val, e.arc_range_map]
  have hFirst :
      (∀ x ∈ A, B ∈ 𝓝 x) ↔ (∀ y ∈ A', B' ∈ 𝓝 y) := by
    rw [show A' = e.h '' A from (e.openArc_map f).symm]
    constructor
    · intro h y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [← hB]
      exact (e.mem_nhds_image_iff x B).mp (h x hx)
    · intro h x hx
      apply (e.mem_nhds_image_iff x B).mpr
      have hmem : e.h x ∈ e.h '' A := ⟨x, hx, rfl⟩
      have hn := h (e.h x) hmem
      rw [← hB] at hn
      exact hn
  have hSecond : A ⊆ closure F.val ↔ A' ⊆ closure (e.faceMap F).val := by
    rw [show A' = e.h '' A from (e.openArc_map f).symm,
      e.faceMap_val, ← e.h.image_closure]
    constructor
    · intro hs y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, hs hx, rfl⟩
    · intro hs x hx
      have hy := hs ⟨x, hx, rfl⟩
      rcases hy with ⟨y, hy, hxy⟩
      exact e.h.injective hxy ▸ hy
  unfold PlaneGraphDrawing.faceMult
  congr 1
  · exact propext (by simpa [A, A', B, B', e.faceMap_val] using hFirst)
  · congr 1
    exact propext (by simpa [A, A', B, B', e.faceMap_val] using hSecond)

end PlaneGraphDrawing.HomeoEquiv

namespace PlaneGraphDrawing.HomeoEquiv

variable {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}

/-- Face degree is invariant under drawing equivalence; the supremum is
reindexed by the edge bijection. -/
theorem faceDegree_map (e : PlaneGraphDrawing.HomeoEquiv D D')
    (F : D.Face) :
    D.faceDegree F = D'.faceDegree (e.faceMap F) := by
  classical
  unfold PlaneGraphDrawing.faceDegree
  apply (Equiv.finsetCongr e.σE).iSup_congr
  intro s
  rw [Equiv.finsetCongr_apply]
  symm
  apply Finset.sum_bij (fun x _ => e.σE x)
  · intro x hx
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  · intro x hx y hy hxy
    exact e.σE.injective hxy
  · intro y hy
    rcases Finset.mem_map.mp hy with ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩
  · intro x hx
    exact e.faceMult_map x F

/-- Internal-face status is preserved by a drawing equivalence. -/
theorem isInternal_faceMap_iff (e : PlaneGraphDrawing.HomeoEquiv D D')
    (F : D.Face) :
    D'.IsInternal (e.faceMap F) ↔ D.IsInternal F := by
  rw [D'.isInternal_iff_not_isExternal, D.isInternal_iff_not_isExternal,
    e.isExternal_faceMap_iff]

end PlaneGraphDrawing.HomeoEquiv

namespace DirectedPlaneMap.HomeoEquiv

variable {M : DirectedPlaneMap V E} {M' : DirectedPlaneMap V' E'}

@[expose] noncomputable def symm (e : DirectedPlaneMap.HomeoEquiv M M') :
    DirectedPlaneMap.HomeoEquiv M' M where
  drawing := e.drawing.symm
  forward_map := by
    intro f
    have hf := e.forward_map (e.drawing.σE.symm f)
    rw [e.drawing.σE.apply_symm_apply] at hf
    exact hf.symm

/-- Tail vertices are transported along the vertex bijection. -/
theorem tail_map (e : DirectedPlaneMap.HomeoEquiv M M') (f : E) :
    M'.tail (e.drawing.σE f) = e.drawing.σV (M.tail f) := by
  by_cases hf : M.forward f
  · simp [DirectedPlaneMap.tail, hf, e.forward_map, e.drawing.src_map]
  · simp [DirectedPlaneMap.tail, hf, e.forward_map, e.drawing.tgt_map]

/-- Head vertices are transported along the vertex bijection. -/
theorem head_map (e : DirectedPlaneMap.HomeoEquiv M M') (f : E) :
    M'.head (e.drawing.σE f) = e.drawing.σV (M.head f) := by
  by_cases hf : M.forward f
  · simp [DirectedPlaneMap.head, hf, e.forward_map, e.drawing.tgt_map]
  · simp [DirectedPlaneMap.head, hf, e.forward_map, e.drawing.src_map]

/-- Directed steps correspond under the transported edge and vertex maps. -/
theorem step_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') (u w : V) :
    M.step u w ↔ M'.step (e.drawing.σV u) (e.drawing.σV w) := by
  rw [M.step_iff, M'.step_iff]
  constructor
  · rintro ⟨f, ht, hh⟩
    refine ⟨e.drawing.σE f, ?_, ?_⟩
    · simpa [e.tail_map] using congrArg e.drawing.σV ht
    · simpa [e.head_map] using congrArg e.drawing.σV hh
  · rintro ⟨f', ht, hh⟩
    let f := e.drawing.σE.symm f'
    have hef : e.drawing.σE f = f' := e.drawing.σE.apply_symm_apply f'
    refine ⟨f, ?_, ?_⟩
    · apply e.drawing.σV.injective
      calc
        e.drawing.σV (M.tail f) = M'.tail (e.drawing.σE f) := (e.tail_map f).symm
        _ = M'.tail f' := by rw [hef]
        _ = e.drawing.σV u := ht
    · apply e.drawing.σV.injective
      calc
        e.drawing.σV (M.head f) = M'.head (e.drawing.σE f) := (e.head_map f).symm
        _ = M'.head f' := by rw [hef]
        _ = e.drawing.σV w := hh

theorem transGen_map (e : DirectedPlaneMap.HomeoEquiv M M') {u w : V}
    (h : Relation.TransGen M.step u w) :
    Relation.TransGen M'.step (e.drawing.σV u) (e.drawing.σV w) := by
  have hr : M.step ≤ fun a b => M'.step (e.drawing.σV a) (e.drawing.σV b) := by
    intro a b hab
    exact (e.step_map_iff a b).mp hab
  exact h.lift e.drawing.σV hr

theorem transGen_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') {u w : V} :
    Relation.TransGen M.step u w ↔
      Relation.TransGen M'.step (e.drawing.σV u) (e.drawing.σV w) := by
  constructor
  · exact e.transGen_map
  · intro h
    have h' := e.symm.transGen_map h
    change Relation.TransGen M.step
      (e.drawing.σV.symm (e.drawing.σV u))
      (e.drawing.σV.symm (e.drawing.σV w)) at h'
    simpa using h'

/-- Acyclicity is preserved by a directed drawing equivalence. -/
theorem isAcyclic_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') :
    M.IsAcyclic ↔ M'.IsAcyclic := by
  rw [M.isAcyclic_iff, M'.isAcyclic_iff]
  constructor
  · intro h v' cyc
    obtain ⟨v, rfl⟩ := e.drawing.σV.surjective v'
    exact h v ((e.transGen_map_iff).mpr cyc)
  · intro h v cyc
    exact h (e.drawing.σV v) ((e.transGen_map_iff).mp cyc)

/-- Source status is transported to the corresponding vertex. -/
theorem isSource_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') (v : V) :
    M.IsSource v ↔ M'.IsSource (e.drawing.σV v) := by
  rw [M.isSource_iff, M'.isSource_iff]
  constructor
  · intro hs f'
    let f := e.drawing.σE.symm f'
    have hef := e.drawing.σE.apply_symm_apply f'
    intro hhead
    have hval : M.head f = v := e.drawing.σV.injective (by
      calc
        e.drawing.σV (M.head f) = M'.head (e.drawing.σE f) := (e.head_map f).symm
        _ = M'.head f' := by rw [hef]
        _ = e.drawing.σV v := hhead)
    exact hs f hval
  · intro hs f hhead
    apply hs (e.drawing.σE f)
    calc
      M'.head (e.drawing.σE f) = e.drawing.σV (M.head f) := e.head_map f
      _ = e.drawing.σV v := congrArg e.drawing.σV hhead

/-- Sink status is transported to the corresponding vertex. -/
theorem isSink_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') (v : V) :
    M.IsSink v ↔ M'.IsSink (e.drawing.σV v) := by
  rw [M.isSink_iff, M'.isSink_iff]
  constructor
  · intro hs f'
    let f := e.drawing.σE.symm f'
    have hef := e.drawing.σE.apply_symm_apply f'
    intro htail
    have hval : M.tail f = v := e.drawing.σV.injective (by
      calc
        e.drawing.σV (M.tail f) = M'.tail (e.drawing.σE f) := (e.tail_map f).symm
        _ = M'.tail f' := by rw [hef]
        _ = e.drawing.σV v := htail)
    exact hs f hval
  · intro hs f htail
    apply hs (e.drawing.σE f)
    calc
      M'.tail (e.drawing.σE f) = e.drawing.σV (M.tail f) := e.tail_map f
      _ = e.drawing.σV v := congrArg e.drawing.σV htail

/-- Subsingleton source sets correspond under the vertex equivalence. -/
theorem source_subsingleton_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') :
    Subsingleton {v : V // M.IsSource v} ↔
      Subsingleton {v : V' // M'.IsSource v} := by
  constructor
  · intro hs
    constructor
    intro a b
    apply Subtype.ext
    let a' : {v : V // M.IsSource v} := ⟨e.drawing.σV.symm a.1,
      (e.isSource_map_iff _).2 (by simpa using a.2)⟩
    let b' : {v : V // M.IsSource v} := ⟨e.drawing.σV.symm b.1,
      (e.isSource_map_iff _).2 (by simpa using b.2)⟩
    have hab := congrArg Subtype.val (hs.elim a' b')
    simpa [a', b'] using congrArg e.drawing.σV hab
  · intro hs
    constructor
    intro a b
    apply Subtype.ext
    let a' : {v : V' // M'.IsSource v} :=
      ⟨e.drawing.σV a.1, (e.isSource_map_iff _).mp a.2⟩
    let b' : {v : V' // M'.IsSource v} :=
      ⟨e.drawing.σV b.1, (e.isSource_map_iff _).mp b.2⟩
    have hab := congrArg Subtype.val (hs.elim a' b')
    have hab' : e.drawing.σV a.1 = e.drawing.σV b.1 := by
      simpa [a', b'] using hab
    exact e.drawing.σV.injective hab'

/-- Subsingleton sink sets correspond under the vertex equivalence. -/
theorem sink_subsingleton_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') :
    Subsingleton {v : V // M.IsSink v} ↔
      Subsingleton {v : V' // M'.IsSink v} := by
  constructor
  · intro hs
    constructor
    intro a b
    apply Subtype.ext
    let a' : {v : V // M.IsSink v} := ⟨e.drawing.σV.symm a.1,
      (e.isSink_map_iff _).2 (by simpa using a.2)⟩
    let b' : {v : V // M.IsSink v} := ⟨e.drawing.σV.symm b.1,
      (e.isSink_map_iff _).2 (by simpa using b.2)⟩
    have hab := congrArg Subtype.val (hs.elim a' b')
    simpa [a', b'] using congrArg e.drawing.σV hab
  · intro hs
    constructor
    intro a b
    apply Subtype.ext
    let a' : {v : V' // M'.IsSink v} :=
      ⟨e.drawing.σV a.1, (e.isSink_map_iff _).mp a.2⟩
    let b' : {v : V' // M'.IsSink v} :=
      ⟨e.drawing.σV b.1, (e.isSink_map_iff _).mp b.2⟩
    have hab := congrArg Subtype.val (hs.elim a' b')
    have hab' : e.drawing.σV a.1 = e.drawing.σV b.1 := by
      simpa [a', b'] using hab
    exact e.drawing.σV.injective hab'

/-- Bipolarity is preserved by a directed drawing equivalence. -/
theorem isBipolar_map_iff (e : DirectedPlaneMap.HomeoEquiv M M') :
    M.IsBipolar ↔ M'.IsBipolar := by
  rw [M.isBipolar_iff, M'.isBipolar_iff]
  constructor
  · rintro ⟨ha, hs, ht⟩
    exact ⟨e.isAcyclic_map_iff.mp ha,
      e.source_subsingleton_map_iff.mp hs,
      e.sink_subsingleton_map_iff.mp ht⟩
  · rintro ⟨ha, hs, ht⟩
    exact ⟨e.isAcyclic_map_iff.mpr ha,
      e.source_subsingleton_map_iff.mpr hs,
      e.sink_subsingleton_map_iff.mpr ht⟩

/-- Bipolar triangulation is preserved, including all internal face degrees. -/
theorem isBipolarTriangulation_map_iff
    (e : DirectedPlaneMap.HomeoEquiv M M') :
    M.IsBipolarTriangulation ↔ M'.IsBipolarTriangulation := by
  rw [M.isBipolarTriangulation_iff, M'.isBipolarTriangulation_iff]
  constructor
  · rintro ⟨hb, htri⟩
    refine ⟨e.isBipolar_map_iff.mp hb, ?_⟩
    intro F' hInt
    let F := e.drawing.faceEquiv.symm F'
    have hFace : e.drawing.faceMap F = F' :=
      e.drawing.faceEquiv.apply_symm_apply F'
    have hIntMap : M'.toPlaneGraphDrawing.IsInternal (e.drawing.faceMap F) := by
      simpa [hFace] using hInt
    have hIntSource := (e.drawing.isInternal_faceMap_iff F).mp hIntMap
    calc
      M'.toPlaneGraphDrawing.faceDegree F' =
          M'.toPlaneGraphDrawing.faceDegree (e.drawing.faceMap F) :=
        congrArg M'.toPlaneGraphDrawing.faceDegree hFace.symm
      _ = M.toPlaneGraphDrawing.faceDegree F :=
        (e.drawing.faceDegree_map F).symm
      _ = 3 := htri F hIntSource
  · rintro ⟨hb, htri⟩
    refine ⟨e.isBipolar_map_iff.mpr hb, ?_⟩
    intro F hInt
    have hIntMap : M'.toPlaneGraphDrawing.IsInternal (e.drawing.faceMap F) :=
      (e.drawing.isInternal_faceMap_iff F).mpr hInt
    calc
      M.toPlaneGraphDrawing.faceDegree F =
          M'.toPlaneGraphDrawing.faceDegree (e.drawing.faceMap F) :=
        e.drawing.faceDegree_map F
      _ = 3 := htri (e.drawing.faceMap F) hIntMap

end DirectedPlaneMap.HomeoEquiv

namespace PlaneMapWithMissing.HomeoEquiv

variable {D : PlaneMapWithMissing V E} {D' : PlaneMapWithMissing V' E'}

@[expose] noncomputable def symm (e : PlaneMapWithMissing.HomeoEquiv D D') :
    PlaneMapWithMissing.HomeoEquiv D' D where
  drawing := e.drawing.symm
  missing_map := by
    intro f
    have hf := e.missing_map (e.drawing.σE.symm f)
    rw [e.drawing.σE.apply_symm_apply] at hf
    exact hf.symm

/-- Helper toward Definitions 1.1/3.1: external faces whose closure contains
an edge correspond under a missing-edge drawing equivalence. -/
theorem externalFaceClosure_map (e : PlaneMapWithMissing.HomeoEquiv D D')
    (f : E) (F : D.toPlaneGraphDrawing.Face)
    (hF : D.toPlaneGraphDrawing.IsExternal F)
    (hcl : Set.range (D.arc f) ⊆ closure F.val) :
    ∃ F' : D'.toPlaneGraphDrawing.Face,
      D'.toPlaneGraphDrawing.IsExternal F' ∧
        Set.range (D'.arc (e.drawing.σE f)) ⊆ closure F'.val := by
  refine ⟨e.drawing.faceMap F,
    (e.drawing.isExternal_faceMap_iff F).mpr hF, ?_⟩
  rw [e.drawing.arc_range_map f, e.drawing.faceMap_val,
    ← e.drawing.h.image_closure]
  exact Set.image_mono hcl

/-- Helper toward Definitions 1.1/3.1: the edge-to-external-face closure
condition is invariant under missing-edge equivalence. -/
theorem externalFaceClosure_map_iff
    (e : PlaneMapWithMissing.HomeoEquiv D D') (f : E) :
    (∃ F : D.toPlaneGraphDrawing.Face,
      D.toPlaneGraphDrawing.IsExternal F ∧
        Set.range (D.arc f) ⊆ closure F.val) ↔
    (∃ F' : D'.toPlaneGraphDrawing.Face,
      D'.toPlaneGraphDrawing.IsExternal F' ∧
        Set.range (D'.arc (e.drawing.σE f)) ⊆ closure F'.val) := by
  constructor
  · rintro ⟨F, hF, hcl⟩
    exact e.externalFaceClosure_map f F hF hcl
  · intro h
    rcases h with ⟨F', hF', hcl'⟩
    obtain ⟨F, hF, hcl⟩ := e.symm.externalFaceClosure_map
      (e.drawing.σE f) F' hF' hcl'
    have he : e.symm.drawing.σE (e.drawing.σE f) = f :=
      e.drawing.σE.symm_apply_apply f
    rw [he] at hcl
    exact ⟨F, hF, hcl⟩

/-- Missing-edge externality data is transported in both directions. -/
theorem missing_on_external_map
    (e : PlaneMapWithMissing.HomeoEquiv D D') (f : E) :
    D.missing f →
      ∃ F' : D'.toPlaneGraphDrawing.Face,
        D'.toPlaneGraphDrawing.IsExternal F' ∧
          Set.range (D'.arc (e.drawing.σE f)) ⊆ closure F'.val := by
  intro hf
  rcases D.missing_on_external f hf with ⟨F, hF, hcl⟩
  exact e.externalFaceClosure_map f F hF hcl

/-- Helper toward Definitions 1.1/3.1: missing-edge externality is preserved
in both directions, together with the transported missing-edge tag. -/
theorem missing_on_external_map_iff
    (e : PlaneMapWithMissing.HomeoEquiv D D') (f : E) :
    (D.missing f →
      ∃ F : D.toPlaneGraphDrawing.Face,
        D.toPlaneGraphDrawing.IsExternal F ∧
          Set.range (D.arc f) ⊆ closure F.val) ↔
    (D'.missing (e.drawing.σE f) →
      ∃ F' : D'.toPlaneGraphDrawing.Face,
        D'.toPlaneGraphDrawing.IsExternal F' ∧
          Set.range (D'.arc (e.drawing.σE f)) ⊆ closure F'.val) := by
  constructor
  · intro hsrc hm'
    have hm : D.missing f := (e.missing_map f).mp hm'
    exact (e.externalFaceClosure_map_iff f).mp (hsrc hm)
  · intro htgt hm
    have hm' := (e.missing_map f).mpr hm
    exact (e.externalFaceClosure_map_iff f).mpr
      (htgt hm')

end PlaneMapWithMissing.HomeoEquiv

namespace DirectedPlaneMapWithMissing.HomeoEquiv

variable {M : DirectedPlaneMapWithMissing V E}
  {M' : DirectedPlaneMapWithMissing V' E'}

/-- Present edges correspond bijectively under a missing-edge equivalence. -/
@[expose] noncomputable def presentEdgeEquiv
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M') :
    {f : E // ¬ M.toPlaneMapWithMissing.missing f} ≃
      {f : E' // ¬ M'.toPlaneMapWithMissing.missing f} where
  toFun f := ⟨e.drawing.drawing.σE f.1, by
    intro hm
    exact f.2 ((e.drawing.missing_map f.1).mp hm)⟩
  invFun f := ⟨e.drawing.drawing.σE.symm f.1, by
    intro hm
    have hm' := (e.drawing.missing_map
      (e.drawing.drawing.σE.symm f.1)).mpr hm
    rw [e.drawing.drawing.σE.apply_symm_apply] at hm'
    exact f.2 hm'⟩
  left_inv f := by
    apply Subtype.ext
    exact e.drawing.drawing.σE.symm_apply_apply f.1
  right_inv f := by
    apply Subtype.ext
    exact e.drawing.drawing.σE.apply_symm_apply f.1

@[simp]
theorem presentEdgeEquiv_val (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (f : {f : E // ¬ M.toPlaneMapWithMissing.missing f}) :
    (e.presentEdgeEquiv f).val = e.drawing.drawing.σE f.val := rfl

/-- Present-edge tails are transported by the vertex equivalence. -/
theorem tail_map (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (f : {f : E // ¬ M.toPlaneMapWithMissing.missing f}) :
    M'.tail (e.presentEdgeEquiv f) =
      e.drawing.drawing.σV (M.tail f) := by
  have hforward : M'.forward (e.presentEdgeEquiv f) = M.forward f := by
    have he : e.presentEdgeEquiv f = ⟨e.drawing.drawing.σE f.val,
        by intro hm; exact f.property ((e.drawing.missing_map f.val).mp hm)⟩ := by
      apply Subtype.ext
      rfl
    rw [he]
    exact e.forward_map f
  by_cases hf : M.forward f
  · simp [DirectedPlaneMapWithMissing.tail, hf, hforward,
      e.drawing.drawing.src_map]
  · simp [DirectedPlaneMapWithMissing.tail, hf, hforward,
      e.drawing.drawing.tgt_map]

/-- Present-edge heads are transported by the vertex equivalence. -/
theorem head_map (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (f : {f : E // ¬ M.toPlaneMapWithMissing.missing f}) :
    M'.head (e.presentEdgeEquiv f) =
      e.drawing.drawing.σV (M.head f) := by
  have hforward : M'.forward (e.presentEdgeEquiv f) = M.forward f := by
    have he : e.presentEdgeEquiv f = ⟨e.drawing.drawing.σE f.val,
        by intro hm; exact f.property ((e.drawing.missing_map f.val).mp hm)⟩ := by
      apply Subtype.ext
      rfl
    rw [he]
    exact e.forward_map f
  by_cases hf : M.forward f
  · simp [DirectedPlaneMapWithMissing.head, hf, hforward,
      e.drawing.drawing.tgt_map]
  · simp [DirectedPlaneMapWithMissing.head, hf, hforward,
      e.drawing.drawing.src_map]

/-- Directed steps using present edges correspond under equivalence. -/
theorem step_map_iff (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (u w : V) :
    M.step u w ↔ M'.step (e.drawing.drawing.σV u) (e.drawing.drawing.σV w) := by
  rw [M.step_iff, M'.step_iff]
  constructor
  · rintro ⟨f, ht, hh⟩
    refine ⟨e.presentEdgeEquiv f, ?_, ?_⟩
    · simpa [e.tail_map] using congrArg e.drawing.drawing.σV ht
    · simpa [e.head_map] using congrArg e.drawing.drawing.σV hh
  · rintro ⟨f', ht, hh⟩
    let f := e.presentEdgeEquiv.symm f'
    have hef := e.presentEdgeEquiv.apply_symm_apply f'
    refine ⟨f, ?_, ?_⟩
    · apply e.drawing.drawing.σV.injective
      calc
        e.drawing.drawing.σV (M.tail f) = M'.tail (e.presentEdgeEquiv f) :=
          (e.tail_map f).symm
        _ = M'.tail f' := by rw [hef]
        _ = e.drawing.drawing.σV u := ht
    · apply e.drawing.drawing.σV.injective
      calc
        e.drawing.drawing.σV (M.head f) = M'.head (e.presentEdgeEquiv f) :=
          (e.head_map f).symm
        _ = M'.head f' := by rw [hef]
        _ = e.drawing.drawing.σV w := hh

/-- Acyclicity on present edges is preserved by missing-edge equivalence. -/
theorem isAcyclic_map_iff (e : DirectedPlaneMapWithMissing.HomeoEquiv M M') :
    M.IsAcyclic ↔ M'.IsAcyclic := by
  rw [M.isAcyclic_iff, M'.isAcyclic_iff]
  constructor
  · intro h v' cyc
    obtain ⟨v, rfl⟩ := e.drawing.drawing.σV.surjective v'
    have hr : M'.step ≤ fun a b => M.step
        (e.drawing.drawing.σV.symm a) (e.drawing.drawing.σV.symm b) := by
      intro a b hab
      have hs := (e.step_map_iff (e.drawing.drawing.σV.symm a)
        (e.drawing.drawing.σV.symm b)).mpr (by simpa using hab)
      simpa using hs
    have hc := cyc.lift e.drawing.drawing.σV.symm hr
    change Relation.TransGen M.step
      (e.drawing.drawing.σV.symm (e.drawing.drawing.σV v))
      (e.drawing.drawing.σV.symm (e.drawing.drawing.σV v)) at hc
    exact h v (by simpa using hc)
  · intro h v cyc
    have hr : M.step ≤ fun a b => M'.step
        (e.drawing.drawing.σV a) (e.drawing.drawing.σV b) := by
      intro a b hab
      exact (e.step_map_iff a b).mp hab
    have hc := cyc.lift e.drawing.drawing.σV hr
    exact h (e.drawing.drawing.σV v) (by simpa using hc)

end DirectedPlaneMapWithMissing.HomeoEquiv

end DirectedDistances.PlanarMap

end
