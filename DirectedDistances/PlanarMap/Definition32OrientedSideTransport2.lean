/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.Definition32OrientedSideTransport

/-! # Oriented side transport for missing edges -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

/-- A cast between paths with equal endpoints leaves the underlying function
unchanged. Helper toward Definition 3.2. -/
theorem path_coe_cast_of_eq {X : Type*} [TopologicalSpace X]
    {a b a' b' : X} (ha : a = a') (hb : b = b')
    (h : Path a b = Path a' b') (γ : Path a b) :
    ⇑(cast h γ : Path a' b') = γ := by
  subst a'
  subst b'
  cases h
  rfl

/-- Helper toward Definition 3.2: the underlying function of the oriented
arc is the stored edge path, or its reversal when the edge orientation is
opposite to the stored direction. -/
theorem orientedArc_coe (M : DirectedPlaneMapWithMissing V E)
    (e : PresentEdge M) :
    ⇑(orientedArc M e) =
      if M.forward e then
        ⇑(M.toPlaneMapWithMissing.arc e.1)
      else
        ⇑(M.toPlaneMapWithMissing.arc e.1).symm := by
  by_cases hf : M.forward e
  · simp only [orientedArc, dite_eq_left hf, eq_mpr_eq_cast, if_pos hf]
    apply path_coe_cast_of_eq
      (by simp [DirectedPlaneMapWithMissing.tail, hf])
      (by simp [DirectedPlaneMapWithMissing.head, hf])
  · simp only [orientedArc, dite_eq_right hf, eq_mpr_eq_cast, if_neg hf]
    apply path_coe_cast_of_eq
      (by simp [DirectedPlaneMapWithMissing.tail, hf])
      (by simp [DirectedPlaneMapWithMissing.head, hf])

/-- The oriented parameter correspondence intertwines the two oriented arcs.
Helper toward Definition 3.2. -/
theorem orientedArc_map_reparam
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E}
    {M' : DirectedPlaneMapWithMissing V' E'}
    (e : OrientedMissingHomeoEquiv M M') (d : PresentEdge M) :
    ∀ t, e.toHomeoEquiv.drawing.drawing.h ((orientedArc M d) t) =
      (orientedArc M' (e.toHomeoEquiv.presentEdgeMap d))
        (e.orientedEdgeReparam d t) := by
  let d' := e.toHomeoEquiv.presentEdgeMap d
  let φ := e.orientedEdgeReparam d
  have hforward : M'.forward d' = M.forward d := e.toHomeoEquiv.forward_map d
  intro t
  change e.toHomeoEquiv.drawing.drawing.h
      (⇑(orientedArc M d) t) = ⇑(orientedArc M' d') (φ t)
  rw [orientedArc_coe M d, orientedArc_coe M' d']
  by_cases hf : M.forward d
  · have hf' : M'.forward d' := by rw [hforward]; exact hf
    rw [if_pos hf, if_pos hf']
    have hφ : φ t = e.edgeReparam d.1 t := by
      simp [φ, OrientedMissingHomeoEquiv.orientedEdgeReparam, hf]
    rw [hφ]
    have hstored := e.edgeReparam_arc d.1 t
    change e.toHomeoEquiv.drawing.drawing.h
        (M.toPlaneMapWithMissing.arc d.1 t) =
      M'.toPlaneMapWithMissing.arc
        (e.toHomeoEquiv.drawing.drawing.σE d.1)
        (e.edgeReparam d.1 t) at hstored
    change e.toHomeoEquiv.drawing.drawing.h
        (M.toPlaneMapWithMissing.arc d.1 t) =
      M'.toPlaneMapWithMissing.arc
        (e.toHomeoEquiv.drawing.drawing.σE d.1)
        (e.edgeReparam d.1 t)
    exact hstored
  · have hf' : ¬ M'.forward d' := by rw [hforward]; exact hf
    rw [if_neg hf, if_neg hf']
    change e.toHomeoEquiv.drawing.drawing.h
        (M.toPlaneMapWithMissing.arc d.1 (unitInterval.symm t)) =
      M'.toPlaneMapWithMissing.arc d'.1 (unitInterval.symm (φ t))
    rw [e.edgeReparam_arc d.1 (unitInterval.symm t)]
    change M'.toPlaneMapWithMissing.arc
        (e.toHomeoEquiv.drawing.drawing.σE d.1)
        (e.edgeReparam d.1 (unitInterval.symm t)) =
      M'.toPlaneMapWithMissing.arc
        (e.toHomeoEquiv.drawing.drawing.σE d.1)
        (unitInterval.symm (φ t))
    congr 1
    have hφ : φ t = unitInterval.symm
        (e.edgeReparam d.1 (unitInterval.symm t)) := by
      simp [φ, OrientedMissingHomeoEquiv.orientedEdgeReparam, hf,
        unitInterval.symmHomeomorph]
    rw [hφ, unitInterval.symm_symm]

/-- Helper toward Definition 3.2: left-side touching is preserved by an
orientation-preserving transport of missing-edge maps with its oriented edge
parameter correspondence. -/
theorem leftAtOn_orientedArc_transport_iff
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E}
    {M' : DirectedPlaneMapWithMissing V' E'}
    (e : OrientedMissingHomeoEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M))
    (d : PresentEdge M)
    (s : {t : I // t ∈ openParams}) :
    LeftAtOn F.val (orientedArc M d) s ↔
      LeftAtOn (e.toHomeoEquiv.faceMap F).val
        (orientedArc M' (e.toHomeoEquiv.presentEdgeMap d))
          ⟨e.orientedEdgeReparam d s.1,
            (mem_openParams_homeomorph_iff (e.orientedEdgeReparam d)
              (e.orientedEdgeReparam_zero d) (e.orientedEdgeReparam_one d)
              s.1).mpr s.2⟩ := by
  let d' := e.toHomeoEquiv.presentEdgeMap d
  let φ := e.orientedEdgeReparam d
  have h0 : φ 0 = 0 := e.orientedEdgeReparam_zero d
  have h1 : φ 1 = 1 := e.orientedEdgeReparam_one d
  have hpath := orientedArc_map_reparam e d
  let s' : {t : I // t ∈ openParams} :=
    ⟨φ s.1, (mem_openParams_homeomorph_iff φ h0 h1 s.1).mpr s.2⟩
  have hs' : φ s.1 = s'.1 := rfl
  have hside := leftAtOn_map_reparam_iff F.val (orientedArc M d)
    (orientedArc M' d') s s' e.toHomeoEquiv.drawing.drawing.h
    e.orientationPreserving φ h0 h1 hpath hs'
  simpa [s', DirectedPlaneMapWithMissing.HomeoEquiv.faceMap] using hside

/-- Helper toward Definition 3.2: right-side touching is preserved by an
orientation-preserving transport of missing-edge maps with its oriented edge
parameter correspondence. -/
theorem rightAtOn_orientedArc_transport_iff
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E}
    {M' : DirectedPlaneMapWithMissing V' E'}
    (e : OrientedMissingHomeoEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M))
    (d : PresentEdge M)
    (s : {t : I // t ∈ openParams}) :
    RightAtOn F.val (orientedArc M d) s ↔
      RightAtOn (e.toHomeoEquiv.faceMap F).val
        (orientedArc M' (e.toHomeoEquiv.presentEdgeMap d))
          ⟨e.orientedEdgeReparam d s.1,
            (mem_openParams_homeomorph_iff (e.orientedEdgeReparam d)
              (e.orientedEdgeReparam_zero d) (e.orientedEdgeReparam_one d)
              s.1).mpr s.2⟩ := by
  let d' := e.toHomeoEquiv.presentEdgeMap d
  let φ := e.orientedEdgeReparam d
  have h0 : φ 0 = 0 := e.orientedEdgeReparam_zero d
  have h1 : φ 1 = 1 := e.orientedEdgeReparam_one d
  have hpath := orientedArc_map_reparam e d
  let s' : {t : I // t ∈ openParams} :=
    ⟨φ s.1, (mem_openParams_homeomorph_iff φ h0 h1 s.1).mpr s.2⟩
  have hs' : φ s.1 = s'.1 := rfl
  have hside := rightAtOn_map_reparam_iff F.val (orientedArc M d)
    (orientedArc M' d') s s' e.toHomeoEquiv.drawing.drawing.h
    e.orientationPreserving φ h0 h1 hpath hs'
  simpa [s', DirectedPlaneMapWithMissing.HomeoEquiv.faceMap] using hside

/-- Helper toward Definition 3.2: the left-side predicate on a whole present
edge is preserved by oriented transport. -/
theorem leftOf_orientedArc_transport_iff
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E}
    {M' : DirectedPlaneMapWithMissing V' E'}
    (e : OrientedMissingHomeoEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) (d : PresentEdge M) :
    LeftOf M F d ↔
      LeftOf M' (e.toHomeoEquiv.faceMap F)
        (e.toHomeoEquiv.presentEdgeMap d) := by
  change (∀ s, LeftAtOn F.val (orientedArc M d) s) ↔
    (∀ s, LeftAtOn (e.toHomeoEquiv.faceMap F).val
      (orientedArc M' (e.toHomeoEquiv.presentEdgeMap d)) s)
  let φ := e.orientedEdgeReparam d
  have h0 : φ 0 = 0 := e.orientedEdgeReparam_zero d
  have h1 : φ 1 = 1 := e.orientedEdgeReparam_one d
  have hi0 : φ.symm 0 = 0 := by apply φ.injective; simp [h0]
  have hi1 : φ.symm 1 = 1 := by apply φ.injective; simp [h1]
  constructor
  · intro h t
    let s : {t : I // t ∈ openParams} :=
      ⟨φ.symm t.1,
        (mem_openParams_homeomorph_iff φ.symm hi0 hi1 t.1).mpr t.2⟩
    have htr := (leftAtOn_orientedArc_transport_iff e F d s).mp (h s)
    have hparam : φ s.1 = t.1 := φ.apply_symm_apply t.1
    have hs' : (⟨φ s.1,
        (mem_openParams_homeomorph_iff φ h0 h1 s.1).mpr s.2⟩ :
        {t : I // t ∈ openParams}) = t := Subtype.ext hparam
    rw [hs'] at htr
    exact htr
  · intro h s
    let t : {t : I // t ∈ openParams} :=
      ⟨φ s.1, (mem_openParams_homeomorph_iff φ h0 h1 s.1).mpr s.2⟩
    exact (leftAtOn_orientedArc_transport_iff e F d s).mpr (h t)

/-- Helper toward Definition 3.2: the right-side predicate on a whole
present edge is preserved by oriented transport. -/
theorem rightOf_orientedArc_transport_iff
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E}
    {M' : DirectedPlaneMapWithMissing V' E'}
    (e : OrientedMissingHomeoEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) (d : PresentEdge M) :
    RightOf M F d ↔
      RightOf M' (e.toHomeoEquiv.faceMap F)
        (e.toHomeoEquiv.presentEdgeMap d) := by
  change (∀ s, RightAtOn F.val (orientedArc M d) s) ↔
    (∀ s, RightAtOn (e.toHomeoEquiv.faceMap F).val
      (orientedArc M' (e.toHomeoEquiv.presentEdgeMap d)) s)
  let φ := e.orientedEdgeReparam d
  have h0 : φ 0 = 0 := e.orientedEdgeReparam_zero d
  have h1 : φ 1 = 1 := e.orientedEdgeReparam_one d
  have hi0 : φ.symm 0 = 0 := by apply φ.injective; simp [h0]
  have hi1 : φ.symm 1 = 1 := by apply φ.injective; simp [h1]
  constructor
  · intro h t
    let s : {t : I // t ∈ openParams} :=
      ⟨φ.symm t.1,
        (mem_openParams_homeomorph_iff φ.symm hi0 hi1 t.1).mpr t.2⟩
    have htr := (rightAtOn_orientedArc_transport_iff e F d s).mp (h s)
    have hparam : φ s.1 = t.1 := φ.apply_symm_apply t.1
    have hs' : (⟨φ s.1,
        (mem_openParams_homeomorph_iff φ h0 h1 s.1).mpr s.2⟩ :
        {t : I // t ∈ openParams}) = t := Subtype.ext hparam
    rw [hs'] at htr
    exact htr
  · intro h s
    let t : {t : I // t ∈ openParams} :=
      ⟨φ s.1, (mem_openParams_homeomorph_iff φ h0 h1 s.1).mpr s.2⟩
    exact (rightAtOn_orientedArc_transport_iff e F d s).mpr (h t)

/-- Helper toward Definition 3.2: upper-left present-edge membership is
preserved by oriented transport. -/
theorem mem_UL_oriented_transport_iff
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E}
    {M' : DirectedPlaneMapWithMissing V' E'}
    (e : OrientedMissingHomeoEquiv M M') (d : PresentEdge M) :
    d ∈ UL M ↔ e.toHomeoEquiv.presentEdgeMap d ∈ UL M' := by
  change (∃ F : PlaneGraphDrawing.Face (Drawing M),
      (Drawing M).IsExternal F ∧ LeftOf M F d) ↔
    (∃ F' : PlaneGraphDrawing.Face (Drawing M'),
      (Drawing M').IsExternal F' ∧
        LeftOf M' F' (e.toHomeoEquiv.presentEdgeMap d))
  constructor
  · rintro ⟨F, hExt, hLeft⟩
    refine ⟨e.toHomeoEquiv.faceMap F, ?_, ?_⟩
    · exact (e.toHomeoEquiv.isExternal_faceMap_iff F).mpr hExt
    · exact (leftOf_orientedArc_transport_iff e F d).mp hLeft
  · rintro ⟨F', hExt, hLeft⟩
    let f := e.toHomeoEquiv.drawing.drawing.faceEquiv
    let F := f.symm F'
    have hF : e.toHomeoEquiv.faceMap F = F' := by
      have hF0 := f.apply_symm_apply F'
      change e.toHomeoEquiv.faceMap F = F' at hF0
      exact hF0
    have hExtMap : (Drawing M').IsExternal (e.toHomeoEquiv.faceMap F) := by
      simpa only [hF] using hExt
    have hLeftMap : LeftOf M' (e.toHomeoEquiv.faceMap F)
        (e.toHomeoEquiv.presentEdgeMap d) := by
      simpa only [hF] using hLeft
    exact ⟨F, (e.toHomeoEquiv.isExternal_faceMap_iff F).mp hExtMap,
      (leftOf_orientedArc_transport_iff e F d).mpr hLeftMap⟩

/-- Helper toward Definition 3.2: lower-right present-edge membership is
preserved by oriented transport. -/
theorem mem_LR_oriented_transport_iff
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E}
    {M' : DirectedPlaneMapWithMissing V' E'}
    (e : OrientedMissingHomeoEquiv M M') (d : PresentEdge M) :
    d ∈ LR M ↔ e.toHomeoEquiv.presentEdgeMap d ∈ LR M' := by
  change (∃ F : PlaneGraphDrawing.Face (Drawing M),
      (Drawing M).IsExternal F ∧ RightOf M F d) ↔
    (∃ F' : PlaneGraphDrawing.Face (Drawing M'),
      (Drawing M').IsExternal F' ∧
        RightOf M' F' (e.toHomeoEquiv.presentEdgeMap d))
  constructor
  · rintro ⟨F, hExt, hRight⟩
    refine ⟨e.toHomeoEquiv.faceMap F, ?_, ?_⟩
    · exact (e.toHomeoEquiv.isExternal_faceMap_iff F).mpr hExt
    · exact (rightOf_orientedArc_transport_iff e F d).mp hRight
  · rintro ⟨F', hExt, hRight⟩
    let f := e.toHomeoEquiv.drawing.drawing.faceEquiv
    let F := f.symm F'
    have hF : e.toHomeoEquiv.faceMap F = F' := by
      have hF0 := f.apply_symm_apply F'
      change e.toHomeoEquiv.faceMap F = F' at hF0
      exact hF0
    have hExtMap : (Drawing M').IsExternal (e.toHomeoEquiv.faceMap F) := by
      simpa only [hF] using hExt
    have hRightMap : RightOf M' (e.toHomeoEquiv.faceMap F)
        (e.toHomeoEquiv.presentEdgeMap d) := by
      simpa only [hF] using hRight
    exact ⟨F, (e.toHomeoEquiv.isExternal_faceMap_iff F).mp hExtMap,
      (rightOf_orientedArc_transport_iff e F d).mpr hRightMap⟩

end DirectedDistances.PlanarMap

end
