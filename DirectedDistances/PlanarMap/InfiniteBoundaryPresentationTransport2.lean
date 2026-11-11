/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.InfiniteBoundaryPresentationTransport

/-! # Further transport for infinite boundary presentations -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

universe uV uE uV' uE' uUL uUR uLR uLL uI

variable {V : Type uV} {E : Type uE}
variable {V' : Type uV'} {E' : Type uE'}
variable {M : DirectedPlaneMapWithMissing V E}
variable {M' : DirectedPlaneMapWithMissing V' E'}

namespace InfiniteBoundaryMapEquiv

private theorem arcParam_strictMono (e : InfiniteBoundaryMapEquiv M M')
    (d : PresentEdge M) : StrictMono (e.arcParam d) :=
  (e.arcParam d).continuous.strictMono_of_inj_boundedOrder
    (by
      change (e.arcParam d) 0 ≤ (e.arcParam d) 1
      rw [e.arcParam_zero, e.arcParam_one]
      exact zero_le_one)
    (e.arcParam d).injective

private theorem arcParam_mem_openParams
    (e : InfiniteBoundaryMapEquiv M M') (d : PresentEdge M)
    {t : unitInterval} (ht : t ∈ openParams) :
    e.arcParam d t ∈ openParams := by
  have hm := arcParam_strictMono e d
  change 0 < t ∧ t < 1 at ht
  change 0 < e.arcParam d t ∧ e.arcParam d t < 1
  constructor
  · simpa [e.arcParam_zero] using hm ht.1
  · simpa [e.arcParam_one] using hm ht.2

private theorem arcParam_symm_zero (e : InfiniteBoundaryMapEquiv M M')
    (d : PresentEdge M) : (e.arcParam d).symm 0 = 0 := by
  apply (e.arcParam d).injective
  simp [e.arcParam_zero]

private theorem arcParam_symm_one (e : InfiniteBoundaryMapEquiv M M')
    (d : PresentEdge M) : (e.arcParam d).symm 1 = 1 := by
  apply (e.arcParam d).injective
  simp [e.arcParam_one]

private theorem arcParam_symm_strictMono
    (e : InfiniteBoundaryMapEquiv M M') (d : PresentEdge M) :
    StrictMono (e.arcParam d).symm := by
  exact (e.arcParam d).symm.continuous.strictMono_of_inj_boundedOrder
    (by
      change (e.arcParam d).symm 0 ≤ (e.arcParam d).symm 1
      rw [arcParam_symm_zero, arcParam_symm_one]
      exact zero_le_one)
    (e.arcParam d).symm.injective

private theorem arcParam_symm_mem_openParams
    (e : InfiniteBoundaryMapEquiv M M') (d : PresentEdge M)
    {t : unitInterval} (ht : t ∈ openParams) :
    (e.arcParam d).symm t ∈ openParams := by
  have hm := arcParam_symm_strictMono e d
  change 0 < (e.arcParam d).symm t ∧ (e.arcParam d).symm t < 1
  change 0 < t ∧ t < 1 at ht
  constructor
  · simpa [arcParam_symm_zero] using hm ht.1
  · simpa [arcParam_symm_one] using hm ht.2

private theorem leftAtOn_map_reparam_iff
    (e : InfiniteBoundaryMapEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) (d : PresentEdge M)
    (s : {t : unitInterval // t ∈ openParams}) :
    LeftAtOn ((e.map.drawing.drawing.h) '' F.1)
        (orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using d.2⟩) s ↔
      LeftAtOn F.1 (orientedArc M d)
        ⟨(e.arcParam d).symm s.1,
          arcParam_symm_mem_openParams e d s.2⟩ := by
  let φ := e.arcParam d
  let h₀ := arcParam_symm_zero e d
  let h₁ := arcParam_symm_one e d
  let s₀ : {t : unitInterval // t ∈ openParams} :=
    ⟨φ.symm s.1, arcParam_symm_mem_openParams e d s.2⟩
  let δ := (orientedArc M d).map e.map.drawing.drawing.h.continuous
  let γ := δ.reparam φ.symm φ.symm.continuous h₀ h₁
  have hcurve : ∀ t : unitInterval,
      orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩ t = γ t := by
    intro t
    have h := e.orientedArc_map d (φ.symm t)
    change orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩
        (φ (φ.symm t)) =
      e.map.drawing.drawing.h (orientedArc M d (φ.symm t)) at h
    rw [φ.apply_symm_apply] at h
    change orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩ t =
      e.map.drawing.drawing.h (orientedArc M d (φ.symm t))
    exact h
  have hcongr := leftAtOn_congr_fun
    ((e.map.drawing.drawing.h) '' F.1)
    (orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
      by simpa [e.map.drawing.missing_map] using d.2⟩)
    γ s hcurve
  exact hcongr.trans
    ((leftAtOn_reparam_iff _ _ φ.symm h₀ h₁ s s₀ rfl).trans
      (leftAtOn_map_iff F.1 (orientedArc M d) s₀
        e.map.drawing.drawing.h e.orientationPreserving).symm)

private theorem rightAtOn_map_reparam_iff
    (e : InfiniteBoundaryMapEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) (d : PresentEdge M)
    (s : {t : unitInterval // t ∈ openParams}) :
    RightAtOn ((e.map.drawing.drawing.h) '' F.1)
        (orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using d.2⟩) s ↔
      RightAtOn F.1 (orientedArc M d)
        ⟨(e.arcParam d).symm s.1,
          arcParam_symm_mem_openParams e d s.2⟩ := by
  let φ := e.arcParam d
  let h₀ := arcParam_symm_zero e d
  let h₁ := arcParam_symm_one e d
  let s₀ : {t : unitInterval // t ∈ openParams} :=
    ⟨φ.symm s.1, arcParam_symm_mem_openParams e d s.2⟩
  let δ := (orientedArc M d).map e.map.drawing.drawing.h.continuous
  let γ := δ.reparam φ.symm φ.symm.continuous h₀ h₁
  have hcurve : ∀ t : unitInterval,
      orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩ t = γ t := by
    intro t
    have h := e.orientedArc_map d (φ.symm t)
    change orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩
        (φ (φ.symm t)) =
      e.map.drawing.drawing.h (orientedArc M d (φ.symm t)) at h
    rw [φ.apply_symm_apply] at h
    change orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩ t =
      e.map.drawing.drawing.h (orientedArc M d (φ.symm t))
    exact h
  have hcongr := rightAtOn_congr_fun
    ((e.map.drawing.drawing.h) '' F.1)
    (orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
      by simpa [e.map.drawing.missing_map] using d.2⟩)
    γ s hcurve
  exact hcongr.trans
    ((rightAtOn_reparam_iff _ _ φ.symm h₀ h₁ s s₀ rfl).trans
      (rightAtOn_map_iff F.1 (orientedArc M d) s₀
        e.map.drawing.drawing.h e.orientationPreserving).symm)

private def dartIndexEquiv (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) :
    InfiniteBoundaryDartIndex P ≃
      InfiniteBoundaryDartIndex (e.pushforward P) where
  toFun
    | .upperLeft i => .upperLeft i
    | .upperRight i => .upperRight i
    | .lowerRight i => .lowerRight i
    | .lowerLeft i => .lowerLeft i
  invFun
    | .upperLeft i => .upperLeft i
    | .upperRight i => .upperRight i
    | .lowerRight i => .lowerRight i
    | .lowerLeft i => .lowerLeft i
  left_inv := by intro i; cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

private theorem dartIndexEquiv_upperLeft
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : P.upperLeft.Index) :
    dartIndexEquiv e P (.upperLeft i) = .upperLeft i := rfl

private theorem dartIndexEquiv_upperRight
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : P.upperRight.Index) :
    dartIndexEquiv e P (.upperRight i) = .upperRight i := rfl

private theorem dartIndexEquiv_lowerRight
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : P.lowerRight.Index) :
    dartIndexEquiv e P (.lowerRight i) = .lowerRight i := rfl

private theorem dartIndexEquiv_lowerLeft
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : P.lowerLeft.Index) :
    dartIndexEquiv e P (.lowerLeft i) = .lowerLeft i := rfl

private theorem dartIndexEquiv_dart
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : InfiniteBoundaryDartIndex P) :
    InfiniteBoundaryDartIndex.dart (e.pushforward P)
        (dartIndexEquiv e P i) =
      e.mapDart (InfiniteBoundaryDartIndex.dart P i) := by
  cases i with
  | upperLeft j =>
      rw [dartIndexEquiv_upperLeft]
      simp only [InfiniteBoundaryDartIndex.dart_eq, pushforward]
      exact mapDarts_apply e P.upperLeft.darts j
  | upperRight j =>
      rw [dartIndexEquiv_upperRight]
      simp only [InfiniteBoundaryDartIndex.dart_eq, pushforward]
      exact mapDarts_apply e P.upperRight.darts j
  | lowerRight j =>
      rw [dartIndexEquiv_lowerRight]
      simp only [InfiniteBoundaryDartIndex.dart_eq, pushforward]
      exact mapDarts_apply e P.lowerRight.darts j
  | lowerLeft j =>
      rw [dartIndexEquiv_lowerLeft]
      simp only [InfiniteBoundaryDartIndex.dart_eq, pushforward]
      exact mapDarts_apply e P.lowerLeft.darts j

private theorem dartIndexEquiv_edge
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (i : InfiniteBoundaryDartIndex P) :
    (InfiniteBoundaryDartIndex.dart (e.pushforward P)
      (dartIndexEquiv e P i)).1 =
      e.map.drawing.drawing.σE
        (InfiniteBoundaryDartIndex.dart P i).1 := by
  rw [dartIndexEquiv_dart]
  rfl

private theorem listedEdge_pushforward_iff
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (a : E) :
    (∃ i : InfiniteBoundaryDartIndex P,
      (InfiniteBoundaryDartIndex.dart P i).1 = a) ↔
    (∃ j : InfiniteBoundaryDartIndex (e.pushforward P),
      (InfiniteBoundaryDartIndex.dart (e.pushforward P) j).1 =
        e.map.drawing.drawing.σE a) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨dartIndexEquiv e P i, ?_⟩
    rw [dartIndexEquiv_edge]
    exact congrArg e.map.drawing.drawing.σE hi
  · rintro ⟨j, hj⟩
    let i := (dartIndexEquiv e P).symm j
    have hidx : dartIndexEquiv e P i = j := by simp [i]
    refine ⟨i, ?_⟩
    have he := dartIndexEquiv_edge e P i
    rw [hidx] at he
    apply e.map.drawing.drawing.σE.injective
    calc
      e.map.drawing.drawing.σE (InfiniteBoundaryDartIndex.dart P i).1 =
          (InfiniteBoundaryDartIndex.dart (e.pushforward P) j).1 := he.symm
      _ = e.map.drawing.drawing.σE a := hj

/-- Helper toward Definition 3.2: external-frontier edges are invariant
under an orientation-preserving map equivalence. -/
theorem externalFrontierEdge_map_iff (e : InfiniteBoundaryMapEquiv M M')
    (a : E) :
    ExternalFrontierEdge M' (e.map.drawing.drawing.σE a) ↔
      ExternalFrontierEdge M a := by
  rw [externalFrontierEdge_iff, externalFrontierEdge_iff]
  constructor
  · rintro ⟨F', hF', hsub'⟩
    let F := e.map.drawing.drawing.faceEquiv.symm F'
    have hface : e.map.drawing.drawing.faceMap F = F' := by
      exact e.map.drawing.drawing.faceEquiv.apply_symm_apply F'
    refine ⟨F, ?_, ?_⟩
    · exact (e.map.drawing.drawing.isExternal_faceMap_iff F).mp
        (hface ▸ hF')
    · intro z hz
      have hz' : e.map.drawing.drawing.h z ∈
          Set.range (M'.toPlaneMapWithMissing.arc
            (e.map.drawing.drawing.σE a)) := by
        rw [e.map.drawing.drawing.arc_range_map]
        exact ⟨z, hz, rfl⟩
      have hmem := hsub' hz'
      rw [← hface, e.map.drawing.drawing.faceMap_val,
        ← e.map.drawing.drawing.h.image_frontier] at hmem
      rcases hmem with ⟨w, hw, hzw⟩
      exact e.map.drawing.drawing.h.injective hzw ▸ hw
  · rintro ⟨F, hF, hsub⟩
    refine ⟨e.map.drawing.drawing.faceMap F,
      (e.map.drawing.drawing.isExternal_faceMap_iff F).mpr hF, ?_⟩
    intro z hz
    rw [e.map.drawing.drawing.arc_range_map] at hz
    rcases hz with ⟨w, hw, hzw⟩
    rw [e.map.drawing.drawing.faceMap_val,
      ← e.map.drawing.drawing.h.image_frontier]
    exact ⟨w, hsub hw, hzw⟩

/-- Helper toward Definition 3.2: left-side incidence transports for a
present dart under the orientation-preserving map equivalence. -/
theorem LeftOf_map_iff (e : InfiniteBoundaryMapEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) (d : PresentEdge M) :
    LeftOf M' (e.map.drawing.drawing.faceMap F)
        ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using d.2⟩ ↔
      LeftOf M F d := by
  change (∀ s, LeftAtOn ((e.map.drawing.drawing.h) '' F.1)
      (orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩) s) ↔
    (∀ s, LeftAtOn F.1 (orientedArc M d) s)
  constructor
  · intro hs s
    let s₁ : {t : unitInterval // t ∈ openParams} :=
      ⟨e.arcParam d s.1, arcParam_mem_openParams e d s.2⟩
    simpa [s₁, (e.arcParam d).symm_apply_apply] using
      (leftAtOn_map_reparam_iff e F d s₁).mp (hs s₁)
  · intro hs s
    let s₀ : {t : unitInterval // t ∈ openParams} :=
      ⟨(e.arcParam d).symm s.1,
        arcParam_symm_mem_openParams e d s.2⟩
    exact (leftAtOn_map_reparam_iff e F d s).mpr (hs s₀)

/-- Helper toward Definition 3.2: right-side incidence transports for a
present dart under the orientation-preserving map equivalence. -/
theorem RightOf_map_iff (e : InfiniteBoundaryMapEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) (d : PresentEdge M) :
    RightOf M' (e.map.drawing.drawing.faceMap F)
        ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using d.2⟩ ↔
      RightOf M F d := by
  change (∀ s, RightAtOn ((e.map.drawing.drawing.h) '' F.1)
      (orientedArc M' ⟨e.map.drawing.drawing.σE d.1,
        by simpa [e.map.drawing.missing_map] using d.2⟩) s) ↔
    (∀ s, RightAtOn F.1 (orientedArc M d) s)
  constructor
  · intro hs s
    let s₁ : {t : unitInterval // t ∈ openParams} :=
      ⟨e.arcParam d s.1, arcParam_mem_openParams e d s.2⟩
    simpa [s₁, (e.arcParam d).symm_apply_apply] using
      (rightAtOn_map_reparam_iff e F d s₁).mp (hs s₁)
  · intro hs s
    let s₀ : {t : unitInterval // t ∈ openParams} :=
      ⟨(e.arcParam d).symm s.1,
        arcParam_symm_mem_openParams e d s.2⟩
    exact (rightAtOn_map_reparam_iff e F d s).mpr (hs s₀)

/-- Helper toward Definition 3.2: the upper-left presentation predicate is
preserved in both directions by pushforward. -/
theorem ULOkInf_pushforward_iff (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) :
    ULOkInf (e.pushforward P) ↔ ULOkInf P := by
  rw [ULOkInf_iff, ULOkInf_iff]
  simp only [pushforward]
  constructor
  · rintro ⟨hs, hj⟩
    constructor
    · intro i
      let d := P.upperLeft.darts i
      obtain ⟨hp', hdir', F', hF', hside'⟩ := hs i
      have hpmapped0 := hp'
      change ¬ M'.toPlaneMapWithMissing.missing
        (e.mapDart (P.upperLeft.darts i)).1 at hpmapped0
      change ¬ M'.toPlaneMapWithMissing.missing
          (e.map.drawing.drawing.σE (P.upperLeft.darts i).1) at hpmapped0
      have hpmapped : ¬ M'.toPlaneMapWithMissing.missing
          (e.map.drawing.drawing.σE d.1) := by simpa [d] using hpmapped0
      have hp : ¬ M.toPlaneMapWithMissing.missing d.1 :=
        (e.map.drawing.missing_map d.1).not.mp hpmapped
      refine ⟨hp, ?_, ?_⟩
      · change d.2 = M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩ at hdir'
        have hf := e.map.forward_map ⟨d.1, hp⟩
        change M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩ =
            M.forward ⟨d.1, hp⟩ at hf
        rw [hf] at hdir'
        exact hdir'
      · let F := e.map.drawing.drawing.faceEquiv.symm F'
        have hface : e.map.drawing.drawing.faceMap F = F' :=
          e.map.drawing.drawing.faceEquiv.apply_symm_apply F'
        refine ⟨F,
          (e.map.drawing.drawing.isExternal_faceMap_iff F).mp
            (hface ▸ hF'), ?_⟩
        have hside : LeftOf M'
            (e.map.drawing.drawing.faceMap F)
            ⟨e.map.drawing.drawing.σE d.1,
              by simpa [e.map.drawing.missing_map] using hp⟩ := by
          rw [hface]
          exact hside'
        exact (LeftOf_map_iff e F ⟨d.1, hp⟩).mp hside
    · intro i j hn
      have h := hj i j hn
      change boundaryDartTerminal M'
          (e.mapDart (P.upperLeft.darts i)) =
        boundaryDartInitial M'
          (e.mapDart (P.upperLeft.darts j)) at h
      have h' : e.mapVertexEquiv
          (boundaryDartTerminal M (P.upperLeft.darts i)) =
          e.mapVertexEquiv
            (boundaryDartInitial M (P.upperLeft.darts j)) := by
        simpa only [boundaryDartTerminal_map,
          boundaryDartInitial_map] using h
      exact e.mapVertexEquiv.injective h'
  · rintro ⟨hs, hj⟩
    constructor
    · intro i
      let d := P.upperLeft.darts i
      obtain ⟨hp, hdir, F, hF, hside⟩ := hs i
      have hpsource : ¬ M.toPlaneMapWithMissing.missing d.1 := by
        simpa [d] using hp
      have hp' : ¬ M'.toPlaneMapWithMissing.missing
          (e.map.drawing.drawing.σE d.1) :=
        (e.map.drawing.missing_map d.1).not.mpr hpsource
      refine ⟨hp', ?_, ?_⟩
      · have hf := e.map.forward_map ⟨d.1, hpsource⟩
        change M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩ =
            M.forward ⟨d.1, hpsource⟩ at hf
        change d.2 = M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩
        rw [hf]
        exact hdir
      · refine ⟨e.map.drawing.drawing.faceMap F,
          (e.map.drawing.drawing.isExternal_faceMap_iff F).mpr hF, ?_⟩
        exact (LeftOf_map_iff e F ⟨d.1, hpsource⟩).mpr hside
    · intro i j hn
      have h := congrArg e.mapVertexEquiv (hj i j hn)
      change boundaryDartTerminal M'
          (e.mapDart (P.upperLeft.darts i)) =
        boundaryDartInitial M'
          (e.mapDart (P.upperLeft.darts j))
      simpa only [boundaryDartTerminal_map,
        boundaryDartInitial_map] using h

/-- Helper toward Definition 3.2: the lower-right presentation predicate is
preserved in both directions by pushforward. -/
theorem LROkInf_pushforward_iff (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) :
    LROkInf (e.pushforward P) ↔ LROkInf P := by
  rw [LROkInf_iff, LROkInf_iff]
  simp only [pushforward]
  constructor
  · rintro ⟨hs, hj⟩
    constructor
    · intro i
      let d := P.lowerRight.darts i
      obtain ⟨hp', hdir', F', hF', hside'⟩ := hs i
      have hpmapped0 := hp'
      change ¬ M'.toPlaneMapWithMissing.missing
        (e.mapDart (P.lowerRight.darts i)).1 at hpmapped0
      change ¬ M'.toPlaneMapWithMissing.missing
          (e.map.drawing.drawing.σE (P.lowerRight.darts i).1) at hpmapped0
      have hpmapped : ¬ M'.toPlaneMapWithMissing.missing
          (e.map.drawing.drawing.σE d.1) := by simpa [d] using hpmapped0
      have hp : ¬ M.toPlaneMapWithMissing.missing d.1 :=
        (e.map.drawing.missing_map d.1).not.mp hpmapped
      refine ⟨hp, ?_, ?_⟩
      · change d.2 = !(M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩) at hdir'
        have hf := e.map.forward_map ⟨d.1, hp⟩
        change M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩ =
            M.forward ⟨d.1, hp⟩ at hf
        rw [hf] at hdir'
        exact hdir'
      · let F := e.map.drawing.drawing.faceEquiv.symm F'
        have hface : e.map.drawing.drawing.faceMap F = F' :=
          e.map.drawing.drawing.faceEquiv.apply_symm_apply F'
        refine ⟨F,
          (e.map.drawing.drawing.isExternal_faceMap_iff F).mp
            (hface ▸ hF'), ?_⟩
        have hside : RightOf M'
            (e.map.drawing.drawing.faceMap F)
            ⟨e.map.drawing.drawing.σE d.1,
              by simpa [e.map.drawing.missing_map] using hp⟩ := by
          rw [hface]
          exact hside'
        exact (RightOf_map_iff e F ⟨d.1, hp⟩).mp hside
    · intro i j hn
      have h := hj i j hn
      change boundaryDartTerminal M'
          (e.mapDart (P.lowerRight.darts i)) =
        boundaryDartInitial M'
          (e.mapDart (P.lowerRight.darts j)) at h
      have h' : e.mapVertexEquiv
          (boundaryDartTerminal M (P.lowerRight.darts i)) =
          e.mapVertexEquiv
            (boundaryDartInitial M (P.lowerRight.darts j)) := by
        simpa only [boundaryDartTerminal_map,
          boundaryDartInitial_map] using h
      exact e.mapVertexEquiv.injective h'
  · rintro ⟨hs, hj⟩
    constructor
    · intro i
      let d := P.lowerRight.darts i
      obtain ⟨hp, hdir, F, hF, hside⟩ := hs i
      have hpsource : ¬ M.toPlaneMapWithMissing.missing d.1 := by
        simpa [d] using hp
      have hp' : ¬ M'.toPlaneMapWithMissing.missing
          (e.map.drawing.drawing.σE d.1) :=
        (e.map.drawing.missing_map d.1).not.mpr hpsource
      refine ⟨hp', ?_, ?_⟩
      · have hf := e.map.forward_map ⟨d.1, hpsource⟩
        change M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩ =
            M.forward ⟨d.1, hpsource⟩ at hf
        change d.2 = !(M'.forward ⟨e.map.drawing.drawing.σE d.1,
          by simpa [e.map.drawing.missing_map] using hp⟩)
        rw [hf]
        exact hdir
      · refine ⟨e.map.drawing.drawing.faceMap F,
          (e.map.drawing.drawing.isExternal_faceMap_iff F).mpr hF, ?_⟩
        exact (RightOf_map_iff e F ⟨d.1, hpsource⟩).mpr hside
    · intro i j hn
      have h := congrArg e.mapVertexEquiv (hj i j hn)
      change boundaryDartTerminal M'
          (e.mapDart (P.lowerRight.darts i)) =
        boundaryDartInitial M'
          (e.mapDart (P.lowerRight.darts j))
      simpa only [boundaryDartTerminal_map,
        boundaryDartInitial_map] using h

/-- Helper toward Definition 3.2: the set and multiplicity clauses of the
infinite boundary-order predicate are invariant under pushforward. -/
theorem IsBoundaryOrderOfInf_pushforward_iff
    (e : InfiniteBoundaryMapEquiv M M')
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) :
    IsBoundaryOrderOfInf M' (e.pushforward P) ↔ IsBoundaryOrderOfInf M P := by
  rw [IsBoundaryOrderOfInf_iff, IsBoundaryOrderOfInf_iff]
  constructor
  · rintro ⟨hcover', htriple', hpairs'⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact (listedEdge_pushforward_iff e P a).trans
        ((hcover' (e.map.drawing.drawing.σE a)).trans
          (externalFrontierEdge_map_iff e a))
    · intro a i j k hi hj hk
      have hi' : (InfiniteBoundaryDartIndex.dart (e.pushforward P)
          (dartIndexEquiv e P i)).1 = e.map.drawing.drawing.σE a := by
        rw [dartIndexEquiv_edge]
        exact congrArg e.map.drawing.drawing.σE hi
      have hj' : (InfiniteBoundaryDartIndex.dart (e.pushforward P)
          (dartIndexEquiv e P j)).1 = e.map.drawing.drawing.σE a := by
        rw [dartIndexEquiv_edge]
        exact congrArg e.map.drawing.drawing.σE hj
      have hk' : (InfiniteBoundaryDartIndex.dart (e.pushforward P)
          (dartIndexEquiv e P k)).1 = e.map.drawing.drawing.σE a := by
        rw [dartIndexEquiv_edge]
        exact congrArg e.map.drawing.drawing.σE hk
      rcases htriple' (e.map.drawing.drawing.σE a)
          (dartIndexEquiv e P i) (dartIndexEquiv e P j)
          (dartIndexEquiv e P k) hi' hj' hk' with h | h | h
      · exact Or.inl ((dartIndexEquiv e P).injective h)
      · exact Or.inr (Or.inl ((dartIndexEquiv e P).injective h))
      · exact Or.inr (Or.inr ((dartIndexEquiv e P).injective h))
    · intro a i j hij hi hj
      have hi' : (InfiniteBoundaryDartIndex.dart (e.pushforward P)
          (dartIndexEquiv e P i)).1 = e.map.drawing.drawing.σE a := by
        rw [dartIndexEquiv_edge]
        exact congrArg e.map.drawing.drawing.σE hi
      have hj' : (InfiniteBoundaryDartIndex.dart (e.pushforward P)
          (dartIndexEquiv e P j)).1 = e.map.drawing.drawing.σE a := by
        rw [dartIndexEquiv_edge]
        exact congrArg e.map.drawing.drawing.σE hj
      have hij' : dartIndexEquiv e P i ≠ dartIndexEquiv e P j := by
        intro h
        exact hij ((dartIndexEquiv e P).injective h)
      obtain ⟨hp', F', G', hF', hG', hleft', hright'⟩ :=
        hpairs' (e.map.drawing.drawing.σE a)
          (dartIndexEquiv e P i) (dartIndexEquiv e P j) hij' hi' hj'
      have hp : ¬ M.toPlaneMapWithMissing.missing a :=
        (e.map.drawing.missing_map a).not.mp hp'
      let F := e.map.drawing.drawing.faceEquiv.symm F'
      let G := e.map.drawing.drawing.faceEquiv.symm G'
      have hfaceF : e.map.drawing.drawing.faceMap F = F' :=
        e.map.drawing.drawing.faceEquiv.apply_symm_apply F'
      have hfaceG : e.map.drawing.drawing.faceMap G = G' :=
        e.map.drawing.drawing.faceEquiv.apply_symm_apply G'
      refine ⟨hp, F, G,
        (e.map.drawing.drawing.isExternal_faceMap_iff F).mp
          (hfaceF ▸ hF'),
        (e.map.drawing.drawing.isExternal_faceMap_iff G).mp
          (hfaceG ▸ hG'), ?_, ?_⟩
      · have hside : LeftOf M'
            (e.map.drawing.drawing.faceMap F)
            ⟨e.map.drawing.drawing.σE a,
              by simpa [e.map.drawing.missing_map] using hp⟩ := by
          rw [hfaceF]
          exact hleft'
        exact (LeftOf_map_iff e F ⟨a, hp⟩).mp hside
      · have hside : RightOf M'
            (e.map.drawing.drawing.faceMap G)
            ⟨e.map.drawing.drawing.σE a,
              by simpa [e.map.drawing.missing_map] using hp⟩ := by
          rw [hfaceG]
          exact hright'
        exact (RightOf_map_iff e G ⟨a, hp⟩).mp hside
  · rintro ⟨hcover, htriple, hpairs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro b
      let a := e.map.drawing.drawing.σE.symm b
      have hab : e.map.drawing.drawing.σE a = b := by simp [a]
      have hc := (listedEdge_pushforward_iff e P a).symm.trans (hcover a)
      have hext := (externalFrontierEdge_map_iff e a).symm
      simpa [hab] using hc.trans hext
    · intro b i' j' k' hi' hj' hk'
      let a := e.map.drawing.drawing.σE.symm b
      have hab : e.map.drawing.drawing.σE a = b := by simp [a]
      let i := (dartIndexEquiv e P).symm i'
      let j := (dartIndexEquiv e P).symm j'
      let k := (dartIndexEquiv e P).symm k'
      have hidxi : dartIndexEquiv e P i = i' := by simp [i]
      have hidxj : dartIndexEquiv e P j = j' := by simp [j]
      have hidxk : dartIndexEquiv e P k = k' := by simp [k]
      have hi : (InfiniteBoundaryDartIndex.dart P i).1 = a := by
        apply e.map.drawing.drawing.σE.injective
        calc
          e.map.drawing.drawing.σE (InfiniteBoundaryDartIndex.dart P i).1 =
              (InfiniteBoundaryDartIndex.dart (e.pushforward P) i').1 := by
            rw [← hidxi]
            exact (dartIndexEquiv_edge e P i).symm
          _ = b := hi'
          _ = e.map.drawing.drawing.σE a := hab.symm
      have hj : (InfiniteBoundaryDartIndex.dart P j).1 = a := by
        apply e.map.drawing.drawing.σE.injective
        calc
          e.map.drawing.drawing.σE (InfiniteBoundaryDartIndex.dart P j).1 =
              (InfiniteBoundaryDartIndex.dart (e.pushforward P) j').1 := by
            rw [← hidxj]
            exact (dartIndexEquiv_edge e P j).symm
          _ = b := hj'
          _ = e.map.drawing.drawing.σE a := hab.symm
      have hk : (InfiniteBoundaryDartIndex.dart P k).1 = a := by
        apply e.map.drawing.drawing.σE.injective
        calc
          e.map.drawing.drawing.σE (InfiniteBoundaryDartIndex.dart P k).1 =
              (InfiniteBoundaryDartIndex.dart (e.pushforward P) k').1 := by
            rw [← hidxk]
            exact (dartIndexEquiv_edge e P k).symm
          _ = b := hk'
          _ = e.map.drawing.drawing.σE a := hab.symm
      rcases htriple a i j k hi hj hk with h | h | h
      · exact Or.inl (calc
          i' = dartIndexEquiv e P i := hidxi.symm
          _ = dartIndexEquiv e P j := congrArg (dartIndexEquiv e P) h
          _ = j' := hidxj)
      · exact Or.inr (Or.inl (calc
          i' = dartIndexEquiv e P i := hidxi.symm
          _ = dartIndexEquiv e P k := congrArg (dartIndexEquiv e P) h
          _ = k' := hidxk))
      · exact Or.inr (Or.inr (calc
          j' = dartIndexEquiv e P j := hidxj.symm
          _ = dartIndexEquiv e P k := congrArg (dartIndexEquiv e P) h
          _ = k' := hidxk))
    · intro b i' j' hij' hi' hj'
      let a := e.map.drawing.drawing.σE.symm b
      have hab : e.map.drawing.drawing.σE a = b := by simp [a]
      let i := (dartIndexEquiv e P).symm i'
      let j := (dartIndexEquiv e P).symm j'
      have hidxi : dartIndexEquiv e P i = i' := by simp [i]
      have hidxj : dartIndexEquiv e P j = j' := by simp [j]
      have hi : (InfiniteBoundaryDartIndex.dart P i).1 = a := by
        apply e.map.drawing.drawing.σE.injective
        calc
          e.map.drawing.drawing.σE (InfiniteBoundaryDartIndex.dart P i).1 =
              (InfiniteBoundaryDartIndex.dart (e.pushforward P) i').1 := by
            rw [← hidxi]
            exact (dartIndexEquiv_edge e P i).symm
          _ = b := hi'
          _ = e.map.drawing.drawing.σE a := hab.symm
      have hj : (InfiniteBoundaryDartIndex.dart P j).1 = a := by
        apply e.map.drawing.drawing.σE.injective
        calc
          e.map.drawing.drawing.σE (InfiniteBoundaryDartIndex.dart P j).1 =
              (InfiniteBoundaryDartIndex.dart (e.pushforward P) j').1 := by
            rw [← hidxj]
            exact (dartIndexEquiv_edge e P j).symm
          _ = b := hj'
          _ = e.map.drawing.drawing.σE a := hab.symm
      have hij : i ≠ j := by
        intro h
        apply hij'
        calc
          i' = dartIndexEquiv e P i := hidxi.symm
          _ = dartIndexEquiv e P j := congrArg (dartIndexEquiv e P) h
          _ = j' := hidxj
      obtain ⟨hp, F, G, hF, hG, hleft, hright⟩ :=
        hpairs a i j hij hi hj
      have hp' : ¬ M'.toPlaneMapWithMissing.missing b := by
        rw [← hab]
        exact (e.map.drawing.missing_map a).not.mpr hp
      let F' := e.map.drawing.drawing.faceMap F
      let G' := e.map.drawing.drawing.faceMap G
      refine ⟨hp', F', G',
        (e.map.drawing.drawing.isExternal_faceMap_iff F).mpr hF,
        (e.map.drawing.drawing.isExternal_faceMap_iff G).mpr hG,
        ?_, ?_⟩
      · simpa [F', hab] using (LeftOf_map_iff e F ⟨a, hp⟩).mpr hleft
      · simpa [G', hab] using (RightOf_map_iff e G ⟨a, hp⟩).mpr hright

end InfiniteBoundaryMapEquiv

end DirectedDistances.PlanarMap

end
