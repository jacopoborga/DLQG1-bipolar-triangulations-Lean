/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBoundaryPresentationTransport
public import DirectedDistances.PlanarMap.BoundaryPresentationData
public import DirectedDistances.PlanarMap.Definition32OrientedSideTransport

/-! # Further transport of finite boundary presentations -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

variable {V E V' E' : Type*}
variable {M : DirectedPlaneMapWithMissing V E}
variable {M' : DirectedPlaneMapWithMissing V' E'}

namespace DirectedPlaneMapWithMissing.HomeoEquiv

/-- Helper toward Definition 3.2: the UL block commutes with pushforward. -/
theorem ul_pushforward (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    (e.pushforward P).ul = P.ul.map e.mapDart := by
  rw [FiniteBoundaryPresentation.ul_eq (P := e.pushforward P),
    FiniteBoundaryPresentation.ul_eq (P := P)]
  simp only [pushforward, List.map_take, List.map_drop]

/-- Helper toward Definition 3.2: the UR block commutes with pushforward. -/
theorem ur_pushforward (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    (e.pushforward P).ur = P.ur.map e.mapDart := by
  rw [FiniteBoundaryPresentation.ur_eq (P := e.pushforward P),
    FiniteBoundaryPresentation.ur_eq (P := P)]
  simp only [pushforward, List.map_take, List.map_drop]

/-- Helper toward Definition 3.2: the LR block commutes with pushforward. -/
theorem lr_pushforward (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    (e.pushforward P).lr = P.lr.map e.mapDart := by
  rw [FiniteBoundaryPresentation.lr_eq (P := e.pushforward P),
    FiniteBoundaryPresentation.lr_eq (P := P)]
  simp only [pushforward, List.map_take, List.map_drop]

/-- Helper toward Definition 3.2: the LL block commutes with pushforward. -/
theorem ll_pushforward (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    (e.pushforward P).ll = P.ll.map e.mapDart := by
  rw [FiniteBoundaryPresentation.ll_eq (P := e.pushforward P),
    FiniteBoundaryPresentation.ll_eq (P := P)]
  simp only [pushforward, List.map_drop]

/-- Helper toward Definition 3.2: the UR missing-edge predicate is invariant under pushforward. -/
theorem UROk_pushforward_iff (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    UROk (e.pushforward P) ↔ UROk P := by
  rw [UROk_iff (P := e.pushforward P), ur_pushforward, UROk_iff (P := P)]
  constructor
  · intro h d hd
    have hm := h (e.mapDart d) (List.mem_map.mpr ⟨d, hd, rfl⟩)
    change M'.toPlaneMapWithMissing.missing
      (e.drawing.drawing.σE d.1) at hm
    exact (e.drawing.missing_map d.1).mp hm
  · intro h d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, hEq⟩
    have hEdge : d.1 = e.drawing.drawing.σE d₀.1 := congrArg Prod.fst hEq.symm
    rw [hEdge]
    exact (e.drawing.missing_map d₀.1).mpr (h d₀ hd₀)

/-- Helper toward Definition 3.2: the LL missing-edge predicate is invariant under pushforward. -/
theorem LLOk_pushforward_iff (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    LLOk (e.pushforward P) ↔ LLOk P := by
  rw [LLOk_iff (P := e.pushforward P), ll_pushforward, LLOk_iff (P := P)]
  constructor
  · intro h d hd
    have hm := h (e.mapDart d) (List.mem_map.mpr ⟨d, hd, rfl⟩)
    change M'.toPlaneMapWithMissing.missing
      (e.drawing.drawing.σE d.1) at hm
    exact (e.drawing.missing_map d.1).mp hm
  · intro h d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, hEq⟩
    have hEdge : d.1 = e.drawing.drawing.σE d₀.1 := congrArg Prod.fst hEq.symm
    rw [hEdge]
    exact (e.drawing.missing_map d₀.1).mpr (h d₀ hd₀)

/-- Helper toward Definition 3.2: external-frontier edges are invariant under map equivalence. -/
theorem externalFrontierEdge_pushforward_iff
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M') (a : E) :
    ExternalFrontierEdge M' (e.drawing.drawing.σE a) ↔
      ExternalFrontierEdge M a := by
  rw [externalFrontierEdge_iff, externalFrontierEdge_iff]
  constructor
  · rintro ⟨F', hF', hsub'⟩
    let F := e.drawing.drawing.faceEquiv.symm F'
    have hface : e.drawing.drawing.faceMap F = F' :=
      e.drawing.drawing.faceEquiv.apply_symm_apply F'
    refine ⟨F, ?_, ?_⟩
    · exact (e.drawing.drawing.isExternal_faceMap_iff F).mp (hface ▸ hF')
    · intro z hz
      have hz' : e.drawing.drawing.h z ∈
          Set.range (M'.toPlaneMapWithMissing.arc
            (e.drawing.drawing.σE a)) := by
        rw [e.drawing.drawing.arc_range_map]
        exact ⟨z, hz, rfl⟩
      have hmem := hsub' hz'
      rw [← hface, e.drawing.drawing.faceMap_val,
        ← e.drawing.drawing.h.image_frontier] at hmem
      rcases hmem with ⟨w, hw, hzw⟩
      exact e.drawing.drawing.h.injective hzw ▸ hw
  · rintro ⟨F, hF, hsub⟩
    refine ⟨e.drawing.drawing.faceMap F,
      (e.drawing.drawing.isExternal_faceMap_iff F).mpr hF, ?_⟩
    intro z hz
    rw [e.drawing.drawing.arc_range_map] at hz
    rcases hz with ⟨w, hw, hzw⟩
    rw [e.drawing.drawing.faceMap_val,
      ← e.drawing.drawing.h.image_frontier]
    exact ⟨w, hsub hw, hzw⟩

end DirectedPlaneMapWithMissing.HomeoEquiv

















end DirectedDistances.PlanarMap

end
