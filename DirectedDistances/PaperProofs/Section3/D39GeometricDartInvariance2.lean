/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartInvariance

/-! # Whole-map geometric dart invariance for Definition 3.8 -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open unitInterval

universe uV uE u_1 u_2

variable {V : Type uV} {E : Type uE}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}



theorem D39GeomRootedMapIsoV2.domain_map
    {V_1 : Type u_1} {E_1 : Type u_2}
    {M' : DirectedPlaneMapWithMissing V_1 E_1} {rho' : E_1 × Bool}
    (e : D39GeomRootedMapIsoV2 M rho M' rho')
    (h : D39GeomDomain M rho) : D39GeomDomain M' rho' :=
  e.toCombDartIso.domain_map h

/-- Helper toward Definition 3.8: reverse selected stored endpoint orders as
a whole-map rooted geometric isomorphism. -/
@[expose] noncomputable def D39GeomRootedMapIsoV2.storeFlip
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E) :
    D39GeomRootedMapIsoV2 M rho (flipEdges M S)
      (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) := by
  classical
  let swap := d39GeomEdgeFlipBit S
  refine {
    h := Homeomorph.refl ℂ
    orientationPreserving := orientationPreserving_refl
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    edgeFlip := swap
    edgeParam := fun e => if swap e then unitInterval.symmHomeomorph
      else Homeomorph.refl _
    edgeParam_mono := ?_
    edgeParam_anti := ?_
    pos_map := ?_
    arc_map := ?_
    src_map := ?_
    tgt_map := ?_
    missing_map := ?_
    orientation_map := ?_
    root_edge_map := rfl
    root_bool_map := rfl }
  · intro e he
    simpa [he] using (strictMono_id : StrictMono (fun t : unitInterval => t))
  · intro e he
    rw [he]
    change StrictAnti unitInterval.symmHomeomorph
    simpa [unitInterval.symmHomeomorph] using unitInterval.strictAnti_symm
  · intro v
    simp [flipEdges, DirectedPlaneMapWithMissing.endpointSwap,
      PlaneMapWithMissing.endpointSwap]
  · intro e t
    change M.toPlaneMapWithMissing.toPlaneGraphDrawing.arc e t =
      M.toPlaneMapWithMissing.toPlaneGraphDrawing.endpointSwapArc swap e
        ((if swap e then unitInterval.symmHomeomorph else Homeomorph.refl _) t)
    by_cases hs : swap e = true
    · simp [hs, endpointSwapArc_apply, unitInterval.symm_symm]
    · simp [hs, endpointSwapArc_apply]
  · intro e
    by_cases hs : swap e = true <;>
      simp [flipEdges, DirectedPlaneMapWithMissing.endpointSwap,
        PlaneMapWithMissing.endpointSwap, PlaneGraphDrawing.endpointSwap, hs, swap]
  · intro e
    by_cases hs : swap e = true <;>
      simp [flipEdges, DirectedPlaneMapWithMissing.endpointSwap,
        PlaneMapWithMissing.endpointSwap, PlaneGraphDrawing.endpointSwap, hs, swap]
  · intro e
    rfl
  · intro e he
    by_cases hs : swap e = true <;>
      simp [flipEdges, DirectedPlaneMapWithMissing.endpointSwap, hs, swap] <;> rfl

/-- Helper toward Definition 3.8: endpoint storage flips preserve the rooted
geometric domain. -/
theorem D39GeomDomain.storeFlip
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E)
    (h : D39GeomDomain M rho) :
    D39GeomDomain (flipEdges M S)
      (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) :=
  (D39GeomRootedMapIsoV2.storeFlip M rho S).domain_map h

end DirectedDistances.PaperProofs.Section3

end
