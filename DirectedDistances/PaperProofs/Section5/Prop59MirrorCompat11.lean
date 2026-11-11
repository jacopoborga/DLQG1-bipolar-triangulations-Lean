/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat10
public import DirectedDistances.PaperProofs.Section5.Prop59RootAbsentAE
import DirectedDistances.PlanarMap.GeneralPlaneMapSides
import DirectedDistances.PlanarMap.GeneralPlaneMapSideDegree
import DirectedDistances.PaperProofs.Section3.D39GeomMirror

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open unitInterval
open scoped ComplexConjugate

/-- Helper toward Proposition 5.9. Conjugation commutes with the restricted
subarc used to close a winding loop. -/
theorem prop59_edgeSubarc_geomConj {x y : ℂ} (γ : Path x y)
    (a b : I) (hab : a ≤ b) :
    (edgeSubarc γ a b hab).map Complex.continuous_conj =
      edgeSubarc (γ.map Complex.continuous_conj) a b hab := by
  ext t
  let r : ℝ := min (max (t : ℝ) a) b
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [r]
      exact le_min (a.2.1.trans (le_max_right _ _)) b.2.1
    · dsimp [r]
      exact le_trans (min_le_right _ _) b.2.2
  change conj (γ.extend r) = (γ.map Complex.continuous_conj).extend r
  rw [γ.extend_extends' ⟨r, hr⟩,
    (γ.map Complex.continuous_conj).extend_extends' ⟨r, hr⟩]
  simp only [Path.map_coe, Function.comp_apply]

/-- Helper toward Proposition 5.9. The image of a closure under conjugation
is the closure of the conjugate image. -/
theorem prop59_conj_image_closure (S : Set ℂ) :
    conj '' closure S = closure (conj '' S) := by
  apply Set.Subset.antisymm
  · exact image_closure_subset_closure_image Complex.continuous_conj
  · intro z hz
    have hz' : conj z ∈ closure (conj '' (conj '' S)) :=
      image_closure_subset_closure_image Complex.continuous_conj ⟨z, hz, rfl⟩
    have hz'' : conj z ∈ closure S := by
      simpa [Set.image_image, Complex.conj_conj] using hz'
    exact ⟨conj z, hz'', by simp⟩

/-- Helper toward Proposition 5.9. Reflection interchanges the two
winding-defined side predicates along a path. -/
theorem prop59_LeftAtOn_geomConj_iff_RightAtOn
    {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) :
    LeftAtOn (conj '' F) (γ.map Complex.continuous_conj) s ↔
      RightAtOn F γ s := by
  constructor
  · rintro ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hclose⟩
    let q' : Path (γ b) (γ a) :=
      (q.map Complex.continuous_conj).cast
        (by simp [Path.map_coe])
        (by simp [Path.map_coe])
    have hq'i : Function.Injective q' := by
      intro u v huv
      apply hqi
      exact (Function.Involutive.injective (fun z : ℂ => Complex.conj_conj z))
        (by simpa [q', Path.map_coe] using huv)
    have hq'F : ∀ t : I, t ∈ openParams → q' t ∈ F := by
      intro t ht
      obtain ⟨z, hz, hzt⟩ := hqF t ht
      have heq : q' t = z := by
        simpa [q', Path.map_coe, Complex.conj_conj] using (congrArg conj hzt).symm
      rw [heq]
      exact hz
    have hloop :
        (((edgeSubarc γ a b (le_of_lt (lt_trans has hsb))).trans q').map
          Complex.continuous_conj) =
          (edgeSubarc (γ.map Complex.continuous_conj) a b
            (le_of_lt (lt_trans has hsb))).trans q := by
      rw [Path.map_trans, prop59_edgeSubarc_geomConj]
      congr 1
      ext t
      simp [q', Path.map_coe]
      rfl
    refine ⟨a, b, ha, has, hsb, hb, q', hq'i, hq'F, ?_⟩
    let S : Set ℂ := {w | w ∈ F ∧ HasWinding
      ((edgeSubarc γ a b (le_of_lt (lt_trans has hsb))).trans q') w (-1)}
    let T : Set ℂ := {w | w ∈ conj '' F ∧ HasWinding
      ((edgeSubarc (γ.map Complex.continuous_conj) a b
        (le_of_lt (lt_trans has hsb))).trans q) w 1}
    have hST : conj '' S = T := by
      ext w
      constructor
      · rintro ⟨z, ⟨hzF, hzW⟩, rfl⟩
        refine ⟨⟨z, hzF, rfl⟩, ?_⟩
        rw [← hloop]
        exact (hasWinding_conj_iff _ z (-1)).2 hzW
      · rintro ⟨⟨z, hzF, rfl⟩, hzW⟩
        refine ⟨z, ⟨hzF, ?_⟩, by simp⟩
        rw [← hloop] at hzW
        exact (hasWinding_conj_iff _ z (-1)).1 hzW
    have hclose' : conj (γ s.1) ∈ conj '' closure S := by
      rw [prop59_conj_image_closure, hST]
      exact hclose
    obtain ⟨z, hz, heq⟩ := hclose'
    have : z = γ s.1 :=
      Function.Involutive.injective (fun w : ℂ => Complex.conj_conj w) heq
    simpa [this] using hz
  · rintro ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hclose⟩
    let q' : Path ((γ.map Complex.continuous_conj) b)
        ((γ.map Complex.continuous_conj) a) :=
      (q.map Complex.continuous_conj).cast
        (by simp [Path.map_coe]) (by simp [Path.map_coe])
    have hq'i : Function.Injective q' := by
      intro u v huv
      apply hqi
      exact (Function.Involutive.injective (fun z : ℂ => Complex.conj_conj z))
        (by simpa [q', Path.map_coe] using huv)
    have hq'F : ∀ t : I, t ∈ openParams → q' t ∈ conj '' F := by
      intro t ht
      exact ⟨q t, hqF t ht, by simp [q']⟩
    have hloop :
        (((edgeSubarc γ a b (le_of_lt (lt_trans has hsb))).trans q).map
          Complex.continuous_conj) =
          (edgeSubarc (γ.map Complex.continuous_conj) a b
            (le_of_lt (lt_trans has hsb))).trans q' := by
      rw [Path.map_trans, prop59_edgeSubarc_geomConj]
      ext t
      simp [q']
      rfl
    refine ⟨a, b, ha, has, hsb, hb, q', hq'i, hq'F, ?_⟩
    let S : Set ℂ := {w | w ∈ F ∧ HasWinding
      ((edgeSubarc γ a b (le_of_lt (lt_trans has hsb))).trans q) w (-1)}
    let T : Set ℂ := {w | w ∈ conj '' F ∧ HasWinding
      ((edgeSubarc (γ.map Complex.continuous_conj) a b
        (le_of_lt (lt_trans has hsb))).trans q') w 1}
    have hST : conj '' S = T := by
      ext w
      constructor
      · rintro ⟨z, ⟨hzF, hzW⟩, rfl⟩
        refine ⟨⟨z, hzF, rfl⟩, ?_⟩
        rw [← hloop]
        exact (hasWinding_conj_iff _ z (-1)).2 hzW
      · rintro ⟨⟨z, hzF, rfl⟩, hzW⟩
        refine ⟨z, ⟨hzF, ?_⟩, by simp⟩
        rw [← hloop] at hzW
        exact (hasWinding_conj_iff _ z (-1)).1 hzW
    have hclose' : conj (γ s.1) ∈ conj '' closure S :=
      ⟨γ s.1, hclose, rfl⟩
    rw [prop59_conj_image_closure, hST] at hclose'
    exact hclose'

/-- Helper toward Proposition 5.9. Applying the side swap after a second
reflection gives the converse side correspondence. -/
theorem prop59_RightAtOn_geomConj_iff_LeftAtOn
    {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) :
    RightAtOn (conj '' F) (γ.map Complex.continuous_conj) s ↔
      LeftAtOn F γ s := by
  have himage : conj '' (conj '' F) = F := by
    ext z
    simp [Set.image_image]
  let δ : Path x y := ((γ.map Complex.continuous_conj).map
    Complex.continuous_conj).cast (by simp) (by simp)
  have hpath : δ = γ := by
    ext t
    simp [δ, Path.map_coe]
  have hbase := prop59_LeftAtOn_geomConj_iff_RightAtOn
    (conj '' F) (γ.map Complex.continuous_conj) s
  have hcast : LeftAtOn (conj '' (conj '' F))
      ((γ.map Complex.continuous_conj).map Complex.continuous_conj) s ↔
      LeftAtOn F δ s := by
    rw [himage]
    exact Iff.rfl
  have hdouble : LeftAtOn F δ s ↔
      RightAtOn (conj '' F) (γ.map Complex.continuous_conj) s :=
    hcast.symm.trans hbase
  have hmap : δ.map Complex.continuous_conj =
      γ.map Complex.continuous_conj :=
    congrArg (fun p : Path x y => p.map Complex.continuous_conj) hpath
  have hdouble' : RightAtOn (conj '' F) (δ.map Complex.continuous_conj) s ↔
      LeftAtOn F δ s := by
    rw [hmap]
    exact hdouble.symm
  rw [← hpath]
  exact hdouble'

/-- Helper toward Proposition 5.9. The reflected face lies on the left of a
reflected stored edge exactly when the original face lies on its right. -/
theorem prop59_SideLeftOf_geomMirror_iff_SideRightOf
    {V E : Type*} (D : PlaneGraphDrawing V E)
    (F : D.Face) (e : E) :
    D.geomMirror.SideLeftOf (D.geomMirrorEquiv.faceMap F) e ↔
      D.SideRightOf F e := by
  change (∀ s, LeftAtOn (D.geomMirrorEquiv.faceMap F).val
      ((D.arc e).map Complex.continuous_conj) s) ↔
    ∀ s, RightAtOn F.val (D.arc e) s
  rw [D.geomMirrorEquiv.faceMap_val]
  have hface : geomConj '' F.val = conj '' F.val := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [geomConj]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [geomConj]⟩
  have hface' : D.geomMirrorEquiv.h '' F.val = conj '' F.val := by
    change geomConj '' F.val = conj '' F.val
    exact hface
  rw [hface']
  exact forall_congr' fun s => prop59_LeftAtOn_geomConj_iff_RightAtOn F.val
    (D.arc e) s

/-- Helper toward Proposition 5.9. The reflected face lies on the right of a
reflected stored edge exactly when the original face lies on its left. -/
theorem prop59_SideRightOf_geomMirror_iff_SideLeftOf
    {V E : Type*} (D : PlaneGraphDrawing V E)
    (F : D.Face) (e : E) :
    D.geomMirror.SideRightOf (D.geomMirrorEquiv.faceMap F) e ↔
      D.SideLeftOf F e := by
  change (∀ s, RightAtOn (D.geomMirrorEquiv.faceMap F).val
      ((D.arc e).map Complex.continuous_conj) s) ↔
    ∀ s, LeftAtOn F.val (D.arc e) s
  rw [D.geomMirrorEquiv.faceMap_val]
  have hface : geomConj '' F.val = conj '' F.val := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [geomConj]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [geomConj]⟩
  have hface' : D.geomMirrorEquiv.h '' F.val = conj '' F.val := by
    change geomConj '' F.val = conj '' F.val
    exact hface
  rw [hface']
  exact forall_congr' fun s => prop59_RightAtOn_geomConj_iff_LeftAtOn F.val
    (D.arc e) s

/- The remaining representation assembly toward Proposition 5.9 is recorded
without adding any conclusion-equivalent premise.

(B) The exact generic reflected-data target, with the available field inputs,
is: for `M : RootedLocallyFiniteMap`, `B : D39DomainRootedMapV2`,
`x : D39DrawingRepresentationData3 M.toD39RootedMap B`, and
`hmirrorDomain : D39GeomDomain B.map.geomMirror
  (d39GeomMirrorRoot B.root)`, construct

`D39DrawingRepresentationData3
  (mirrorRootedLocallyFiniteMap M).toD39RootedMap
  ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root,
    hmirrorDomain⟩`.

The intended route is a field-by-field structure assembly using
`prop59_mirrorRepresentation_rootMark`, `_dart_edgeInv`, `_dart_endpoints`,
`_dart_headEndpoint`, `_edge_fields`, `_rotation_field`,
`_frontier_field`, `prop59_mirrorFaceCycle`, and the two side-transport
equivalences proved above. That structure assembly is not included here.

(C) The exact almost-sure target under the measure used for Proposition 5.9
is:

`∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
  ∃ (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n),
    let A := uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos
    let rho := uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin
    ∃ (hA : D39GeomDomain A rho),
      ∃ (hmirrorDomain : D39GeomDomain A.geomMirror
        (d39GeomMirrorRoot rho)),
        D39DrawingRepresents3
          ((mirrorRootedLocallyFinitePlanarMap
            (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap
              .toD39RootedMap)
          ⟨A.V, A.E, A.geomMirror, d39GeomMirrorRoot rho, hmirrorDomain⟩`.

The route to close (C) is to intersect the conull event for
`uibhbotRootedPlanarMapConullEvent` with
`uibhbotCodeLawRel_ae_d39CanonicalGeomDomain` and
`prop59_uibhbotRootEdge_absent_ae`, obtain the existing unmirrored canonical
representation from `uibhbotD39CanonicalRepresentation14_data3`, then apply
(B). Neither this file's (B) structure assembly nor that almost-sure
combination is proved here. -/

end DirectedDistances.PaperProofs.Section5

end
