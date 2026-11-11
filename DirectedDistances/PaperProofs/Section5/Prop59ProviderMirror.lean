/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59ProviderLaw

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.KMSW MeasureTheory

/-- Helper toward Proposition 5.9. Reflection preserves the local topology planar class
of rooted locally finite planar maps whenever their local topology rooted maps are
isomorphic. This is a combinatorial-class helper and does not establish
geometric Definition 3.8 faithfulness. -/
theorem mirrorRootedLocallyFinitePlanarMap_d39PlanarClass_eq_of_iso
    (M N : RootedLocallyFinitePlanarMap)
    (h : Nonempty (D39RootedMapIso
      M.toD39PlanarRootedMap.toD39RootedMap
      N.toD39PlanarRootedMap.toD39RootedMap)) :
    Quotient.mk D39PlanarRootedMap.setoid
        (mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap =
      Quotient.mk D39PlanarRootedMap.setoid
        (mirrorRootedLocallyFinitePlanarMap N).toD39PlanarRootedMap := by
  let A := M.toRootedLocallyFiniteMap
  let B := N.toRootedLocallyFiniteMap
  change Nonempty (D39RootedMapIso A.toD39RootedMap B.toD39RootedMap) at h
  apply Quotient.sound
  rcases h with ⟨I⟩
  change Nonempty (D39RootedMapIso
    (mirrorRootedLocallyFiniteMap A).toD39RootedMap
    (mirrorRootedLocallyFiniteMap B).toD39RootedMap)
  refine ⟨{
      toEquiv := I.toEquiv
      rot_comm := ?_
      edgeInv_comm := I.edgeInv_comm
      missing_iff := I.missing_iff
      tail_iff := I.tail_iff
      root_dart_comm := ?_
    }⟩
  · intro d
    change I.toEquiv (A.toD39RootedMap.core.rot.symm d) =
      B.toD39RootedMap.core.rot.symm (I.toEquiv d)
    let σ := A.toD39RootedMap.core.rot
    let τ := B.toD39RootedMap.core.rot
    have hc : τ (I.toEquiv (σ.symm d)) = I.toEquiv d := by
      calc
        τ (I.toEquiv (σ.symm d)) = I.toEquiv (σ (σ.symm d)) :=
          (I.rot_comm (σ.symm d)).symm
        _ = I.toEquiv d := congrArg I.toEquiv (σ.apply_symm_apply d)
    have h := congrArg τ.symm hc
    simpa only [τ.symm_apply_apply] using h
  · change I.toEquiv
      (A.toD39RootedMap.core.edgeInv A.toD39RootedMap.rootMark.dart) =
      B.toD39RootedMap.core.edgeInv B.toD39RootedMap.rootMark.dart
    exact (I.edgeInv_comm _).trans
      (congrArg B.toD39RootedMap.core.edgeInv I.root_dart_comm)

/- The recorded endpoint compared a provider-side `D39RootedMap` with a
`D39PlanarRootedMap` on the code side, and applied the planar mirror to the
provider's unwrapped `RootedLocallyFiniteMap`. On the conull event the capture
witnesses package that provider map as a `RootedLocallyFinitePlanarMap`. The
faithful class-level correction is therefore equality of the local topology planar classes
of the two mirrored planar maps. -/
/-- Helper toward Proposition 5.9. This is a combinatorial-class helper; it does
not establish geometric Definition 3.8 faithfulness. Almost surely, the
provider and code-selected planar maps have the same local topology planar class after
reflection. -/
theorem uibhbotCodeLawRel_ae_provider_d39PlanarClass_eq_mirror :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      W ∈ uibhbotRootedPlanarMapConullEvent ∧
      ∃ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C₀ : UIBHBOTCertifiedRootCapture W 0)
        (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
        Quotient.mk D39PlanarRootedMap.setoid
            ((mirrorRootedLocallyFinitePlanarMap
              (uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap)).toD39PlanarRootedMap) =
          Quotient.mk D39PlanarRootedMap.setoid
            ((mirrorRootedLocallyFinitePlanarMap
              (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap) := by
  filter_upwards [uibhbotCodeLawRel_ae_provider_d39PlanarClass_eq] with W hProvider
  obtain ⟨hW, H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    hClauses⟩ := hProvider
  have hClausesCopy := hClauses.1
  rcases hClausesCopy with ⟨_, _, _, _, _, _, _, _, _, _, he, _⟩
  obtain ⟨hhit, C₀, hIdentified⟩ :=
    uibhbotProviderAssemblyD39_identification W hW H h0 hL hR hfin P hp ha F hf hFim hFa
      hRpos e he
  obtain ⟨_, _, _, hcap, _⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hW).1
  let providerPlanar := uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap
  have hMirrorIso : Nonempty (D39RootedMapIso
      providerPlanar.toD39PlanarRootedMap.toD39RootedMap
      (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap.toD39RootedMap) := by
    simpa [providerPlanar, uibhbotRootedLocallyFinitePlanarMap,
      RootedLocallyFinitePlanarMap.toD39PlanarRootedMap] using hIdentified.1
  exact ⟨hW, H, hhit, C₀, hcap,
    mirrorRootedLocallyFinitePlanarMap_d39PlanarClass_eq_of_iso
      providerPlanar (uibhbotRootedPlanarMapOfCode W) hMirrorIso⟩




































































































end DirectedDistances.PaperProofs.Section5
