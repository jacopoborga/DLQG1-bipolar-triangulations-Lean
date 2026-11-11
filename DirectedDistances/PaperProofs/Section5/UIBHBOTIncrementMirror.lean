module

public import DirectedDistances.RandomWalk.UIBHBOTBusemannIncrement
public import DirectedDistances.PaperProofs.Section5.Prop516RootedLawConvergence
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorClose

/-! Conditional scalar symmetry transport for the reversed ordered root-pair convention.

The intrinsic rooted-map observable has NOT been constructed here. Its measurable
realization and geometric reflection are separate, explicitly open propositions.
The imported code-level distance realization does not identify those observables
on the rooted planar-map carrier. In particular, no arbitrary code preimage or
default value is used to manufacture a rooted-map Busemann observable.

For boundary labels `y_k = f(x_(1-k))`, reanchoring at zero gives the profile
`X(1-k) - X(1)`. Its index-zero increment is minus the original index-two increment.
The algebra below proves this shift; identifying these labels with the intrinsic
boundary traversal of the actual reflected carrier remains part of the open
geometric reflection obligation. Mirror measurability is also recorded explicitly.

The final theorem is an implication from these open obligations and mirror-law
invariance. It is not an unconditional symmetry theorem or a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The helper faced-ball topology, with the same convention as the imported map law. -/
noncomputable local instance incrementMirrorTopology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel measurable structure of the helper faced-ball topology. -/
noncomputable local instance incrementMirrorMeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Normalized reversal for the reanchored labels `y_k = f(x_(1-k))`. This is profile
algebra only; it does not identify the boundary labels of a reflected map. -/
@[expose] def reanchoredMirrorBusemannProfile (X : ℤ → ℤ) (k : ℤ) : ℤ :=
  X (1 - k) - X 1

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reanchoring normalizes the profile at zero. -/
theorem reanchoredMirrorBusemannProfile_zero (X : ℤ → ℤ) :
    reanchoredMirrorBusemannProfile X 0 = 0 := by
  simp only [reanchoredMirrorBusemannProfile, sub_zero, sub_self]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reanchoring changes the index-zero increment to minus increment two, rather than
minus increment zero. The assertion is deterministic and requires no independence. -/
theorem reanchoredMirrorBusemannProfile_increment (X : ℤ → ℤ) (k : ℤ) :
    reanchoredMirrorBusemannProfile X k -
        reanchoredMirrorBusemannProfile X (k - 1) =
      -(X (2 - k) - X ((2 - k) - 1)) := by
  have hleft : 1 - (k - 1) = 2 - k := by omega
  have hright : (2 - k) - 1 = 1 - k := by omega
  simp only [reanchoredMirrorBusemannProfile, hleft, hright]
  omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The existing mirror chooses the former opposite frame incidence as its root.
This verifies the root swap, but does not establish the full boundary reindexing. -/
theorem incrementMirror_rootDart (M : RootedLocallyFinitePlanarMap) :
    (mirrorRootedLocallyFinitePlanarMap M).rootDart = M.edgeInv M.frameEdgeDart := rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open obligation (1): the proposed intrinsic increment observables are measurable
in the helper Borel structure. No family of observables is supplied by this file. -/
@[expose] def UIBHBOTIncrementObservableMeasurable
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ) : Prop :=
  ∀ k, Measurable (Φ k)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open obligation (2): the rooted-map observables realize the already constructed
code increments, simultaneously at every integer boundary index. This requires
the intrinsic boundary and distance identifications, not just code measurability. -/
@[expose] def UIBHBOTIncrementObservableRealization
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ) : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
    Φ k (uibhbotRootedPlanarMapOfCode W) = uibhbotBusemannIncrement k W

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open obligation (3), with shift two for the reanchored reversed-root convention.
The actual mirror must transport the intrinsic finite distances and boundary
labels. The deterministic profile identity alone does not prove this assertion. -/
@[expose] def UIBHBOTIncrementObservableReflection
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ) : Prop :=
  ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
    Φ 0 (mirrorRootedLocallyFinitePlanarMap M) = -Φ 2 M

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Separate open measure-transport obligation, at the weakest strength used below.
Mirror-law equality by itself is not used as a substitute for measurability. -/
@[expose] def UIBHBOTIncrementMirrorMeasurable : Prop :=
  AEMeasurable mirrorRootedLocallyFinitePlanarMap
    (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Conditional transport of the proved code marginal law to any measurable intrinsic
realization. This does not construct or certify such a realization. -/
theorem uibhbotIncrementObservable_law
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ)
    (hΦm : UIBHBOTIncrementObservableMeasurable Φ)
    (hΦr : UIBHBOTIncrementObservableRealization Φ) (k : ℤ) :
    (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map (Φ k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) := by
  change ((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode).map (Φ k) = _
  rw [Measure.map_map (hΦm k) measurable_uibhbotRootedPlanarMapOfCode]
  calc
    _ = (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (uibhbotBusemannIncrement k) := by
      apply Measure.map_congr
      filter_upwards [hΦr] with W hW
      exact hW k
    _ = _ := uibhbotBusemannIncrement_law k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Honest conditional symmetry implication. All four open observable/transport
obligations remain explicit premises; none is asserted here. Only the proved
equality of increment marginals is needed, not independence of the increments. -/
theorem hsym_of_uibhbot_mirror_invariance
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ)
    (hΦm : UIBHBOTIncrementObservableMeasurable Φ)
    (hΦr : UIBHBOTIncrementObservableRealization Φ)
    (hΦmirror : UIBHBOTIncrementObservableReflection Φ)
    (hm : UIBHBOTIncrementMirrorMeasurable)
    (h : (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
        mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw) :
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) := by
  have hscalar :
      (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map (Φ 0) =
        (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
          (fun M => -Φ 2 M) := by
    calc
      _ = ((uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
          mirrorRootedLocallyFinitePlanarMap).map (Φ 0) := by rw [h]
      _ = (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
          (Φ 0 ∘ mirrorRootedLocallyFinitePlanarMap) :=
        (hΦm 0).aemeasurable.map_map_of_aemeasurable hm
      _ = _ := Measure.map_congr hΦmirror
  have hinc : Measurable (ldpIncrement busemannLDPMeasurableVersion 0) :=
    (measurable_busemannLDPMeasurableVersion 0).sub
      (measurable_busemannLDPMeasurableVersion (0 - 1))
  calc
    _ = (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map (Φ 0) :=
      (uibhbotIncrementObservable_law Φ hΦm hΦr 0).symm
    _ = (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
        (fun M => -Φ 2 M) := hscalar
    _ = ((uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
        (Φ 2)).map (fun z : ℤ => -z) :=
      (Measure.map_map measurable_neg (hΦm 2)).symm
    _ = (iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0)).map
        (fun z : ℤ => -z) := by rw [uibhbotIncrementObservable_law Φ hΦm hΦr 2]
    _ = _ := Measure.map_map measurable_neg hinc

end DirectedDistances.PaperProofs.Section5
