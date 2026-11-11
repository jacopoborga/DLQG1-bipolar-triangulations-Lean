module

public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarLaw
public import DirectedDistances.KMSW.KMSWStageRootedMirror
public import DirectedDistances.PlanarMap.MirrorMap
public import DirectedDistances.Paper.Section3.BdyReverse

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
mirror uses the finite theorem's reversed ordered root-pair convention: it
mirrors the channeled map and reindexes the selected dart by `Fin.rev`. -/
@[expose] noncomputable def diskRootedPlanarSampleMirror (n ell : ℕ)
    (hell : 0 < ell) :
    ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) →
    ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) := fun p =>
  (kmswMirrorSymmetryEquiv (ell + 1) (n + (ell + 1)) (by omega) p.1,
    Fin.rev p.2)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
the disk parameters is invariant under the finite mirror and reversed root
pair reindexing. The grade is the actual sample grade in `diskRootedPlanarMapLaw`. -/
theorem diskRootedPlanarSampleMirror_uniform (n ell : ℕ) (hell : 0 < ell) :
    let Q :=
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
      (diskRootedPlanarSampleMirror n ell hell) =
        (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell)) := by
  let Q :=
    {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  change ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
      (fun p =>
        (kmswMirrorSymmetryEquiv (ell + 1) (n + (ell + 1)) (by omega) p.1,
          Fin.rev p.2)) = _
  exact kmswMirrorSymmetryEquiv_uniform_prod (ell + 1) n (by omega)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
sample map obtained by mirroring its finite KMSW parameter and reversing the
ordered root pair, at the grade of the actual Prop. 5.16 sample law. -/
@[expose] noncomputable def diskRootedPlanarMapOfMirroredSample (n ell : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) : RootedLocallyFinitePlanarMap :=
  diskRootedPlanarMapOfSample n ell hell
    (diskRootedPlanarSampleMirror n ell hell p)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
the law of the reindexed sample equals the actual disk sample law. The grade is
the Prop. 5.16 sample grade used by `diskRootedPlanarMapLaw`. -/
theorem diskRootedPlanarMapLaw_map_mirror (n ell : ℕ)
    (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    let Q :=
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    (((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
      (diskRootedPlanarMapOfMirroredSample n ell hell)) =
      (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure := by
  classical
  let Q :=
    {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : Nonempty (KMSWLeftWalkClass (ell + 1) n) :=
    kmswLeftWalkClass_nonempty_of_domain ell n hell hle hmod
  let : Nonempty Q := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm.nonempty
  let : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  let := diskBS_uniformCountingMeasure_probability Q
  let := diskBS_uniformCountingMeasure_probability (Fin ell)
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let μ := (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))
  have hmirror := diskRootedPlanarSampleMirror_uniform n ell hell
  have hmap := congrArg (fun ν : Measure (Q × Fin ell) =>
    ν.map (diskRootedPlanarMapOfSample n ell hell)) hmirror
  rw [Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)] at hmap
  rw [diskRootedPlanarMapLaw_toMeasure n ell hell hle hmod]
  change (μ.map (diskRootedPlanarMapOfSample n ell hell ∘
    diskRootedPlanarSampleMirror n ell hell)) =
      μ.map (diskRootedPlanarMapOfSample n ell hell)
  exact hmap

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
pointwise gap between the finite parameter reindexing and an action on the
actual `RootedLocallyFinitePlanarMap` sample. Any witness must reverse rotation,
preserve edge directions, retain missing geometric edges, and implement the
finite theorem's reversed ordered root-pair convention. This proposition is
open and is not assumed by any theorem in this file. The grade is the actual
sample grade used by `diskRootedPlanarMapLaw`. -/
def diskRootedPlanarSampleMirrorCompatibility (n ell : ℕ)
    (hell : 0 < ell) : Prop :=
  ∃ mirror : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap,
    ∀ p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
        Fin ell,
      let A := diskRootedPlanarMapOfSample n ell hell p
      let B := diskRootedPlanarMapOfMirroredSample n ell hell p
      mirror A = B ∧
        ∃ e : A.D ≃ B.D,
          (∀ d, e (A.rot d) = B.rot.symm (e d)) ∧
          (∀ d, e (A.edgeInv d) = B.edgeInv (e d)) ∧
          (∀ d, A.missing d ↔ B.missing (e d)) ∧
          (∀ d, A.tail d ↔ B.tail (e d)) ∧
          e (A.edgeInv A.outer) = B.outer ∧
          (∃ d, A.frameOtherDart = some d ∧ e d = B.rootDart) ∧
          e (A.edgeInv A.frameEdgeDart) = B.frameEdgeDart ∧
          B.frameOtherDart = some (e A.frameEdgeDart)

end DirectedDistances.PaperProofs.Section5
