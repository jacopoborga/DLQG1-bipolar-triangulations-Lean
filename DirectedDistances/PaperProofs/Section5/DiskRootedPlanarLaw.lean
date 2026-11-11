module

public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarObject
public import DirectedDistances.PaperProofs.Section5.FacedDiskWindowCompare
public import DirectedDistances.PaperProofs.Section3.BSTopologyGeneric
public import DirectedDistances.PaperProofs.Section3.RootedMapBallMeasurability

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
uniform missing-edge mark determine the disk-rooted planar map. -/
@[expose] noncomputable def diskRootedPlanarMapOfSample (n ell : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) : RootedLocallyFinitePlanarMap :=
  diskRootedPlanarMapOfCodeMark
    ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1)
    (Fin.cast (by omega : ell = (ell + 1) - 1) p.2)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
the local topology measurable structure on rooted locally finite planar maps. -/
theorem measurable_diskRootedPlanarMapOfSample (n ell : ℕ) (hell : 0 < ell) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    Measurable (diskRootedPlanarMapOfSample n ell hell) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  exact measurable_of_countable _

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
same independent uniform factors as `facedDiskBSBallLaw`. -/
@[expose] noncomputable def diskRootedPlanarMapLaw (n ell : ℕ)
    (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    ProbabilityMeasure RootedLocallyFinitePlanarMap := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  letI : MeasurableSpace Q := ⊤
  letI : MeasurableSpace (Fin ell) := ⊤
  letI : Nonempty (KMSWLeftWalkClass (ell + 1) n) :=
    kmswLeftWalkClass_nonempty_of_domain ell n hell hle hmod
  letI : Nonempty Q := F.symm.nonempty
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  letI := diskBS_uniformCountingMeasure_probability Q
  letI := diskBS_uniformCountingMeasure_probability (Fin ell)
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  exact ⟨((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
    (diskRootedPlanarMapOfSample n ell hell), inferInstance⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
same product of uniform finite sample measures used by `facedDiskBSBallLaw`. -/
theorem diskRootedPlanarMapLaw_toMeasure (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
        (diskRootedPlanarMapOfSample n ell hell) := rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
the source faced-ball radius `r + 1`. -/
theorem diskRootedPlanarMapOfSample_facedClass_eq (n ell : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) (r : ℕ) :
    rootedLocallyFiniteFacedBallClass r
        (diskRootedPlanarMapOfSample n ell hell p) =
      facedDiskBSBallClass n ell hell (r + 1) (Nat.succ_pos r) p := by
  rcases p with ⟨q, k⟩
  change rootedLocallyFiniteFacedBallClass r
      (diskRootedPlanarMapOfCodeMark
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q)
        (Fin.cast (by omega : ell = (ell + 1) - 1) k)) = _
  rw [diskRootedPlanarMapOfCodeMark_facedBallClass_index_eq]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
of the disk-rooted law is exactly the finite faced disk law, with index shift `r+1`. -/
theorem diskRootedPlanarMapLaw_map_facedClass (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) :
    letI : TopologicalSpace FacedFramedBallClass := ⊥
    letI : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    (diskRootedPlanarMapLaw n ell hell hle hmod).map
      (rootedLocallyFiniteFacedBallClass r) =
        facedDiskBSBallLaw n ell hell hle hmod (r + 1) (Nat.succ_pos r) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let : MeasurableSpace FacedFramedBallClass := ⊤
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  apply Subtype.ext
  change (((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
      (diskRootedPlanarMapOfSample n ell hell)).map
      (rootedLocallyFiniteFacedBallClass r) =
    (((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
      (facedDiskBSBallClass n ell hell (r + 1) (Nat.succ_pos r)))
  have hclass : rootedLocallyFiniteFacedBallClass r ∘
      diskRootedPlanarMapOfSample n ell hell =
        facedDiskBSBallClass n ell hell (r + 1) (Nat.succ_pos r) := by
    funext p
    exact diskRootedPlanarMapOfSample_facedClass_eq n ell hell p r
  have hsample : Measurable (diskRootedPlanarMapOfSample n ell hell) :=
    measurable_diskRootedPlanarMapOfSample n ell hell
  have hclassmeas : Measurable (rootedLocallyFiniteFacedBallClass r) := by
    apply measurable_iff_comap_le.mpr
    let S := rootedLocallyFiniteFacedBallSystem
    change MeasurableSpace.comap (S.ballClass r) ⊤ ≤
      @borel S.Object (bsLocalDistanceTopologyGeneric S)
    rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic S]
    exact le_iSup_of_le r le_rfl
  rw [Measure.map_map hclassmeas hsample, hclass]

end DirectedDistances.PaperProofs.Section5
