module

public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarLaw
public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.PaperProofs.Section3.BSTopologyGeneric

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16; not a paper result.
The finite disk sample with its ordered missing root mark. -/
@[expose] noncomputable def diskRootedD39MapOfSample (n ell : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) : D39RootedMap :=
  (diskRootedPlanarMapOfSample n ell hell p).toRootedLocallyFiniteMap.toD39RootedMap

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16; not a paper result.
Local finiteness follows from the finite disk dart carrier. -/
theorem diskRootedD39MapOfSample_locallyFinite (n ell : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    ∀ d : (diskRootedD39MapOfSample n ell hell p).core.D,
      {e | (diskRootedD39MapOfSample n ell hell p).core.rot.SameCycle d e}.Finite := by
  exact (diskRootedD39MapOfSample n ell hell p).core.locallyFinite

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v2) and Proposition 5.16; not a paper result.
The finite sample is measurable into the local topology Borel space. -/
theorem measurable_diskRootedD39MapOfSample (n ell : ℕ) (hell : 0 < ell) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    letI : BorelSpace D39RootedMap := ⟨rfl⟩
    Measurable (diskRootedD39MapOfSample n ell hell) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : TopologicalSpace D39RootedMap :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  let : MeasurableSpace D39RootedMap := borel D39RootedMap
  let : BorelSpace D39RootedMap := ⟨rfl⟩
  exact measurable_of_countable _

end DirectedDistances.PaperProofs.Section5
