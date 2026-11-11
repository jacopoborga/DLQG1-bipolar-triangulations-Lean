module

public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarLaw
public import DirectedDistances.PlanarMap.D39RootedPlanarBallGenusZero

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv). The local topology ball of a
sampled disk-rooted map is the faced-framed ball converted to local topology data. -/
theorem diskRootedPlanarMapOfSample_d39BallClass_eq (n ell : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) (r : ℕ) :
    d39BallClass
        ((diskRootedPlanarMapOfSample n ell hell p).toRootedLocallyFiniteMap.toD39RootedMap)
        (r + 1) (Nat.succ_pos r) =
      facedFramedBallClassToD39BallClass
        (facedDiskBSBallClass n ell hell (r + 1) (Nat.succ_pos r) p) := by
  rw [← diskRootedPlanarMapOfSample_facedClass_eq n ell hell p r]
  exact d39BallClass_eq_facedFramedBallClassToD39BallClass
    (diskRootedPlanarMapOfSample n ell hell p) r

end DirectedDistances.PaperProofs.Section5
