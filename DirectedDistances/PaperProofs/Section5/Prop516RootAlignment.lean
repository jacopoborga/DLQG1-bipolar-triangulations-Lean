/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516D39ClassTransport
public import DirectedDistances.KMSW.KMSWDiskRootedLaw
















public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory

/-- Helper toward Proposition 5.16. The planar-map root is the flipped KMSW
sampled dart, preserving its geometric edge ID. -/
theorem diskRootedMapOfCodeMark_rootDart_eq_edgeFlip {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    (diskRootedMapOfCodeMark c k).rootDart =
      edgeFlip _ (kmswDiskRootDart c k) := rfl

/-- Helper toward Proposition 5.16. The root mark has the same geometric edge
ID as the unflipped KMSW sample. -/
theorem diskRootedMapOfCodeMark_rootEdge_eq_sample {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    ((diskRootedMapOfCodeMark c k).rootDart).1 =
      (kmswDiskRootDart c k).1 := by
  rw [diskRootedMapOfCodeMark_rootDart_eq_edgeFlip]
  rfl

/-- Helper toward Proposition 5.16. Root alignment changes neither missing
edge status nor the direction predicate on any present edge. -/
theorem diskRootedMapOfCodeMark_missing_eq_stageMissing {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    (diskRootedMapOfCodeMark c k).missing =
      (kmswStageDirectedMap
        (finiteCodeExtend (n := n + 1) c.val) n).missing := rfl

/-- Helper toward Proposition 5.16. The present-edge tail predicate is copied
unchanged from the KMSW stage, preserving every present-edge direction. -/
theorem diskRootedMapOfCodeMark_tail_eq_stageTail {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    (diskRootedMapOfCodeMark c k).tail =
      (kmswStageDirectedMap
        (finiteCodeExtend (n := n + 1) c.val) n).tail := rfl

/-- Helper toward Proposition 5.16. The root dart of the planar finite map
selects the west endpoint of the same sampled geometric edge. -/
theorem diskRootedMapOfCodeMark_rootEndpoint_eq_west {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
        (diskRootedMapOfCodeMark c k).rootDart =
      (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).west
        (kmswDiskRootDart c k).1.val := by
  rw [diskRootedMapOfCodeMark_rootDart_eq_edgeFlip]
  simp [stageEndpoint, edgeFlip, kmswDiskRootDart]

/-- Helper toward Proposition 5.16. Every all-geometric ball is centred at the
west endpoint of the marked edge, including the radius-zero case. -/
theorem diskRootedMapOfCodeMark_ballDarts_eq_west_center {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) :
    rootedLocallyFiniteBallDarts (diskRootedMapOfCodeMark c k) r =
      kmswStageBallDarts (fun _ _ => True)
        (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) r
        ((kmswStage (finiteCodeExtend (n := n + 1) c.val) n).west
          (kmswDiskRootDart c k).1.val) := by
  have hcenter :
      stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
          (edgeFlip _ (kmswDiskRootDart c k)) =
        (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).west
          (kmswDiskRootDart c k).1.val := by
    simp [stageEndpoint, edgeFlip, kmswDiskRootDart]
  simpa only [hcenter] using diskRootedMapOfCodeMark_ballDarts_eq c k r

/-- Helper toward Proposition 5.16. Flipping the sampled dart leaves the
geometric edge index, and hence its conditional uniform edge law, unchanged. -/
theorem kmswDiskRootEdge_uniform_law_eq_flip {ell n : ℕ}
    (hell : 0 < ell) (c : KMSWLeftWalkClass (ell + 1) n) :
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace
      (Fin (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).nextEdge) := ⊤
    Measure.map
        (fun k : Fin ell =>
          (kmswDiskRootDart c (Fin.cast (by omega : ell = (ell + 1) - 1) k)).1)
        (uniformCountingMeasure (Fin ell)) =
      Measure.map
        (fun k : Fin ell =>
          (edgeFlip _ (kmswDiskRootDart c
            (Fin.cast (by omega : ell = (ell + 1) - 1) k))).1)
        (uniformCountingMeasure (Fin ell)) := by
  have hfun :
      (fun k : Fin ell =>
        (kmswDiskRootDart c (Fin.cast (by omega : ell = (ell + 1) - 1) k)).1) =
      (fun k : Fin ell =>
        (edgeFlip _ (kmswDiskRootDart c
          (Fin.cast (by omega : ell = (ell + 1) - 1) k))).1) := by
    funext k
    rfl
  rw [hfun]

/-- Helper toward Proposition 5.16. Every output of the finite sample map
used by `diskRootedPlanarMapLaw` is rooted at the sampled edge's west endpoint.
The law is the push-forward through this sample map by
`diskRootedPlanarMapLaw_toMeasure`. -/
theorem diskRootedPlanarMapOfSample_rootEndpoint_eq_west (n ell : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    stageEndpoint
        (kmswStage (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val) n)
        ((diskRootedPlanarMapOfSample n ell hell p).toRootedLocallyFiniteMap.rootDart) =
      (kmswStage (finiteCodeExtend (n := n + 1)
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val) n).west
        (kmswDiskRootDart
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1)
          (Fin.cast (by omega : ell = (ell + 1) - 1) p.2)).1.val := by
  exact diskRootedMapOfCodeMark_rootEndpoint_eq_west _ _

/-- Helper toward Proposition 5.16. The local topology ball class of each finite law
sample is the local topology image of the corresponding finite faced ball. That faced ball
uses the west endpoint as its centre by
`kmswDiskStageFacedFramedBall` (`KMSWStageFacedFramedBall.lean:16`). -/
theorem diskRootedPlanarMapOfSample_d39BallClass_eq_west_facedClass
    (n ell : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) (r : ℕ) :
    d39BallClass
        (diskRootedPlanarMapOfSample n ell hell p).toD39PlanarRootedMap.toD39RootedMap
        (r + 1) (Nat.succ_pos r) =
      facedFramedBallClassToD39BallClass
        (facedDiskBSBallClass n ell hell (r + 1) (Nat.succ_pos r) p) := by
  rw [d39PlanarRootedMap_ballClass_eq_facedFramedBallClassToD39BallClass]
  exact congrArg facedFramedBallClassToD39BallClass
    (diskRootedPlanarMapOfSample_facedClass_eq n ell hell p r)

end DirectedDistances.PaperProofs.Section5
