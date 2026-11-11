module

public import DirectedDistances.PaperProofs.Section5.Prop59FiniteReflectionGrade
public import DirectedDistances.PlanarMap.D39RootedMapQuotient
public import DirectedDistances.PlanarMap.D39RootedPlanarBallGenusZero

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory

/-! These declarations identify the actual reflection of each finite rooted sample
with the sample indexed by the reversed finite mirror parameter. The KMSW grade
is `n - 1`, encoded by the total edge count `n + (ell + 1)` on both sides. -/

/-- Helper toward Proposition 5.9. The local topology combinatorial class of the actual
geometric reflection of a finite rooted sample is the class of the rooted
sample indexed by the mirrored KMSW class and reversed mark. -/
theorem diskRootedPlanarSampleMirror_d39PlanarClass_eq
    (n ell : ℕ) (hell : 0 < ell)
    (p : Prop59LeftFiniteClass n ell × Fin ell) :
    Quotient.mk D39PlanarRootedMap.setoid
        ((mirrorRootedLocallyFinitePlanarMap
          (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap) =
      Quotient.mk D39PlanarRootedMap.setoid
        ((diskRootedPlanarMapOfMirroredSample n ell hell p).toD39PlanarRootedMap) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let c := F.symm p.1
  let k : Fin ((ell + 1) - 1) := Fin.cast (by omega) p.2
  let c' := F.symm (kmswMirrorSymmetryEquiv (ell + 1) (n + (ell + 1)) (by omega) p.1)
  let k' : Fin ((ell + 1) - 1) := Fin.cast (by omega) (Fin.rev p.2)
  have hc : kmswWalkMirrorEquiv (ell + 1) n (by omega) c = c' := by
    simp only [kmswWalkMirrorEquiv, Equiv.trans_apply, c, c', F,
      Equiv.apply_symm_apply]
  have hk : Fin.rev k = k' := by
    apply Fin.ext
    simp only [k, k', Fin.rev, Fin.val_cast]
    omega
  have hid := rootedStage_walkMirror (by omega : 2 ≤ ell + 1) c k
  rw [hc, hk] at hid
  let A := kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n
  let B := kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c'.val) n
  obtain ⟨I, hi⟩ := (DirectedMapWithMissing.toRootedClass_eq_iff B
    (kmswDiskRootDart c' k') A.mirror (A.edgeInv (kmswDiskRootDart c k))).mp hid
  let M := mirrorRootedLocallyFinitePlanarMap (diskRootedPlanarMapOfCodeMark c k)
  let N := diskRootedPlanarMapOfCodeMark c' k'
  have hframe : I.toEquiv.symm M.frameEdgeDart = N.frameEdgeDart := by
    apply I.toEquiv.injective
    change I.toEquiv (I.toEquiv.symm (A.edgeInv (A.edgeInv (kmswDiskRootDart c k)))) =
      I.toEquiv (B.edgeInv (kmswDiskRootDart c' k'))
    rw [Equiv.apply_symm_apply, I.edgeInv_comm, hi, A.edgeInv_invol]
    rfl
  have hclass :
      Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap =
        Quotient.mk D39PlanarRootedMap.setoid N.toD39PlanarRootedMap := by
    apply Quotient.sound
    refine ⟨{
      toEquiv := I.toEquiv.symm
      rot_comm := I.symm.rot_comm
      edgeInv_comm := I.symm.edgeInv_comm
      missing_iff := I.symm.missing_iff
      tail_iff := fun d _ => I.symm.tail_iff d
      root_dart_comm := ?_ }⟩
    change I.toEquiv.symm M.frameEdgeDart = N.frameEdgeDart
    exact hframe
  change Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap =
      Quotient.mk D39PlanarRootedMap.setoid N.toD39PlanarRootedMap at hclass
  simpa [M, N, diskRootedPlanarMapOfMirroredSample,
    diskRootedPlanarSampleMirror, diskRootedPlanarMapOfSample,
    diskRootedPlanarMapOfCodeMark, F, c, k, c', k'] using hclass

/-- Helper toward Proposition 5.9. The law of the reflected finite rooted
sample, viewed in the local topology combinatorial class space, equals the law of the
finite sample indexed by the reversed mirror parameter. -/
theorem diskRootedPlanarSampleMirror_d39PlanarClass_law
    (n ell : ℕ) (hell : 0 < ell) :
    let Q := Prop59LeftFiniteClass n ell
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace (Quotient D39PlanarRootedMap.setoid) := ⊤
    let μ := (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))
    μ.map (fun p => Quotient.mk D39PlanarRootedMap.setoid
        ((mirrorRootedLocallyFinitePlanarMap
          (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap)) =
      μ.map (fun p => Quotient.mk D39PlanarRootedMap.setoid
        ((diskRootedPlanarMapOfSample n ell hell p).toD39PlanarRootedMap)) := by
  classical
  let Q := Prop59LeftFiniteClass n ell
  letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
  letI : MeasurableSpace Q := ⊤
  letI : MeasurableSpace (Fin ell) := ⊤
  letI : MeasurableSpace (Quotient D39PlanarRootedMap.setoid) := ⊤
  let μ := (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))
  have hpoint :
      (fun p => Quotient.mk D39PlanarRootedMap.setoid
        ((mirrorRootedLocallyFinitePlanarMap
          (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap)) =
      (fun p => Quotient.mk D39PlanarRootedMap.setoid
        ((diskRootedPlanarMapOfSample n ell hell
          (diskRootedPlanarSampleMirror n ell hell p)).toD39PlanarRootedMap)) := by
    funext p
    simpa only [diskRootedPlanarMapOfMirroredSample] using
      diskRootedPlanarSampleMirror_d39PlanarClass_eq n ell hell p
  rw [hpoint]
  have hmirror := diskRootedPlanarSampleMirror_uniform n ell hell
  have hmap := congrArg (fun ν : Measure (Q × Fin ell) =>
    ν.map (fun p => Quotient.mk D39PlanarRootedMap.setoid
      ((diskRootedPlanarMapOfSample n ell hell p).toD39PlanarRootedMap))) hmirror
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hmap
  exact hmap



























end DirectedDistances.PaperProofs.Section5
