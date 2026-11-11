module

public import DirectedDistances.PaperProofs.Section5.DiskBridgeDecoderLaw
public import DirectedDistances.PlanarMap.KMSWStageFramedBall
public import DirectedDistances.PlanarMap.FramedBallCountable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/- Positive-radius disk ball laws for the local topology reading of Definition 3.8.
The finite map-and-mark law is transported through the inverse left KMSW -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk
  DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped ENNReal

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The positive-radius stage ball class, with the ordered missing root retained -/
@[expose] noncomputable def diskStageBSBallClass {ℓ n : ℕ} (r : ℕ) (hr : 0 < r)
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) : FramedBallClass :=
  Quotient.mk FramedBall.setoid (kmswDiskStageFramedBall p.1 p.2 r hr)

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The finite stage-ball class map is measurable for the discrete sample spaces -/
theorem measurable_diskStageBSBallClass (ℓ n r : ℕ) (hr : 0 < r) :
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    Measurable (diskStageBSBallClass (ℓ := ℓ) (n := n) r hr) := by
  classical
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  exact measurable_of_countable _

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The sampled map class and independent mark are sent to the ball of their decoded -/
@[expose] noncomputable def diskBSBallClass (n ell : ℕ) (hell : 0 < ell)
    (r : ℕ) (hr : 0 < r)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) : FramedBallClass :=
  diskStageBSBallClass r hr
    ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1,
      Fin.cast (by omega : ell = (ell + 1) - 1) p.2)

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
Measurability of the ball map from the finite map-and-mark carrier -/
theorem measurable_diskBSBallClass (n ell : ℕ) (hell : 0 < ell)
    (r : ℕ) (hr : 0 < r) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    Measurable (diskBSBallClass n ell hell r hr) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  exact measurable_of_countable _

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
Normalized counting measure on a nonempty finite sample space has total mass one -/
theorem diskBS_uniformCountingMeasure_probability (α : Type*) [Fintype α]
    [MeasurableSpace α] [Nonempty α] :
    IsProbabilityMeasure (uniformCountingMeasure α) := by
  constructor
  change (Fintype.card α : ℝ≥0∞)⁻¹ * Measure.count Set.univ = 1
  have hcount : (Measure.count : Measure α) Set.univ = (Fintype.card α : ℝ≥0∞) := by
    simpa only [Finset.coe_univ, Finset.card_univ] using
      (Measure.count_apply_finset' (α := α) (s := Finset.univ) (by simp))
  rw [hcount]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (by finiteness)

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
Pushforward of the uniform channeled map class and independent uniform missing-edge
The S3 domain ensures that the finite carrier is nonempty. -/
@[expose] noncomputable def diskBSBallLaw (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) : ProbabilityMeasure FramedBallClass := by
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
  exact ⟨((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
    (diskBSBallClass n ell hell r hr), inferInstance⟩

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
Exact pushforward characterization of the probability law on positive-radius ball -/
theorem diskBSBallLaw_toMeasure (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) (hr : 0 < r) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    (diskBSBallLaw n ell hell hle hmod r hr).toMeasure =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
        (diskBSBallClass n ell hell r hr) := rfl

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
Every subset of ball classes has the prescribed finite sample preimage mass -/
theorem diskBSBallLaw_apply (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) (hr : 0 < r)
    (C : Set FramedBallClass) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    (diskBSBallLaw n ell hell hle hmod r hr).toMeasure C =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell)))
        (diskBSBallClass n ell hell r hr ⁻¹' C) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  rw [diskBSBallLaw_toMeasure]
  exact Measure.map_apply (measurable_diskBSBallClass n ell hell r hr)
    MeasurableSpace.measurableSet_top

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The bridge-and-level law gives exactly the same positive-radius ball law after
fallback does not change this equality. -/
theorem bridgeLevelLaw_map_diskBSBallClass (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) :
    (bridgeLevelLaw n ell).map
        (diskBSBallClass n ell hell r hr ∘ diskBridgeDecoder ell n hell hle hmod) =
      (diskBSBallLaw n ell hell hle hmod r hr).toMeasure := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  rw [← Measure.map_map (measurable_diskBSBallClass n ell hell r hr)
    (measurable_diskBridgeDecoder ell n hell hle hmod)]
  rw [bridgeLevelLaw_map_diskBridgeDecoder ell n hell hle hmod]
  exact (diskBSBallLaw_toMeasure n ell hell hle hmod r hr).symm

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
Equivalently the disk ball law samples a uniform admissible walk and an independent -/
theorem diskBSBallLaw_eq_uniform_stage (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) :
    letI : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
    letI : MeasurableSpace (Fin ((ell + 1) - 1)) := ⊤
    (diskBSBallLaw n ell hell hle hmod r hr).toMeasure =
      ((uniformCountingMeasure (KMSWLeftWalkClass (ell + 1) n)).prod
        (uniformCountingMeasure (Fin ((ell + 1) - 1)))).map
          (diskStageBSBallClass r hr) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let f : Q × Fin ell → KMSWLeftWalkClass (ell + 1) n × Fin ((ell + 1) - 1) :=
    fun p => (F.symm p.1, Fin.cast (by omega : ell = (ell + 1) - 1) p.2)
  have hf : Measurable f := measurable_of_countable f
  have hu : ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map f =
      (uniformCountingMeasure (KMSWLeftWalkClass (ell + 1) n)).prod
        (uniformCountingMeasure (Fin ((ell + 1) - 1))) :=
    kmswDiskFiniteSample_uniform_prod (ell + 1) n (by omega)
  rw [diskBSBallLaw_toMeasure, ← hu]
  exact (Measure.map_map
    (measurable_diskStageBSBallClass (ell + 1) n r hr) hf).symm





theorem diskBSBallClass_source_sample (n ell : ℕ) (hell : 0 < ell)
    (r : ℕ) (hr : 0 < r)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
    (k : Fin ell) :
    let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
    let j := Fin.cast (by omega : ell = (ell + 1) - 1) k
    let u := finiteCodeExtend (n := n + 1) c.val
    let B := kmswDiskStageFramedBall c j r hr
    let a := q.val.out.B.leftPath.darts.get
      ⟨k.val, by rw [q.val.out.B.leftPath.darts_length]; omega⟩
    diskBSBallClass n ell hell r hr (q, k) = Quotient.mk FramedBall.setoid B ∧
      ∃ I : DirectedMapWithMissingIso q.val.out.partialMap (kmswStageDirectedMap u n),
        I.toEquiv (q.val.out.partialMap.edgeInv a) = B.frameEdgeDart.1 ∧
        I.toEquiv a = (B.map.edgeInv B.frameEdgeDart).1 ∧
        B.frameOtherDart = some (B.map.edgeInv B.frameEdgeDart) ∧
        B.map.missing B.frameEdgeDart ∧ ¬ B.map.tail B.frameEdgeDart := by
  classical
  dsimp only
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  let j := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let u := finiteCodeExtend (n := n + 1) c.val
  let B := kmswDiskStageFramedBall c j r hr
  let a := q.val.out.B.leftPath.darts.get
    ⟨k.val, by rw [q.val.out.B.leftPath.darts_length]; omega⟩
  obtain ⟨I⟩ := kmswDiskFiniteSample_partialMapIso (ell + 1) n (by omega) q
  have ha : I.toEquiv a = kmswDiskRootDart c j :=
    iso_leftPathDart_eq_rootDart (by omega) c q I j
  have hother : (B.map.edgeInv B.frameEdgeDart).1 = kmswDiskRootDart c j :=
    (kmswStageDirectedMap u n).edgeInv_invol (kmswDiskRootDart c j)
  have hroot := kmswDiskStageFramedBall_root_spec c j r hr
  refine ⟨rfl, I, ?_, ha.trans hother.symm, hroot.2.2.1,
    B.frameEdge_missing, hroot.2.2.2.2.2.1⟩
  exact (I.edgeInv_comm a).trans (congrArg (kmswStageDirectedMap u n).edgeInv ha)

end DirectedDistances.PaperProofs.Section5
