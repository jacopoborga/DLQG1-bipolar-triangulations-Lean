module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTFacedBallLaw
public import DirectedDistances.PlanarMap.KMSWStageFacedFramedBall
public import DirectedDistances.PaperProofs.Section5.DiskWindowDartTransport
import all DirectedDistances.PaperProofs.Section5.UIBHBOTFacedBallLaw
import all DirectedDistances.PaperProofs.Section5.DiskWindowDartTransport
import all DirectedDistances.PlanarMap.KMSWStageFramedBall
import all DirectedDistances.PaperProofs.Section5.DiskWindowFramedIso
import all DirectedDistances.PaperProofs.Section5.Prop516Assembly
import all DirectedDistances.PaperProofs.Section5.UIBHBOTWindowClassCompare

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology symmDiff

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def facedDiskStageBSBallClass {ℓ n : ℕ} (r : ℕ) (hr : 0 < r)
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) : FacedFramedBallClass :=
  Quotient.mk FacedFramedBall.setoid (kmswDiskStageFacedFramedBall p.1 p.2 r hr)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskStageBSBallClass_forget {ℓ n : ℕ} (r : ℕ) (hr : 0 < r)
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) :
    (facedDiskStageBSBallClass r hr p).forget = diskStageBSBallClass r hr p := rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def facedDiskBSBallClass (n ell : ℕ) (hell : 0 < ell)
    (r : ℕ) (hr : 0 < r)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) : FacedFramedBallClass :=
  facedDiskStageBSBallClass r hr
    ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1,
      Fin.cast (by omega : ell = (ell + 1) - 1) p.2)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskBSBallClass_forget (n ell : ℕ) (hell : 0 < ell)
    (r : ℕ) (hr : 0 < r)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    (facedDiskBSBallClass n ell hell r hr p).forget =
      diskBSBallClass n ell hell r hr p := rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem measurable_facedDiskBSBallClass (n ell : ℕ) (hell : 0 < ell)
    (r : ℕ) (hr : 0 < r) :
    let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    Measurable (facedDiskBSBallClass n ell hell r hr) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  exact measurable_of_countable _

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def facedDiskBSBallLaw (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) : ProbabilityMeasure FacedFramedBallClass := by
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
    (facedDiskBSBallClass n ell hell r hr), inferInstance⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskBSBallLaw_forget (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) (hr : 0 < r) :
    (facedDiskBSBallLaw n ell hell hle hmod r hr).map FacedFramedBallClass.forget =
      diskBSBallLaw n ell hell hle hmod r hr := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  apply Subtype.ext
  change (((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
    (facedDiskBSBallClass n ell hell r hr)).map FacedFramedBallClass.forget = _
  rw [Measure.map_map measurable_facedFramedBallClass_forget
    (measurable_facedDiskBSBallClass n ell hell r hr)]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem bridgeLevelLaw_map_facedDiskBSBallClass (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) :
    (bridgeLevelLaw n ell).map
        (facedDiskBSBallClass n ell hell r hr ∘ diskBridgeDecoder ell n hell hle hmod) =
      (facedDiskBSBallLaw n ell hell hle hmod r hr).toMeasure := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  rw [← Measure.map_map (measurable_facedDiskBSBallClass n ell hell r hr)
    (measurable_diskBridgeDecoder ell n hell hle hmod)]
  rw [bridgeLevelLaw_map_diskBridgeDecoder ell n hell hle hmod]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def facedUIBHBOTWindowStageBallClass (N r : ℕ)
    (u : ℕ → Fin 3) : FacedFramedBallClass :=
  facedUIBHBOTStageDataBallClassRel
    ⟨kmswStage u (2 * N), kmswStageDirectedMap u (2 * N)⟩
    r (kmswLLCreatedEdge u N) true

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def facedUIBHBOTDecodedWindowBallClass (N r : ℕ)
    (x : Fin (2 * N + 1) → ℤ × ℤ) : FacedFramedBallClass :=
  facedUIBHBOTWindowStageBallClass N r (windowCodeDecode N x)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTWindowStageBallClass_eq_prefix (N r : ℕ) (u v : ℕ → Fin 3)
    (h : ∀ i < 2 * N, u i = v i) :
    facedUIBHBOTWindowStageBallClass N r u =
      facedUIBHBOTWindowStageBallClass N r v := by
  have he : kmswLLCreatedEdge u N = kmswLLCreatedEdge v N := by
    unfold kmswLLCreatedEdge
    rw [kmswStage_congr (fun i hi => h i (by omega))]
  unfold facedUIBHBOTWindowStageBallClass
  rw [he]
  exact congrArg (fun p => facedUIBHBOTStageDataBallClassRel p r _ true)
    (relStageMap_data_eq u v (2 * N) h)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem measurable_facedUIBHBOTWindowStageBallClass (N r : ℕ) :
    Measurable (facedUIBHBOTWindowStageBallClass N r) :=
  measurable_of_factors_prefix (2 * N) _
    (facedUIBHBOTWindowStageBallClass_eq_prefix N r)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem measurable_facedUIBHBOTDecodedWindowBallClass (N r : ℕ) :
    Measurable (facedUIBHBOTDecodedWindowBallClass N r) :=
  (measurable_facedUIBHBOTWindowStageBallClass N r).comp (measurable_windowCodeDecode N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTBallClassRel_eq_windowStageClass (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N r : ℕ) (hr : 0 < r)
    (hcap : ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream W N) N) true) :
    facedUIBHBOTBallClassRel W r hr =
      facedUIBHBOTWindowStageBallClass N r (shiftedStream W N) := by
  obtain ⟨c, hc⟩ := hcap
  obtain ⟨C, hN, hm, _, he, hb⟩ :=
    (uibhbotFixedCaptureRel_iff W r N (2 * N) c _ true).mp hc
  rw [facedUIBHBOTBallClassRel_eq_capture W H r hr C, C.facedClass_eq_stageData hr]
  rw [he, hb]
  unfold facedUIBHBOTWindowStageBallClass
  have hs : shiftedStream W C.N = shiftedStream W N := congrArg _ hN
  rw [hs, hm]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTDecodedWindowBallClass_concat (N r : ℕ)
    (w : ℤ → List (Fin 3)) (hw : ∀ k, IsStoppedExcursionWord (w k)) :
    facedUIBHBOTDecodedWindowBallClass N r
      (fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N)) =
      facedUIBHBOTWindowStageBallClass N r
        (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) :=
  facedUIBHBOTWindowStageBallClass_eq_prefix N r _ _
    (windowCodeDecode_uibhbotConcatWalk N w hw)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskStage_original_iff_orbit {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r)
    (d : (kmswDiskStageFacedFramedBall c k r hr).toFramedBall.D) :
    d ∈ (kmswDiskStageFacedFramedBall c k r hr).original ↔
      ∀ e, (kmswMap (finiteCodeExtend (n := n + 1) c.val) n).faceSucc.SameCycle
        d.1 e → e ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) r
          (stageEndpoint _ (edgeFlip _ (kmswDiskRootDart c k))) := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u n) r
    (stageEndpoint _ (edgeFlip _ (kmswDiskRootDart c k)))
  rw [kmswDiskStageFacedFramedBall_original_iff]
  constructor
  · intro h e he
    obtain ⟨j, rfl⟩ := he.exists_nat_pow_eq
    rw [kmswStageBallDarts_mem_iff]
    refine ⟨h j, ?_⟩
    have hn := h (j + 1)
    rw [pow_succ', Equiv.Perm.mul_apply, kmswStage_faceSucc_endpoint] at hn
    exact hn
  · intro h j
    have he := h (((kmswMap u n).faceSucc ^ j) d.1)
      ⟨(j : ℤ), by simp only [zpow_natCast]; rfl⟩
    exact ((kmswStageBallDarts_mem_iff _ _ _ _ _).mp he).1

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindow_endpoint_originalFace_iff
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    let a := activeInitial u N
    ∀ d : StageDart (kmswStage (fun i => w (s + i)) (2 * N)).nextEdge,
      (∀ e, (kmswMap (fun i => w (s + i)) (2 * N)).faceSucc.SameCycle d e →
        e ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (fun i => w (s + i)) (2 * N)) r a) ↔
      (∀ e, (kmswMap w (s + 2 * N)).faceSucc.SameCycle
        (kmswWindowDartMap w s (2 * N) d) e →
        e ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w (s + 2 * N)) r
          (kmswWindowPatchVertexMap w s (2 * N) a)) := by
  classical
  dsimp only
  let w := fun i => p.1 (i + 1)
  let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
  let a := activeInitial (windowCodeDecode N x) N
  let S := kmswStageBallDarts (fun _ _ => True)
    (kmswStage (fun i => w (s + i)) (2 * N)) r a
  let T := kmswStageBallDarts (fun _ _ => True) (kmswStage w (s + 2 * N)) r
    (kmswWindowPatchVertexMap w s (2 * N) a)
  let f := kmswWindowDartMap w s (2 * N)
  obtain ⟨E, hE⟩ := diskWindowClass_endpoint_darts_equiv h hev hnd
  have hb : Set.BijOn f (↑S) (↑T) := by
    refine ⟨?_, (kmswWindowDartMap_injective w s (2 * N)).injOn, ?_⟩
    · intro d hd
      have he := (E ⟨d, hd⟩).2
      rw [hE] at he
      exact he
    · intro e he
      let d := E.symm ⟨e, he⟩
      refine ⟨d.1, d.2, ?_⟩
      have hd := hE d
      rw [Equiv.apply_symm_apply] at hd
      exact hd.symm
  intro d
  apply retainedOrbit_transport _ _ (↑S) (↑T) f
    (kmswWindowDartMap_injective w s (2 * N)) hb
  intro e he
  have hd := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp he
  exact ((transport_structure h hev hnd).2.2.2 e hd.1 hd.2).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindow_valid {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindow_stage_originalFace_iff
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    let ht := (facedDiskWindow_valid h).2
    ∀ d : StageDart (kmswStage w (T + N)).nextEdge,
      (∀ e, (kmswMap w (T + N)).faceSucc.SameCycle d e →
        e ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T)) ↔
      (∀ e, (kmswMap w n).faceSucc.SameCycle
        (outerSucc_castDart (kmswStage_nextEdge_mono w ht) d) e →
        e ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T)) := by
  classical
  dsimp only
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let w := fun i => p.1 (i + 1)
  have ht : T + N ≤ n := (facedDiskWindow_valid h).2
  let f := outerSucc_castDart (kmswStage_nextEdge_mono w ht)
  let S := kmswStageBallDarts (fun _ _ => True) (kmswStage w (T + N)) r
    (activeInitial w T)
  let U := kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r (activeInitial w T)
  have hf : Function.Injective f := by
    intro a b hab
    apply Prod.ext
    · exact Fin.ext (congrArg (fun d => d.1.val) hab)
    · exact congrArg (fun z : StageDart (kmswStage w n).nextEdge => z.2) hab
  obtain ⟨E, hE⟩ := diskWindowClass_stage_darts_equiv h hev hnd
  have he (d : S) : (E d).1 = f d.1 := by
    apply Prod.ext
    · exact Fin.ext (hE d).1
    · exact (hE d).2
  have hb : Set.BijOn f (↑S) (↑U) := by
    refine ⟨?_, hf.injOn, ?_⟩
    · intro d hd
      have hd' := (E ⟨d, hd⟩).2
      rw [he] at hd'
      exact hd'
    · intro e he'
      let d := E.symm ⟨e, he'⟩
      refine ⟨d.1, d.2, ?_⟩
      have hd := he d
      rw [Equiv.apply_symm_apply] at hd
      exact hd.symm
  intro d
  apply retainedOrbit_transport _ _ (↑S) (↑U) f hf hb
  intro e he'
  have hd := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp he'
  have hv : stageEndpoint (kmswStage w (T + N))
      ((kmswMap w (T + N)).faceSucc e) ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage w (T + N)) r
        (activeInitial w T) := by
    rw [kmswStage_faceSucc_endpoint]
    exact hd.2
  apply (stageRot w n).injective
  change stageRot w n (f ((kmswMap w (T + N)).faceSucc e)) =
    (kmswMap w n).rot ((kmswMap w n).rot.symm (edgeFlip _ (f e)))
  rw [Equiv.apply_symm_apply]
  rw [diskWindowClass_stage_rotation h hev hnd n ht _ hv]
  change f ((stageRot w (T + N))
    ((stageRot w (T + N)).symm (edgeFlip _ e))) = edgeFlip _ (f e)
  rw [Equiv.apply_symm_apply]
  rfl

private theorem orbit_data_eq {s t : State}
    (M : DirectedMapWithMissing (StageDart s.nextEdge))
    (Q : DirectedMapWithMissing (StageDart t.nextEdge))
    (h : (⟨s, M⟩ : Σ s : State, DirectedMapWithMissing (StageDart s.nextEdge)) =
      ⟨t, Q⟩) (r c : ℕ) (d : StageDart s.nextEdge) (e : StageDart t.nextEdge)
    (hid : e.1.val = d.1.val) (hside : e.2 = d.2) :
    (∀ x, M.faceSucc.SameCycle d x →
      x ∈ kmswStageBallDarts (fun _ _ => True) s r c) ↔
    (∀ x, Q.faceSucc.SameCycle e x →
      x ∈ kmswStageBallDarts (fun _ _ => True) t r c) := by
  have hs : s = t := congrArg Sigma.fst h
  cases hs
  have hM : M = Q := eq_of_heq (Sigma.mk.inj h).2
  cases hM
  have he : e = d := Prod.ext (Fin.ext hid) hside
  cases he
  rfl

private theorem orbit_prefix (u v : ℕ → Fin 3) (m r c : ℕ)
    (h : ∀ i < m, u i = v i)
    (d : StageDart (kmswStage u m).nextEdge)
    (e : StageDart (kmswStage v m).nextEdge)
    (hid : e.1.val = d.1.val) (hside : e.2 = d.2) :
    (∀ x, (kmswMap u m).faceSucc.SameCycle d x →
      x ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage u m) r c) ↔
    (∀ x, (kmswMap v m).faceSucc.SameCycle e x →
      x ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage v m) r c) :=
  orbit_data_eq _ _ (transport_stage_data_eq u v m h) r c d e hid hside

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindow_orbit_transport
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let s := T - N
    let a := activeInitial u N
    let b := activeInitial w T
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage u (2 * N)) r a ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r b,
      (∀ z, (e z).1.1.val = (kmswWindowPatchData w s (2 * N)).φ z.1.1.val) ∧
      (∀ z, (e z).1.2 = z.1.2) ∧
      (∀ z, (∀ q, (kmswMap u (2 * N)).faceSucc.SameCycle z.1 q →
        q ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage u (2 * N)) r a) ↔
        (∀ q, (kmswMap w n).faceSucc.SameCycle (e z).1 q →
          q ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r b)) := by
  classical
  dsimp only
  let u := windowCodeDecode N x
  let w := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let a := activeInitial u N
  let b := activeInitial w T
  have hvalid := facedDiskWindow_valid h
  have hsm : s + m = T + N := by dsimp only [s, m]; omega
  have hsN : s + N = T := by dsimp only [s]; omega
  have hcode (i : ℕ) (hi : i < m) : w (s + i) = u i :=
    (windowCodeDecode_bridge h i hi).symm
  have hroot : kmswWindowPatchVertexMap w s m a = b := by
    have hstageN : kmswStage (fun i => w (s + i)) N = kmswStage u N :=
      kmswStage_congr (fun i hi => hcode i (by dsimp only [m]; omega))
    have hbound : a < (kmswStage (fun i => w (s + i)) N).nextVertex := by
      rw [hstageN]
      change activeInitial u N < _
      rw [CutConverse.activeInitial_eq]
      exact (kmswStage_endpoints_lt_nextVertex u N (kmswStage u N).active
        (kmswStage_boundary_ids_lt_nextEdge u N).1).1
    calc
      kmswWindowPatchVertexMap w s m a = kmswWindowPatchVertexMap w s N a :=
        kmswWindowPatchVertexMap_extends_le w s N m (by dsimp only [m]; omega) a hbound
      _ = activeInitial w (s + N) := kmswWindowPatchVertexMap_activeInitial u w s N
        (fun i hi => hcode i (by dsimp only [m]; omega))
      _ = b := by rw [hsN]
  obtain ⟨e0, h0id, h0side, _⟩ :=
    transport_prefix_ball u (fun i => w (s + i)) m r a (fun i hi => (hcode i hi).symm)
  have he1 := transport_endpoint_iso h hev hnd
  dsimp only at he1
  rw [hsm, hroot] at he1
  obtain ⟨e1, h1id, h1side, _⟩ := he1
  obtain ⟨e2, h2⟩ := diskWindowClass_stage_darts_equiv h hev hnd
  have h2id (z) : (e2 z).1.1.val = z.1.1.val := (h2 z).1
  have h2side (z) : (e2 z).1.2 = z.1.2 := (h2 z).2
  let e := e0.trans (e1.trans e2)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro z
    change (e2 (e1 (e0 z))).1.1.val = _
    rw [h2id, h1id, h0id]
  · intro z
    change (e2 (e1 (e0 z))).1.2 = _
    rw [h2side, h1side, h0side]
  · intro z
    have h0 := orbit_prefix u (fun i => w (s + i)) m r a
      (fun i hi => (hcode i hi).symm) z.1 (e0 z).1 (h0id z) (h0side z)
    have h1o := facedDiskWindow_endpoint_originalFace_iff h hev hnd (e0 z).1
    dsimp only at h1o
    rw [hroot] at h1o
    have hdata := congrArg (fun j =>
      (⟨kmswStage w j, kmswStageDirectedMap w j⟩ :
        Σ s : State, DirectedMapWithMissing (StageDart s.nextEdge))) hsm
    have h1o' := orbit_data_eq _ _ hdata r b
      (kmswWindowDartMap w s m (e0 z).1) (e1 (e0 z)).1
      (h1id (e0 z)) (h1side (e0 z))
    have h2o := facedDiskWindow_stage_originalFace_iff h hev hnd (e1 (e0 z)).1
    have hh : outerSucc_castDart (kmswStage_nextEdge_mono w hvalid.2)
        (e1 (e0 z)).1 = (e2 (e1 (e0 z))).1 := by
      apply Prod.ext
      · exact Fin.ext (h2id _).symm
      · exact (h2side _).symm
    rw [hh] at h2o
    exact h0.trans (h1o.trans (h1o'.trans h2o))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def facedStageBallAtMissingDart (u : ℕ → Fin 3) (m r : ℕ)
    (hr : 0 < r) (d : StageDart (kmswStage u m).nextEdge)
    (hm : (kmswStageDirectedMap u m).missing d) : FacedFramedBall :=
  uibhbotInducedLocalFacedBallRel (kmswStageDirectedMap u m)
    (kmswStageBallDarts (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d)))
    (fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
      (kmswStage u m) r (stageEndpoint (kmswStage u m) (edgeFlip _ d)) e).mp he)
    (kmswMap_isPlanar u m)
    (kmswStageBallCombinatorialMap_rooted_isConnected u m r d hr)
    ⟨d, (kmswStageBallRootEdge_mem u m r d hr).1⟩ hm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedStageDataBallClass_eq_localFrame (u : ℕ → Fin 3) (m r : ℕ)
    (hr : 0 < r) (d : StageDart (kmswStage u m).nextEdge)
    (hm : (kmswStageDirectedMap u m).missing d) :
    let M := kmswStageDirectedMap u m
    let S := kmswStageBallDarts (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d))
    let hf := fun e he => (kmswStageBallDarts_edgeFlip
      (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d)) e).mp he
    facedUIBHBOTStageDataBallClassRel ⟨kmswStage u m, M⟩ r d.1.val d.2 =
      Quotient.mk FacedFramedBall.setoid
        (uibhbotInducedLocalFacedBallRel M S hf (kmswMap_isPlanar u m)
          (kmswStageBallCombinatorialMap_rooted_isConnected u m r d hr)
          ⟨d, (kmswStageBallRootEdge_mem u m r d hr).1⟩ hm) := by
  classical
  dsimp only
  unfold facedUIBHBOTStageDataBallClassRel
  rw [dite_eq_left d.1.isLt]
  dsimp only
  have hd : ((⟨d.1.val, d.1.isLt⟩, d.2) : StageDart _) = d := rfl
  simp only [hd]
  rw [dite_eq_left, dite_eq_left]
  · rfl
  · exact ⟨kmswMap_isPlanar u m,
      kmswStageBallCombinatorialMap_rooted_isConnected u m r d hr,
      (kmswStageBallRootEdge_mem u m r d hr).1, hm⟩
  · intro e he
    exact (kmswStageBallDarts_edgeFlip (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d)) e).mp he

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskBSBallClass_decoder_eq_prefix_stage
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell) :
    facedDiskBSBallClass n ell hell r hr
        (diskBridgeDecoder ell n (by omega) hle hmod p) =
      facedDiskStageBSBallClass r hr
        (⟨diskBridgePrefix n p,
            diskBridgePrefix_admissible_of_cone ell n p hp⟩,
          Fin.cast (by omega : ell = (ell + 1) - 1)
            ⟨p.2 - 1, by omega⟩) := by
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let c : KMSWLeftWalkClass (ell + 1) n :=
    ⟨diskBridgePrefix n p, diskBridgePrefix_admissible_of_cone ell n p hp⟩
  rw [diskBridgeDecoder_eq_on_cone_support ell n (by omega) hle hmod p hp hlo hhi]
  change Quotient.mk FacedFramedBall.setoid
      (kmswDiskStageFacedFramedBall (F.symm (F c))
        (Fin.cast (by omega : ell = (ell + 1) - 1) ⟨p.2 - 1, by omega⟩)
        r hr) =
    Quotient.mk FacedFramedBall.setoid
      (kmswDiskStageFacedFramedBall c
        (Fin.cast (by omega : ell = (ell + 1) - 1) ⟨p.2 - 1, by omega⟩)
        r hr)
  rw [F.symm_apply_apply]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindow_class_eq_on_support
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r) (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell)
    (x : Fin (2 * N + 1) → ℤ × ℤ)
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    facedDiskBSBallClass n ell hell r hr (diskBridgeDecoder ell n hell hle hmod p) =
      facedUIBHBOTDecodedWindowBallClass N r x := by
  let c : KMSWLeftWalkClass (ell + 1) n :=
    ⟨diskBridgePrefix n p, diskBridgePrefix_admissible_of_cone ell n p hp⟩
  let k : Fin ell := ⟨p.2 - 1, by omega⟩
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let u := windowCodeDecode N x
  have hc : ∀ i : Fin n, c.val i = p.1 (i.val + 1) := diskBridgePrefix_apply n p
  have hk : k.val + 1 = p.2 := by dsimp [k]; omega
  have hrec := decodedWindow_central_record hp hlo hhi h
  obtain ⟨d, hde, hdb, hdm, hdo, hcenter⟩ := framedRootData_of_record u N (2 * N)
    (framedCapture_window_pos hev) (by omega) hrec
  let B := kmswDiskStageFramedBall c kc r hr
  let C := framedStageBallAtMissingDart u (2 * N) r hr d hdm
  obtain ⟨e, heId, heSide, hrot, hflip, hmissing, htail⟩ :=
    diskWindowFramedDartTransport_holds n ell N K0 r hr p c hc k hk x h hev hnd d hde hdb hdm
  have hC : C.rootDart = C.frameEdgeDart ∧
      C.frameOtherDart = some (C.map.edgeInv C.frameEdgeDart) ∧
      C.map.IsOuter (C.map.edgeInv C.frameEdgeDart) := by
    exact inducedLocalFramedBall_orderedFrame _ _ _ _ _ _ hdm hdo
  have hframe : e C.frameEdgeDart = B.frameEdgeDart := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      calc
        (e C.frameEdgeDart).1.1.val =
            (kmswWindowPatchData (finiteCodeExtend (n := n + 1) c.val)
              ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)).φ
                C.frameEdgeDart.1.1.val := heId _
        _ = kmswLLCreatedEdge (finiteCodeExtend (n := n + 1) c.val)
            (kmswDiskFirstHit c kc) := by
          change (kmswWindowPatchData (finiteCodeExtend (n := n + 1) c.val)
            ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)).φ d.1.val = _
          rw [hde]
          exact diskFrame_decoded_createdEdge_map p c hc k hk h hev
        _ = B.frameEdgeDart.1.1.val := rfl
    · rw [heSide]
      change Bool.not d.2 = Bool.not true
      exact congrArg Bool.not hdb
  have hBouter : B.map.IsOuter (B.map.edgeInv B.frameEdgeDart) := by
    rw [← diskStageFramedBall_outer_frame c kc r hr]
    exact Equiv.Perm.SameCycle.rfl
  let I := framedBallIso_of_orderedFrame C B e hrot hflip hmissing htail hframe
    hC.1 rfl hC.2.1 (kmswDiskStageFramedBall_root_spec c kc r hr).2.2.1
    hC.2.2 hBouter
  let BF := kmswDiskStageFacedFramedBall c kc r hr
  let CF := facedStageBallAtMissingDart u (2 * N) r hr d hdm
  have hvalid := facedDiskWindow_valid h
  let w := fun i => p.1 (i + 1)
  let v := finiteCodeExtend (n := n + 1) c.val
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let a := activeInitial u N
  let b := activeInitial w T
  have hprefix (i : ℕ) (hi : i < n) : v i = w i := by
    change (if ht : i < n + 1 - 1 then c.val ⟨i, ht⟩ else 0) = _
    rw [dite_eq_left (by omega : i < n + 1 - 1)]
    exact hc ⟨i, hi⟩
  have hT : kmswDiskFirstHit c kc = T :=
    kmswDiskFirstHit_eq_codeFstFirstHit_toNat ell n p c hc k hk
  have hBcenter : stageEndpoint (kmswStage v n)
      (edgeFlip _ (kmswDiskRootDart c kc)) = b := by
    change (kmswStage v n).west (kmswLLCreatedEdge v (kmswDiskFirstHit c kc)) = b
    rw [(kmswDiskRootEdge_endpoints c kc).1, hT]
    exact activeInitial_congr (fun i hi => hprefix i (by omega))
  obtain ⟨E, hEid, hEside, hEface⟩ := facedDiskWindow_orbit_transport h hev hnd
  have hpatch := transport_patch_prefix v w s (2 * N)
    (fun i hi => hprefix i (by omega))
  let J : FacedFramedBallIso CF BF := ⟨I, by
    intro z
    rw [facedDiskStage_original_iff_orbit]
    change (∀ q, (kmswMap v n).faceSucc.SameCycle (e z).1 q →
      q ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage v n) r
        (stageEndpoint (kmswStage v n) (edgeFlip _ (kmswDiskRootDart c kc)))) ↔
      ∀ q, (kmswMap u (2 * N)).faceSucc.SameCycle z.1 q →
        q ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage u (2 * N)) r
          (stageEndpoint (kmswStage u (2 * N)) (edgeFlip _ d))
    conv_lhs =>
      intro q
      rhs
      rw [hBcenter]
    conv_rhs =>
      intro q
      rhs
      rw [hcenter]
    let z' : KMSWStageBallDart (fun _ _ => True) (kmswStage u (2 * N)) r a :=
      ⟨z.1, by simpa only [hcenter] using z.2⟩
    have hid : (E z').1.1.val = (e z).1.1.val := by
      calc
        (E z').1.1.val =
            (kmswWindowPatchData w s (2 * N)).φ z'.1.1.val := hEid z'
        _ = (kmswWindowPatchData v s (2 * N)).φ z.1.1.val := by rw [hpatch]
        _ = (e z).1.1.val := (heId z).symm
    have hside : (E z').1.2 = (e z).1.2 := (hEside z').trans (heSide z).symm
    exact (orbit_prefix v w n r b hprefix (e z).1 (E z').1 hid hside).trans
      (hEface z').symm⟩
  rw [facedDiskBSBallClass_decoder_eq_prefix_stage n ell hell hle hmod r hr p hp hlo hhi]
  change Quotient.mk FacedFramedBall.setoid BF =
    facedUIBHBOTStageDataBallClassRel
      ⟨kmswStage u (2 * N), kmswStageDirectedMap u (2 * N)⟩ r
      (kmswLLCreatedEdge u N) true
  rw [← hde, ← hdb,
    facedStageDataBallClass_eq_localFrame u (2 * N) r hr d hdm]
  exact Quotient.sound ⟨J.symm⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindow_class_eq_on_capture
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r) :
    ∀ᵐ p ∂bridgeLevelLaw n ell, ∀ x,
      bridgeOptionWindow n N p = some x →
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) →
      ¬ DiskDip N K0 p →
      facedDiskBSBallClass n ell hell r hr (diskBridgeDecoder ell n hell hle hmod p) =
        facedUIBHBOTDecodedWindowBallClass N r x := by
  filter_upwards [framedBridge_ae_support ell n] with p hp
  intro x h hev hnd
  exact facedDiskWindow_class_eq_on_support n ell hell hle hmod N K0 r hr p
    hp.1 hp.2.1 hp.2.2 x h hev hnd

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def facedUIBHBOTWindowClassLaw (N r : ℕ) : Measure FacedFramedBallClass :=
  ((uibhbotEncodingWindowLaw N).map (windowCodeDecode N)).map
    (facedUIBHBOTWindowStageBallClass N r)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTWindowClassLaw_eq_map (N r : ℕ) :
    facedUIBHBOTWindowClassLaw N r =
      (uibhbotEncodingWindowLaw N).map (facedUIBHBOTDecodedWindowBallClass N r) := by
  exact Measure.map_map (measurable_facedUIBHBOTWindowStageBallClass N r)
    (measurable_windowCodeDecode N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTWindowClassLaw_eq_code_map (N r : ℕ) :
    facedUIBHBOTWindowClassLaw N r =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun W => facedUIBHBOTWindowStageBallClass N r (shiftedStream W N)) := by
  rw [facedUIBHBOTWindowClassLaw_eq_map, uibhbotEncodingWindowLaw,
    AEMeasurable.map_map_of_aemeasurable
      (measurable_facedUIBHBOTDecodedWindowBallClass N r).aemeasurable
      (aemeasurable_windowFromWords N)]
  change _ = (uibhbotWordFamilyLaw.map uibhbotCodeWordRel).map _
  have hg : Measurable (fun W : ℤ → Fin 3 =>
      facedUIBHBOTWindowStageBallClass N r (shiftedStream W N)) :=
    (measurable_facedUIBHBOTWindowStageBallClass N r).comp (measurable_windowShift N)
  rw [Measure.map_map hg measurable_uibhbotCodeWordRel]
  apply Measure.map_congr
  filter_upwards [uibhbotWordFamilyLaw_ae_certifiedRootCapture] with w hw
  obtain ⟨hw, _, _⟩ := hw
  change facedUIBHBOTDecodedWindowBallClass N r _ =
    facedUIBHBOTWindowStageBallClass N r (shiftedStream (uibhbotCodeWordRel w) N)
  rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
  exact facedUIBHBOTDecodedWindowBallClass_concat N r w hw

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTBSBallLaw_sub_windowClassLaw_le (N r : ℕ) (hr : 0 < r)
    (A : Set FacedFramedBallClass) :
    |(facedUIBHBOTBSBallLaw r hr : Measure FacedFramedBallClass).real A -
        (facedUIBHBOTWindowClassLaw N r).real A| ≤
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).real
        {W | ¬ (WholePlaneRotationHypothesis W ∧
          ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
            (kmswLLCreatedEdge (shiftedStream W N) N) true)} := by
  have hA : MeasurableSet A := MeasurableSpace.measurableSet_top
  have hf := measurable_facedUIBHBOTBallClassRel r hr
  have hg : Measurable (fun W =>
      facedUIBHBOTWindowStageBallClass N r (shiftedStream W N)) :=
    (measurable_facedUIBHBOTWindowStageBallClass N r).comp (measurable_windowShift N)
  rw [facedUIBHBOTWindowClassLaw_eq_code_map]
  change |((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    (fun W => facedUIBHBOTBallClassRel W r hr)).real A - _| ≤ _
  rw [map_measureReal_apply hf hA, map_measureReal_apply hg hA]
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hf hA).nullMeasurableSet (hg hA).nullMeasurableSet).trans
  refine measureReal_mono ?_ (by finiteness)
  intro W hW hcap
  have he := facedUIBHBOTBallClassRel_eq_windowStageClass W hcap.1 N r hr hcap.2
  change (facedUIBHBOTBallClassRel W r hr ∈ A ∧
      facedUIBHBOTWindowStageBallClass N r (shiftedStream W N) ∉ A) ∨
    (facedUIBHBOTWindowStageBallClass N r (shiftedStream W N) ∈ A ∧
      facedUIBHBOTBallClassRel W r hr ∉ A) at hW
  rw [he] at hW
  exact hW.elim (fun h => h.2 h.1) (fun h => h.2 h.1)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTBSBallLaw_sub_windowClassLaw_le_noCapture (N r : ℕ) (hr : 0 < r)
    (A : Set FacedFramedBallClass) :
    |(facedUIBHBOTBSBallLaw r hr : Measure FacedFramedBallClass).real A -
        (facedUIBHBOTWindowClassLaw N r).real A| ≤
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).real
        {W | ¬ ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
          (kmswLLCreatedEdge (shiftedStream W N) N) true} := by
  refine (facedUIBHBOTBSBallLaw_sub_windowClassLaw_le N r hr A).trans_eq ?_
  apply measureReal_congr
  filter_upwards [uibhbotCodeLawRel_ae_ballClassRel_event r] with W hW
  exact propext (by simp only [hW.1, true_and])

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
private theorem measurable_facedBridgeBall (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) (hr : 0 < r) :
    Measurable (facedDiskBSBallClass n ell hell r hr ∘
      diskBridgeDecoder ell n hell hle hmod) := by
  classical
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  exact (measurable_facedDiskBSBallClass n ell hell r hr).comp
    (measurable_diskBridgeDecoder ell n hell hle hmod)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskBSBallLaw_sub_decodedWindow_le
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r) (C : Set FacedFramedBallClass) :
    |(facedDiskBSBallLaw n ell hell hle hmod r hr : Measure FacedFramedBallClass).real C -
      (bridgeLevelLaw n ell).real
        ((fun p => (bridgeOptionWindow n N p).map
          (facedUIBHBOTDecodedWindowBallClass N r)) ⁻¹' (some '' C))| ≤
    1 - (bridgeLevelLaw n ell).real
      {p | ∃ x, bridgeOptionWindow n N p = some x ∧
        kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧
        ¬ DiskDip N K0 p} := by
  classical
  let μ := bridgeLevelLaw n ell
  let : IsProbabilityMeasure μ := bridge_probability n ell hell hle hmod
  let f := facedDiskBSBallClass n ell hell r hr ∘ diskBridgeDecoder ell n hell hle hmod
  let B := (fun p => (bridgeOptionWindow n N p).map
    (facedUIBHBOTDecodedWindowBallClass N r)) ⁻¹' (some '' C)
  let G : Set ((ℕ → Fin 3) × ℕ) :=
    {p | ∃ x, bridgeOptionWindow n N p = some x ∧
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) ∧ ¬ DiskDip N K0 p}
  have hf : Measurable f := measurable_facedBridgeBall n ell hell hle hmod r hr
  have hB : MeasurableSet B := measurableSet_bridgeOptionWindow_preimage n N
    ((Option.map (facedUIBHBOTDecodedWindowBallClass N r)) ⁻¹' (some '' C))
  have hC : MeasurableSet C := MeasurableSpace.measurableSet_top
  let D := (f ⁻¹' C) ∆ B
  have hD : MeasurableSet D := (hf hC).symmDiff hB
  have hbound : μ.real G ≤ μ.real Dᶜ := by
    apply ENNReal.toReal_mono (by finiteness)
    apply measure_mono_ae
    filter_upwards [facedDiskWindow_class_eq_on_capture n ell hell hle hmod N K0 r hr]
      with p hp
    rintro ⟨x, hx, hev, hnd⟩
    have he := hp x hx hev hnd
    have hb : p ∈ B ↔ f p ∈ C := by
      simp only [B, Set.mem_preimage, hx, Option.map_some]
      simpa only [Set.mem_image, Option.some.injEq, exists_eq_right] using
        (show facedUIBHBOTDecodedWindowBallClass N r x ∈ C ↔ f p ∈ C from he ▸ Iff.rfl)
    change ¬ ((f p ∈ C ∧ p ∉ B) ∨ (p ∈ B ∧ f p ∉ C))
    exact fun h => h.elim (fun h => h.2 (hb.mpr h.1))
      (fun h => h.2 (hb.mp h.1))
  have hfailure : μ.real D ≤ 1 - μ.real G := by
    rw [probReal_compl_eq_one_sub hD] at hbound
    linarith only [hbound]
  rw [← bridgeLevelLaw_map_facedDiskBSBallClass n ell hell hle hmod r hr,
    map_measureReal_apply hf hC]
  exact (abs_measureReal_sub_le_measureReal_symmDiff
    (hf hC).nullMeasurableSet hB.nullMeasurableSet).trans hfailure

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskDecodedWindow_sub_uibhbotWindow_le
    (A : ℝ) (hA : 1 < A) (N r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ell : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ C : Set FacedFramedBallClass,
        |(bridgeLevelLaw n ell).real
            ((fun p => (bridgeOptionWindow n N p).map
              (facedUIBHBOTDecodedWindowBallClass N r)) ⁻¹' (some '' C)) -
          (facedUIBHBOTWindowClassLaw N r).real C| ≤ ε := by
  obtain ⟨n₀, htv⟩ := diskWindow_decode_tv A hA N ε hε
    (facedUIBHBOTDecodedWindowBallClass N r) (measurable_facedUIBHBOTDecodedWindowBallClass N r)
  refine ⟨n₀, ?_⟩
  intro n hn ell hlo hhi hle hmod C
  have h := htv n hn ell hlo hhi hle hmod (some '' C)
  change |(bridgeLevelLaw n ell).real _ -
    (uibhbotEncodingWindowLaw N).real _| ≤ ε at h
  rw [facedUIBHBOTWindowClassLaw_eq_map, map_measureReal_apply
    (measurable_facedUIBHBOTDecodedWindowBallClass N r) MeasurableSpace.measurableSet_top]
  have hpre : (fun x => some (facedUIBHBOTDecodedWindowBallClass N r x)) ⁻¹' (some '' C) =
      (facedUIBHBOTDecodedWindowBallClass N r) ⁻¹' C := by
    ext x
    simp
  rw [hpre] at h
  exact h

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindowTransport_setwise
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (r : ℕ) (hr : 0 < r) (C : Set FacedFramedBallClass) :
    Tendsto (fun k =>
      (facedDiskBSBallLaw (k + 1) (ell k) (hadm k).1 (hadm k).2.1
        (hadm k).2.2 r hr : Measure FacedFramedBallClass).real C)
      atTop (𝓝 ((facedUIBHBOTBSBallLaw r hr : Measure FacedFramedBallClass).real C)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp
    (tendsto_uibhbotWindow_noCertifiedCapture r) (ε / 4) (by positivity)
  obtain ⟨K0, N, hMN, hgood⟩ :=
    diskWindowCapture_probability A hA ell hadm hlo hhi r (ε / 4) (by positivity) M
  obtain ⟨n₀, htv⟩ := facedDiskDecodedWindow_sub_uibhbotWindow_le A hA N r
    (ε / 4) (by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hgood
  refine ⟨max n₀ k₀, ?_⟩
  intro k hk
  let d := (facedDiskBSBallLaw (k + 1) (ell k) (hadm k).1 (hadm k).2.1
    (hadm k).2.2 r hr : Measure FacedFramedBallClass).real C
  let b := (bridgeLevelLaw (k + 1) (ell k)).real
    ((fun p => (bridgeOptionWindow (k + 1) N p).map
      (facedUIBHBOTDecodedWindowBallClass N r)) ⁻¹' (some '' C))
  let w := (facedUIBHBOTWindowClassLaw N r).real C
  let u := (facedUIBHBOTBSBallLaw r hr : Measure FacedFramedBallClass).real C
  have hdb : |d - b| ≤ ε / 4 := by
    have hb := facedDiskBSBallLaw_sub_decodedWindow_le (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2 N K0 r hr C
    have hg := hk₀ k ((le_max_right _ _).trans hk)
    dsimp only [d, b]
    linarith only [hb, hg]
  have hbw : |b - w| ≤ ε / 4 :=
    htv (k + 1) (by omega) (ell k) (hlo k) (hhi k)
      (hadm k).2.1 (hadm k).2.2 C
  have hwu : |w - u| < ε / 4 := by
    have hbound := facedUIBHBOTBSBallLaw_sub_windowClassLaw_le_noCapture N r hr C
    have hsmall := hM N hMN
    rw [Real.dist_eq, sub_zero] at hsmall
    rw [abs_sub_comm] at hbound
    dsimp only [w, u]
    exact hbound.trans_lt ((le_abs_self _).trans_lt hsmall)
  change dist d u < ε
  rw [Real.dist_eq]
  have htri₁ := abs_sub_le d b u
  have htri₂ := abs_sub_le b w u
  linarith only [hdb, hbw, hwu, htri₁, htri₂, hε]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedBallLaw_tendsto_of_singleton
    (μ : ℕ → ProbabilityMeasure FacedFramedBallClass) (ν : ProbabilityMeasure FacedFramedBallClass)
    (hmass : ∀ c : FacedFramedBallClass,
      Tendsto (fun k => (μ k : Measure FacedFramedBallClass).real {c}) atTop
        (𝓝 ((ν : Measure FacedFramedBallClass).real {c}))) :
    letI : TopologicalSpace FacedFramedBallClass := ⊥
    letI : OpensMeasurableSpace FacedFramedBallClass := ⟨le_top⟩
    Tendsto μ atTop (𝓝 ν) := by
  classical
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let : OpensMeasurableSpace FacedFramedBallClass := ⟨le_top⟩
  let S : Set (Set FacedFramedBallClass) := {s | ∃ c, s = {c}}
  have hcount : S.Countable := by
    have he : S = Set.range (fun c : FacedFramedBallClass => ({c} : Set FacedFramedBallClass)) := by
      ext s
      simp only [S, Set.mem_ofPred_eq, Set.mem_range]
      exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
    rw [he]
    exact Set.countable_range _
  let : SecondCountableTopology FacedFramedBallClass :=
    (isTopologicalBasis_singletons FacedFramedBallClass).secondCountableTopology
      hcount
  have hpi : IsPiSystem S := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ ⟨x, hx, hy⟩
    have hab : a = b := (Set.mem_singleton_iff.mp hx).symm.trans
      (Set.mem_singleton_iff.mp hy)
    exact ⟨a, by rw [← hab, Set.inter_self]⟩
  apply hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
    (fun _ _ => MeasurableSpace.measurableSet_top)
  · intro U _ x hx
    exact ⟨{x}, ⟨x, rfl⟩, (isOpen_discrete _).mem_nhds (Set.mem_singleton x),
      Set.singleton_subset_iff.mpr hx⟩
  · rintro _ ⟨c, rfl⟩
    rw [← NNReal.tendsto_coe]
    simpa using hmass c

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedDiskWindowTransport_limit
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace FacedFramedBallClass := ⊥
    letI : OpensMeasurableSpace FacedFramedBallClass := ⟨le_top⟩
    ∀ r : ℕ, ∀ hr : 0 < r,
      Tendsto (fun k => facedDiskBSBallLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2 r hr)
        atTop (𝓝 (facedUIBHBOTBSBallLaw r hr)) := by
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : OpensMeasurableSpace FacedFramedBallClass := ⟨le_top⟩
  intro r hr
  apply facedBallLaw_tendsto_of_singleton
  intro c
  exact facedDiskWindowTransport_setwise A hA ell hadm hlo hhi r hr {c}

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem facedUIBHBOTBallClassRel_eq_decodedWindowClass (N r : ℕ) (hr : 0 < r)
    (w : ℤ → List (Fin 3)) (hw : ∀ k, IsStoppedExcursionWord (w k))
    (H : WholePlaneRotationHypothesis (uibhbotCodeWord w (fun k => (hw k).1)))
    (hcap : ∃ c, uibhbotFixedCaptureRel (uibhbotCodeWord w (fun k => (hw k).1))
      r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) N)
      true) :
    facedUIBHBOTBallClassRel (uibhbotCodeWord w (fun k => (hw k).1)) r hr =
      facedUIBHBOTDecodedWindowBallClass N r
        (fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N)) :=
  (facedUIBHBOTBallClassRel_eq_windowStageClass _ H N r hr hcap).trans
    (facedUIBHBOTDecodedWindowBallClass_concat N r w hw).symm

end DirectedDistances.PaperProofs.Section5
