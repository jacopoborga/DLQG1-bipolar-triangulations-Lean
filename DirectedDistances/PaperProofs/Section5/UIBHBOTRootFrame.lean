module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel
public import DirectedDistances.KMSW.KMSWWholePlaneFaces
public import DirectedDistances.KMSW.KMSWWindowGlobalSeamFresh
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.KMSWStageBallDartsStage

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The capture's marked dart determines the ordered whole-plane root frame. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory

private theorem capturedRoot_present_iff (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge)
    (hv : ¬ UpperFrontierEndpoint (kmswStage w m)
      (stageEndpoint (kmswStage w m) d)) :
    EdgePresent w d.1.val ↔ (kmswStage w m).present d.1.val = true := by
  have hstable (n : ℕ) (hmn : m ≤ n) :
      (kmswStage w n).present d.1.val = (kmswStage w m).present d.1.val := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
        have hne : d.1.val ≠ (kmswStage w (n + 1)).active := by
          intro heq
          obtain ⟨xs, hxs⟩ := kmswStage_UL_last w (n + 1)
          have hmem : (kmswStage w (n + 1)).active ∈
              (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR := by
            rw [hxs]
            simp
          have hf := kmswStage_upperFrontier_endpoints w m (n + 1)
            (by omega) _ hmem
          rw [← heq] at hf
          have hs := kmswStage_endpoints_stable w (m := m) (n := n + 1)
            (by omega) d.1.isLt
          rw [hs.1, hs.2] at hf
          cases hb : d.2
          · exact hv (by simpa only [stageEndpoint, hb, Bool.false_eq_true,
              ↓reduceIte] using hf.1)
          · exact hv (by simpa only [stageEndpoint, hb, ↓reduceIte] using hf.2)
        change (kmswStep (kmswStage w n) (w n)).present d.1.val = _
        rw [kmswStep_present_existing _ _
          (d.1.isLt.trans_le (kmswStage_nextEdge_mono w hmn))]
        change (if d.1.val = (kmswStage w (n + 1)).active then true
          else (kmswStage w n).present d.1.val) = _
        rw [ite_eq_right hne]
        exact ih
  constructor
  · rintro ⟨n, hn, hp⟩
    have hp' := (present_mono w hn hp (max m n) (Nat.le_max_right m n)).2
    rw [hstable _ (Nat.le_max_left m n)] at hp'
    exact hp'
  · exact fun hp => ⟨m, d.1.isLt, hp⟩

private theorem certifiedCapture_center_fresh (W : ℤ → Fin 3) (r : ℕ)
    (C : UIBHBOTCertifiedRootCapture W r) (M : ℕ) (hNM : C.N ≤ M) :
    wholePlaneFresh W C.N M hNM C.c := by
  classical
  have hc : C.c < (kmswStage (shiftedStream W C.N) C.m).nextVertex := C.event.1.1
  have hball : C.c ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (shiftedStream W C.N) C.m) r C.c := by
    apply (kmswStageBallVertices_mem_iff_distanceLe _ _ _ _ _ _ hc).mpr
    exact ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  have hball' := kmswStageBallVertices_mono (fun _ _ => True)
    (kmswStage (shiftedStream W C.N) C.m) (show r ≤ r + 1 by omega) hball
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hball).1
  have hs := shiftedStream_shift W C.N M hNM
  have hb' : C.c < (kmswStage
      (fun i => shiftedStream W M (M - C.N + i)) C.m).nextVertex := by
    rw [hs]
    exact hb
  change (kmswStage (shiftedStream W M) (M - C.N)).nextVertex ≤
    kmswWindowVertexMapInf (shiftedStream W M) (M - C.N) C.c
  rw [kmswWindowVertexMapInf_eq_stage _ _ _ _ hb']
  have hdata := C.event.1.2.1 C.c hball'
  apply kmswWindowPatchVertexMap_fresh_of_global_seams
    (shiftedStream W C.N) C.m C.c hb hdata.1
    (shiftedStream W M) (M - C.N) (fun i hi => congrFun hs i)
  intro k hk hcreate
  refine ⟨hdata.2 k hk hcreate, ?_⟩
  intro hl
  by_cases hem : (kmswStage (shiftedStream W C.N) k).UL.dropLast.reverse = []
  · exact Or.inr ((C.seams M hNM k
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,
        ⟨C.c, hball', hcreate⟩, hl, hem⟩)).1)
  · exact Or.inl hem

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The whole-plane representative of the captured missing root edge is absent. -/
theorem UIBHBOTCertifiedRootCapture.root_missing_wholePlane {W : ℤ → Fin 3}
    {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r) :
    ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) := by
  let w := shiftedStream W C.N
  let s := kmswStage w C.m
  have hc : C.c < s.nextVertex := C.event.1.1
  have hball : C.c ∈ kmswStageBallVertices (fun _ _ => True) s (r + 1) C.c := by
    apply (kmswStageBallVertices_mem_iff_distanceLe _ _ _ _ _ _ hc).mpr
    exact ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  have hnot : ¬ UpperFrontierEndpoint s C.c := C.event.2 C.c hball
  have hv : ¬ UpperFrontierEndpoint s
      (stageEndpoint s (edgeFlip s.nextEdge C.dart)) := by
    rw [C.dart_center]
    exact hnot
  have hmiss : s.present C.dart.1.val = false := by
    change (kmswStage w C.m).present C.dart.1.val = false
    exact C.missing
  have hpresent : ¬ EdgePresent w C.dart.1.val := by
    intro hp
    have hp' := (capturedRoot_present_iff w C.m
      (edgeFlip s.nextEdge C.dart) hv).mp hp
    have heq : (edgeFlip s.nextEdge C.dart).1.val = C.dart.1.val := rfl
    rw [heq, hmiss] at hp'
    cases hp'
  have hend : (if !C.dart.2 then edgeEast w C.dart.1.val
      else edgeWest w C.dart.1.val) = C.c := by
    cases hb : C.dart.2
    · have hc' := C.dart_center
      change (if !C.dart.2 then (kmswStage w C.m).east C.dart.1.val
        else (kmswStage w C.m).west C.dart.1.val) = C.c at hc'
      simp only [hb, Bool.not_false, ↓reduceIte] at hc'
      simp only [Bool.not_false, ↓reduceIte]
      exact (edge_endpoints_eq w C.dart.1.isLt).2.symm.trans hc'
    · have hc' := C.dart_center
      change (if !C.dart.2 then (kmswStage w C.m).east C.dart.1.val
        else (kmswStage w C.m).west C.dart.1.val) = C.c at hc'
      simp only [hb, Bool.not_true] at hc'
      simp only [Bool.not_true]
      exact (edge_endpoints_eq w C.dart.1.isLt).1.symm.trans hc'
  have hfresh : ∀ M (hNM : C.N ≤ M), wholePlaneFresh W C.N M hNM
      (if !C.dart.2 then edgeEast w C.dart.1.val else edgeWest w C.dart.1.val) := by
    intro M hNM
    rw [hend]
    exact certifiedCapture_center_fresh W r C M hNM
  have hroot := wholePlaneEdgePresent_ι_of_fresh W C.N C.dart.1.val
    (!C.dart.2) hfresh
  rw [C.root] at hroot
  exact fun hp => hpresent (hroot.mp hp)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The marked dart's opposite incidence is the first root endpoint and its
incidence is the second, in the source order `(endpoint (edgeFlip d), endpoint d)`. -/
theorem UIBHBOTCertifiedRootCapture.root_ordered_endpoints
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r) :
    wholePlaneVertexι W C.N
        (stageEndpoint (kmswStage (shiftedStream W C.N) C.m)
          (edgeFlip _ C.dart)) = uibhbotRootFirstVertex W ∧
      wholePlaneVertexι W C.N
        (stageEndpoint (kmswStage (shiftedStream W C.N) C.m) C.dart) =
          uibhbotRootSecondVertex W := by
  constructor
  · exact (congrArg (wholePlaneVertexι W C.N) C.dart_center).trans C.center
  · have hside := uibhbotRelaxedCapture_rootDart_side W C.N C.m C.c C.center
      C.dart C.dart_center C.root
    have hendpoint : stageEndpoint (kmswStage (shiftedStream W C.N) C.m) C.dart =
        edgeEast (shiftedStream W C.N) C.dart.1.val := by
      simp [stageEndpoint, hside, edge_endpoints_eq (shiftedStream W C.N) C.dart.1.isLt]
    calc
      wholePlaneVertexι W C.N
          (stageEndpoint (kmswStage (shiftedStream W C.N) C.m) C.dart) =
          wholePlaneVertexι W C.N
            (edgeEast (shiftedStream W C.N) C.dart.1.val) :=
              congrArg (wholePlaneVertexι W C.N) hendpoint
      _ = wholePlaneEdgeEast W (wholePlaneEdgeι W C.N C.dart.1.val) :=
        (wholePlaneEdgeEast_ι W C.N C.dart.1.val).symm
      _ = uibhbotRootSecondVertex W := by rw [C.root]; rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Any two certified captures yield the same whole-plane root edge and ordered
incidences. -/
theorem UIBHBOTCertifiedRootCapture.rootFrame_independent
    {W : ℤ → Fin 3} {r : ℕ}
    (C D : UIBHBOTCertifiedRootCapture W r) :
    wholePlaneEdgeι W C.N C.dart.1.val = wholePlaneEdgeι W D.N D.dart.1.val ∧
      (wholePlaneVertexι W C.N
          (stageEndpoint (kmswStage (shiftedStream W C.N) C.m)
            (edgeFlip _ C.dart)),
        wholePlaneVertexι W C.N
          (stageEndpoint (kmswStage (shiftedStream W C.N) C.m) C.dart)) =
      (wholePlaneVertexι W D.N
          (stageEndpoint (kmswStage (shiftedStream W D.N) D.m)
            (edgeFlip _ D.dart)),
        wholePlaneVertexι W D.N
          (stageEndpoint (kmswStage (shiftedStream W D.N) D.m) D.dart)) := by
  constructor
  · exact C.root.trans D.root.symm
  · have hC := C.root_ordered_endpoints
    have hD := D.root_ordered_endpoints
    rw [hC.1, hC.2, hD.1, hD.2]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Almost surely the concatenated word has the canonical ordered whole-plane root,
and that edge is missing. The root edge and endpoints are independent of capture
choice by `rootFrame_independent`. -/
theorem uibhbotWordFamilyLaw_ae_root_missing_wholePlane :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) := by
  filter_upwards [uibhbotWordFamilyLaw_ae_certifiedRootCapture] with w h
  obtain ⟨hw, _, hcaptures⟩ := h
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  refine ⟨hw, ?_⟩
  obtain ⟨C⟩ := hcaptures 0
  exact C.root_missing_wholePlane

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The source domain for the canonical whole-plane root frame consists of stopped
block families. -/
abbrev UIBHBOTStoppedWordFamily :=
  {w : ℤ → List (Fin 3) // ∀ k, IsStoppedExcursionWord (w k)}

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The dependent edge and its two ordered vertices, bundled with their code word. -/
structure UIBHBOTWholePlaneRootFrame where
  word : ℤ → Fin 3
  edge : WholePlaneEdge word
  first : WholePlaneVertex word
  second : WholePlaneVertex word

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The canonical whole-plane root frame as a function of a stopped block family. -/
@[expose] noncomputable def uibhbotWholePlaneRootFrame
    (x : UIBHBOTStoppedWordFamily) : UIBHBOTWholePlaneRootFrame := by
  let W := uibhbotCodeWord x.1 (fun k => (x.2 k).1)
  exact ⟨W, uibhbotRootEdge W, uibhbotRootFirstVertex W,
    uibhbotRootSecondVertex W⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Measurability of the canonical root frame for specified source and target
sigma-algebras; it is recorded as an obligation until a root-frame Borel
structure is supplied. -/
def uibhbotWholePlaneRootFrameMeasurability
    (source : MeasurableSpace UIBHBOTStoppedWordFamily)
    (target : MeasurableSpace UIBHBOTWholePlaneRootFrame) : Prop :=
  @Measurable UIBHBOTStoppedWordFamily UIBHBOTWholePlaneRootFrame source target
    uibhbotWholePlaneRootFrame

end DirectedDistances.PaperProofs.Section5
