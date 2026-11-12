module
public import DirectedDistances.Paper.Section5.DiskBSConv
public import Palomar.Principal.Support.HalfPlaneSource
@[expose] public section
noncomputable section
namespace DLQG1.Palomar.DiskSampler
open MeasureTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5
abbrev Codes (ell n : ℕ) := KMSWLeftWalkClass (ell + 1) n
abbrev Maps (ell n : ℕ) :=
  {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
abbrev CodeSample (ell n : ℕ) := Codes ell n × Fin ell
abbrev MapSample (ell n : ℕ) := Maps ell n × Fin ell
instance codeMeasurableSpace (ell n : ℕ) : MeasurableSpace (Codes ell n) := ⊤
instance mapMeasurableSpace (ell n : ℕ) : MeasurableSpace (Maps ell n) := ⊤
def endpointEquiv (ell n : ℕ) (hell : 0 < ell) : Codes ell n ≃ Maps ell n :=
  kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
@[instance_reducible] def mapFintype (ell n : ℕ) (hell : 0 < ell) : Fintype (Maps ell n) :=
  Fintype.ofEquiv (Codes ell n) (endpointEquiv ell n hell)
def markedEquiv (ell n : ℕ) (hell : 0 < ell) : CodeSample ell n ≃ MapSample ell n :=
  (endpointEquiv ell n hell).prodCongr (Equiv.refl (Fin ell))
theorem mark_preserved (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) :
    (markedEquiv ell n hell p).2 = p.2 := rfl
def codeMeasure (ell n : ℕ) : Measure (CodeSample ell n) :=
  (uniformCountingMeasure (Codes ell n)).prod (uniformCountingMeasure (Fin ell))
def mapMeasure (ell n : ℕ) (hell : 0 < ell) : Measure (MapSample ell n) := by
  letI := mapFintype ell n hell
  exact (uniformCountingMeasure (Maps ell n)).prod (uniformCountingMeasure (Fin ell))
theorem uniform_map_transport (ell n : ℕ) (hell : 0 < ell) :
    (codeMeasure ell n).map (markedEquiv ell n hell) = mapMeasure ell n hell := by
  letI := mapFintype ell n hell
  have hm : Measurable (endpointEquiv ell n hell) := measurable_of_countable _
  have hE := uniformCountingMeasure_map_of_bijective (endpointEquiv ell n hell)
    (endpointEquiv ell n hell).bijective
  letI : SFinite (uniformCountingMeasure (Fin ell)) := by
    unfold uniformCountingMeasure
    infer_instance
  have hmarked : (markedEquiv ell n hell : CodeSample ell n → MapSample ell n) =
      Prod.map (endpointEquiv ell n hell) id := by
    funext p
    rfl
  rw [hmarked]
  simpa only [codeMeasure, mapMeasure, Measure.map_id, hE] using
    (Measure.map_prod_map (uniformCountingMeasure (Codes ell n))
      (uniformCountingMeasure (Fin ell)) hm measurable_id).symm
theorem codeMeasure_probability (ell n : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    IsProbabilityMeasure (codeMeasure ell n) := by
  letI : Nonempty (Codes ell n) := kmswLeftWalkClass_nonempty_of_domain ell n hell hle hmod
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  letI := diskBS_uniformCountingMeasure_probability (Codes ell n)
  letI := diskBS_uniformCountingMeasure_probability (Fin ell)
  dsimp [codeMeasure]
  infer_instance
structure ExteriorData (ell n : ℕ) (hell : 0 < ell) (p : MapSample ell n) where
  drawing : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n
  face : drawing.Face
  unbounded : drawing.IsUnbounded face
  border : ∀ d, drawing.dartBorders d face ↔
    (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d
theorem exteriorData_nonempty (ell n : ℕ) (hell : 0 < ell) (p : MapSample ell n) :
    Nonempty (ExteriorData ell n hell p) := by
  obtain ⟨P, U, hU, hb, _⟩ := finiteSampleClass_spec ell n hell p
  exact ⟨⟨P, U, hU, hb⟩⟩
def exteriorData (ell n : ℕ) (hell : 0 < ell) (p : MapSample ell n) :
    ExteriorData ell n hell p := Classical.choice (exteriorData_nonempty ell n hell p)
def mapClass (ell n : ℕ) (hell : 0 < ell) (p : MapSample ell n) :
    D39GeomRootedMapClass :=
  let D := exteriorData ell n hell p
  PLCylinderBall.geometricClass
    (diskSampleExteriorDomain ell n hell p D.drawing D.face D.unbounded D.border)
def codeClass (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) :
    D39GeomRootedMapClass := mapClass ell n hell (markedEquiv ell n hell p)
local instance : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
local instance : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
theorem measurable_mapClass (ell n : ℕ) (hell : 0 < ell) :
    Measurable (mapClass ell n hell) := by
  letI := mapFintype ell n hell
  exact measurable_of_countable _
theorem measurable_codeClass (ell n : ℕ) (hell : 0 < ell) :
    Measurable (codeClass ell n hell) := by
  exact measurable_of_countable _
theorem mapClass_law_eq_source (ell n : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    (mapMeasure ell n hell).map (mapClass ell n hell) =
      (finiteGeometricLaw n ell hell hle hmod).toMeasure := by
  exact (finiteGeometricLaw_eq_exterior_pushforward n ell hell hle hmod
    (fun p => (exteriorData ell n hell p).drawing)
    (fun p => (exteriorData ell n hell p).face)
    (fun p => (exteriorData ell n hell p).unbounded)
    (fun p => (exteriorData ell n hell p).border)).symm
theorem codeClass_law_eq_source (ell n : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    (codeMeasure ell n).map (codeClass ell n hell) =
      (finiteGeometricLaw n ell hell hle hmod).toMeasure := by
  rw [← mapClass_law_eq_source ell n hell hle hmod, ← uniform_map_transport ell n hell]
  rw [Measure.map_map (measurable_mapClass ell n hell) (measurable_of_countable _)]
  rfl

def codeStream {ell n : ℕ} (c : Codes ell n) : ℕ → Fin 3 :=
  DirectedDistances.KMSW.finiteCodeExtend (n := n + 1) c.val
def markIndex {ell : ℕ} (j : Fin ell) : Fin ((ell + 1) - 1) :=
  Fin.cast (by omega : ell = (ell + 1) - 1) j
def rootDart {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    StageDart (kmswStage (codeStream c) n).nextEdge :=
  edgeFlip _ (kmswDiskRootDart c (markIndex j))
theorem root_missing {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    (kmswStageDirectedMap (codeStream c) n).missing (rootDart c j) := by
  exact ((kmswStageDirectedMap (codeStream c) n).missing_edgeInv _).mp
    (kmswDiskRootDart_missing c (markIndex j))
theorem root_west_to_east {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    stageEndpoint (kmswStage (codeStream c) n) (rootDart c j) =
      (kmswStage (codeStream c) n).west (rootDart c j).1.val ∧
    stageEndpoint (kmswStage (codeStream c) n) (edgeFlip _ (rootDart c j)) =
      (kmswStage (codeStream c) n).east (rootDart c j).1.val := by
  constructor <;> rfl
theorem canonicalCode_transport (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) :
    diskSampleCanonicalStageCode ell n hell (markedEquiv ell n hell p) = codeStream p.1 := by
  simp only [diskSampleCanonicalStageCode, markedEquiv, endpointEquiv,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.symm_apply_apply, codeStream]
theorem rootedMap_transport (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) :
    diskRootedPlanarMapOfSample n ell hell (markedEquiv ell n hell p) =
      diskRootedPlanarMapOfCodeMark p.1 (markIndex p.2) := by
  simp only [diskRootedPlanarMapOfSample, markedEquiv, endpointEquiv,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.symm_apply_apply, markIndex]
def finiteLaw (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    ProbabilityMeasure D39GeomRootedMapClass := by
  letI := codeMeasure_probability ell n hell hle hmod
  exact ⟨(codeMeasure ell n).map (codeClass ell n hell),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_codeClass ell n hell).aemeasurable).2 inferInstance⟩
theorem finiteLaw_eq_source (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    finiteLaw n ell hell hle hmod = finiteGeometricLaw n ell hell hle hmod := by
  apply ProbabilityMeasure.toMeasure_injective
  exact codeClass_law_eq_source ell n hell hle hmod
theorem disk_local_limit (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    Filter.Tendsto (fun k => finiteLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) Filter.atTop
      (nhds uibhbotSourceGeometricClassLaw) := by
  have hfun : (fun k => finiteLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) =
      (fun k => finiteGeometricLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2) := by
    funext k
    exact finiteLaw_eq_source _ _ _ _ _
  rw [hfun]
  exact DirectedDistances.Paper.Section5.prop_disk_bs_conv A hA ell hadm hlo hhi

end DLQG1.Palomar.DiskSampler
@[expose] public section
noncomputable section
namespace DLQG1.Palomar.DiskCodeGeometry
open MeasureTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.SourceResults
open DLQG1.Palomar.DiskSampler
structure DrawingData {ell n : ℕ} (c : Codes ell n) where
  drawing : StageDrawing (codeStream c) n
  face : drawing.Face
  unbounded : drawing.IsUnbounded face
  border : ∀ d, drawing.dartBorders d face ↔ (kmswStageDirectedMap (codeStream c) n).IsOuter d
theorem drawingData_nonempty (ell n : ℕ) (hell : 0 < ell) (c : Codes ell n) :
    Nonempty (DrawingData c) := by
  let p : CodeSample ell n := (c, ⟨0, hell⟩)
  let q := markedEquiv ell n hell p
  let D := exteriorData ell n hell q
  have hx : ∃ P : StageDrawing (diskSampleCanonicalStageCode ell n hell q) n,
      ∃ U : P.Face, P.IsUnbounded U ∧
        (∀ d, P.dartBorders d U ↔
          (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell q) n).IsOuter d) :=
    ⟨D.drawing, D.face, D.unbounded, D.border⟩
  dsimp only [q] at hx
  rw [canonicalCode_transport ell n hell p] at hx
  obtain ⟨P, U, hU, hb⟩ := hx
  exact ⟨⟨P, U, hU, hb⟩⟩
def drawingData (ell n : ℕ) (hell : 0 < ell) (c : Codes ell n) : DrawingData c :=
  Classical.choice (drawingData_nonempty ell n hell c)
def domain {ell n : ℕ} (c : Codes ell n) (j : Fin ell) (D : DrawingData c) :
    D39DomainRootedMapV2 := by
  let w := codeStream c
  let P := D.drawing
  let missing : P.GeometricEdge → Prop := fun e => (kmswStageDirectedMap w n).missing e.out
  let forward : {e : P.GeometricEdge // ¬ missing e} → Bool := fun e => !e.val.out.2
  let hmissingExternal :=
    kmswStageDrawing_missingEdges_external_of_exteriorFace P D.face D.unbounded D.border
  let M := finitePLDrawingDirectedMap P missing forward hmissingExternal
  let root := kmswStageDrawingDartEdgeDirectionEquiv P (rootDart c j)
  have hconn : ∀ v v' : Fin (kmswStage w n).nextVertex,
      (d39GeomGraph M).Reachable v v' := by
    simpa [M, missing, forward] using
      kmswStageDrawing_geometricGraph_connected_of_external P hmissingExternal
  have hframeMissing : (kmswStageDirectedMap w n).missing (rootDart c j) := root_missing c j
  have hroot : M.toPlaneMapWithMissing.missing root.1 := by
    change (kmswStageDirectedMap w n).missing root.1.out
    dsimp [root, kmswStageDrawingDartEdgeDirectionEquiv]
    rcases P.geometricEdge_out_mk (rootDart c j) with hout | hout
    · rw [hout]
      exact hframeMissing
    · rw [hout]
      exact (kmswStageDirectedMap w n).missing_edgeInv (rootDart c j) |>.2 hframeMissing
  exact finitePLDrawingD39DomainRootedMapV2 P missing forward hmissingExternal root hconn (Or.inl hroot)
def classOf (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) : D39GeomRootedMapClass :=
  PLCylinderBall.geometricClass (domain p.1 p.2 (drawingData ell n hell p.1))

def sourceMapClass (ell n : ℕ) (hell : 0 < ell) (p : MapSample ell n) :
    D39GeomRootedMapClass :=
  let c := (endpointEquiv ell n hell).symm p.1
  PLCylinderBall.geometricClass (domain c p.2 (drawingData ell n hell c))
theorem domain_eq_source (ell n : ℕ) (hell : 0 < ell) (p : MapSample ell n)
    (D : DrawingData ((endpointEquiv ell n hell).symm p.1)) :
    domain ((endpointEquiv ell n hell).symm p.1) p.2 D =
      diskSampleExteriorDomain ell n hell p D.drawing D.face D.unbounded D.border := by
  rfl
theorem class_transport (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) :
    sourceMapClass ell n hell (markedEquiv ell n hell p) = classOf ell n hell p := by
  have hfirst : (markedEquiv ell n hell p).1 = endpointEquiv ell n hell p.1 := rfl
  dsimp only [sourceMapClass, classOf]
  rw [hfirst, Equiv.symm_apply_apply, mark_preserved]
local instance : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
local instance : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
theorem measurable_classOf (ell n : ℕ) (hell : 0 < ell) :
    Measurable (classOf ell n hell) := measurable_of_countable _
theorem measurable_sourceMapClass (ell n : ℕ) (hell : 0 < ell) :
    Measurable (sourceMapClass ell n hell) := by
  letI := mapFintype ell n hell
  exact measurable_of_countable _
theorem sourceMapClass_law_eq_source (ell n : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    (mapMeasure ell n hell).map (sourceMapClass ell n hell) =
      (Prop516ExteriorAssembly5.finiteGeometricLaw n ell hell hle hmod).toMeasure := by
  have h := Prop516ExteriorAssembly5.finiteGeometricLaw_eq_exterior_pushforward
    n ell hell hle hmod
    (fun p => (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).drawing)
    (fun p => (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).face)
    (fun p => (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).unbounded)
    (fun p => (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).border)
  have hfun : sourceMapClass ell n hell =
      (fun p => PLCylinderBall.geometricClass
        (diskSampleExteriorDomain ell n hell p
          (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).drawing
          (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).face
          (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).unbounded
          (drawingData ell n hell ((endpointEquiv ell n hell).symm p.1)).border)) := by
    funext p
    exact congrArg PLCylinderBall.geometricClass
      (domain_eq_source ell n hell p _)
  rw [hfun]
  exact h.symm
theorem class_law_eq_source (ell n : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    (codeMeasure ell n).map (classOf ell n hell) =
      (Prop516ExteriorAssembly5.finiteGeometricLaw n ell hell hle hmod).toMeasure := by
  rw [← sourceMapClass_law_eq_source ell n hell hle hmod,
    ← uniform_map_transport ell n hell]
  rw [Measure.map_map (measurable_sourceMapClass ell n hell) (measurable_of_countable _)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun p => (class_transport ell n hell p).symm
def finiteLaw (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    ProbabilityMeasure D39GeomRootedMapClass := by
  letI := codeMeasure_probability ell n hell hle hmod
  exact ⟨(codeMeasure ell n).map (classOf ell n hell),
    (Measure.isProbabilityMeasure_map_iff (measurable_classOf ell n hell).aemeasurable).2 inferInstance⟩
theorem finiteLaw_eq_source (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    finiteLaw n ell hell hle hmod =
      Prop516ExteriorAssembly5.finiteGeometricLaw n ell hell hle hmod := by
  apply ProbabilityMeasure.toMeasure_injective
  exact class_law_eq_source ell n hell hle hmod


theorem law_independent_of_drawing (ell n : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (D : ∀ c : Codes ell n, DrawingData c) :
    (codeMeasure ell n).map (fun p : CodeSample ell n =>
      PLCylinderBall.geometricClass (domain p.1 p.2 (D p.1))) =
        (finiteLaw n ell hell hle hmod).toMeasure := by
  let G : MapSample ell n → D39GeomRootedMapClass := fun p =>
    PLCylinderBall.geometricClass
      (domain ((endpointEquiv ell n hell).symm p.1) p.2
        (D ((endpointEquiv ell n hell).symm p.1)))
  letI := mapFintype ell n hell
  have hG : Measurable G := measurable_of_countable _
  have hs := Prop516ExteriorAssembly5.finiteGeometricLaw_eq_exterior_pushforward
    n ell hell hle hmod
    (fun p => (D ((endpointEquiv ell n hell).symm p.1)).drawing)
    (fun p => (D ((endpointEquiv ell n hell).symm p.1)).face)
    (fun p => (D ((endpointEquiv ell n hell).symm p.1)).unbounded)
    (fun p => (D ((endpointEquiv ell n hell).symm p.1)).border)
  have hfun : G = (fun p => PLCylinderBall.geometricClass
      (diskSampleExteriorDomain ell n hell p
        (D ((endpointEquiv ell n hell).symm p.1)).drawing
        (D ((endpointEquiv ell n hell).symm p.1)).face
        (D ((endpointEquiv ell n hell).symm p.1)).unbounded
        (D ((endpointEquiv ell n hell).symm p.1)).border)) := by
    funext p
    exact congrArg PLCylinderBall.geometricClass (domain_eq_source ell n hell p _)
  have hcomp : G ∘ markedEquiv ell n hell =
      (fun p : CodeSample ell n =>
        PLCylinderBall.geometricClass (domain p.1 p.2 (D p.1))) := by
    funext p
    have hfirst : (markedEquiv ell n hell p).1 = endpointEquiv ell n hell p.1 := rfl
    dsimp only [Function.comp_apply, G]
    rw [hfirst, Equiv.symm_apply_apply, mark_preserved]
  rw [finiteLaw_eq_source, hs]
  rw [← hfun]
  change (codeMeasure ell n).map
      (fun p : CodeSample ell n =>
        PLCylinderBall.geometricClass (domain p.1 p.2 (D p.1))) =
    (mapMeasure ell n hell).map G
  rw [← uniform_map_transport ell n hell,
    Measure.map_map hG (measurable_of_countable _), hcomp]
theorem disk_local_limit (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    Filter.Tendsto (fun k => finiteLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) Filter.atTop
      (nhds uibhbotSourceGeometricClassLaw) := by
  have hfun : (fun k => finiteLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) =
      (fun k => Prop516ExteriorAssembly5.finiteGeometricLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2) := by
    funext k
    exact finiteLaw_eq_source _ _ _ _ _
  rw [hfun]
  exact DirectedDistances.Paper.Section5.prop_disk_bs_conv A hA ell hadm hlo hhi

end DLQG1.Palomar.DiskCodeGeometry
@[expose] public section
noncomputable section
namespace DLQG1.Palomar.DiskMinimal
open MeasureTheory Filter
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.SourceResults
open DLQG1.Palomar.DiskSampler
open DLQG1.Palomar.GeometryInterface
attribute [local instance] DLQG1.Palomar.GeometryInterface.metric
attribute [local instance] DLQG1.Palomar.GeometryInterface.topology
local instance modelMeasurable : MeasurableSpace MapClass := borel MapClass
local instance modelBorel : BorelSpace MapClass := ⟨rfl⟩
theorem firstHit_exists {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    ∃ m, L (codeStream c) m = -((j.val + 1 : ℕ) : ℤ) := by
  exact kmswLL_level_hit (codeStream c) n (j.val + 1) (by omega)
    (kmswDiskFiniteSample_index_bound c (markIndex j)).2
def firstHit {ell n : ℕ} (c : Codes ell n) (j : Fin ell) : ℕ :=
  Nat.find (firstHit_exists c j)
theorem firstHit_eq_source {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    firstHit c j = kmswDiskFirstHit c (markIndex j) := by
  rfl
theorem rootEdge_bound {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    kmswLLCreatedEdge (codeStream c) (firstHit c j) <
      (kmswStage (codeStream c) n).nextEdge := by
  exact (kmswDiskRootDart c (markIndex j)).1.isLt
def rootDart {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    StageDart (kmswStage (codeStream c) n).nextEdge :=
  (⟨kmswLLCreatedEdge (codeStream c) (firstHit c j), rootEdge_bound c j⟩, false)
theorem rootDart_eq_source {ell n : ℕ} (c : Codes ell n) (j : Fin ell) :
    rootDart c j = DLQG1.Palomar.DiskSampler.rootDart c j := by
  rfl
theorem outer_nonempty (w : ℕ → Fin 3) (n : ℕ) : (kmswStage w n).UL ≠ [] :=
  (kmswStage_UL_nonempty_active_last w n).1
theorem outer_head_bound (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.head (outer_nonempty w n) < (kmswStage w n).nextEdge := by
  exact (stageULHeadDart w n).1.isLt
def outerDart (w : ℕ → Fin 3) (n : ℕ) : StageDart (kmswStage w n).nextEdge :=
  (⟨(kmswStage w n).UL.head (outer_nonempty w n), outer_head_bound w n⟩, false)
theorem outerDart_eq_source (w : ℕ → Fin 3) (n : ℕ) :
    outerDart w n = stageULHeadDart w n := by
  rfl
def outer (w : ℕ → Fin 3) (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) : Prop :=
  Equiv.Perm.SameCycle ((stageRot w n)⁻¹ * edgeFlip _) (outerDart w n) d
structure DrawingData {ell n : ℕ} (c : Codes ell n) where
  drawing : StageDrawing (codeStream c) n
  face : drawing.Face
  unbounded : drawing.IsUnbounded face
  border : ∀ d, drawing.dartBorders d face ↔ outer (codeStream c) n d
def DrawingData.toSource {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) :
    DLQG1.Palomar.DiskCodeGeometry.DrawingData c :=
  ⟨D.drawing, D.face, D.unbounded, D.border⟩
theorem drawingData_nonempty (ell n : ℕ) (hell : 0 < ell) (c : Codes ell n) :
    Nonempty (DrawingData c) := by
  let D := DLQG1.Palomar.DiskCodeGeometry.drawingData ell n hell c
  exact ⟨⟨D.drawing, D.face, D.unbounded, D.border⟩⟩
def drawingData (ell n : ℕ) (hell : 0 < ell) (c : Codes ell n) : DrawingData c :=
  Classical.choice (drawingData_nonempty ell n hell c)
def missing {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) :
    D.drawing.GeometricEdge → Prop :=
  fun e => (kmswStage (codeStream c) n).present e.out.1.val = false
def forward {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) :
    {e : D.drawing.GeometricEdge // ¬ missing D e} → Bool :=
  fun e => !e.val.out.2
theorem missing_external {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) :
    ∀ e, missing D e → ∃ F : D.drawing.toPlaneGraphDrawing.Face,
      PlaneGraphDrawing.IsExternal D.drawing.toPlaneGraphDrawing F ∧
        Set.range (D.drawing.toPlaneGraphDrawing.arc e) ⊆ closure F.val := by
  exact kmswStageDrawing_missingEdges_external_of_exteriorFace
    D.drawing D.face D.unbounded D.border
def map {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) :=
  finitePLDrawingDirectedMap D.drawing (missing D) (forward D) (missing_external D)
theorem connected {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) :
    ∀ v v' : Fin (kmswStage (codeStream c) n).nextVertex,
      (d39GeomGraph (map D)).Reachable v v' := by
  exact kmswStageDrawing_geometricGraph_connected_of_external D.drawing (missing_external D)
def root {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) (j : Fin ell) :
    D.drawing.GeometricEdge × Bool :=
  (Quotient.mk D.drawing.edgeSetoid (rootDart c j),
    decide (rootDart c j = (Quotient.mk D.drawing.edgeSetoid (rootDart c j)).out))
theorem root_missing {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) (j : Fin ell) :
    (map D).toPlaneMapWithMissing.missing (root D j).1 := by
  change (kmswStage (codeStream c) n).present (root D j).1.out.1.val = false
  have hframe : (kmswStage (codeStream c) n).present (rootDart c j).1.val = false :=
    DLQG1.Palomar.DiskSampler.root_missing c j
  dsimp [root]
  rcases D.drawing.geometricEdge_out_mk (rootDart c j) with hout | hout
  · rw [hout]
    exact hframe
  · rw [hout]
    exact hframe
def domain {ell n : ℕ} (c : Codes ell n) (j : Fin ell) (D : DrawingData c) :
    D39DomainRootedMapV2 := by
  letI : Finite D.drawing.GeometricEdge := plDrawing_geometricEdge_finite D.drawing
  exact d39FiniteDomainRootedMapV2 (map D) (root D j)
    (connected D) (Or.inl (root_missing D j))
theorem domain_eq_source {ell n : ℕ} (c : Codes ell n) (j : Fin ell) (D : DrawingData c) :
    domain c j D = DLQG1.Palomar.DiskCodeGeometry.domain c j D.toSource := by
  rfl
def finiteClass (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) : MapClass :=
  DLQG1.Palomar.GeometryInterface.classOf (domain p.1 p.2 (drawingData ell n hell p.1))
theorem measurable_finiteClass (ell n : ℕ) (hell : 0 < ell) :
    Measurable (finiteClass ell n hell) := measurable_of_countable _
theorem finiteClass_probability (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    IsProbabilityMeasure ((codeMeasure ell n).map (finiteClass ell n hell)) := by
  letI := codeMeasure_probability ell n hell hle hmod
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_finiteClass ell n hell).aemeasurable).2 inferInstance
def finiteLaw (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) : ProbabilityMeasure MapClass :=
  ⟨(codeMeasure ell n).map (finiteClass ell n hell),
    finiteClass_probability n ell hell hle hmod⟩
theorem finiteLaw_eq_source (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    finiteLaw n ell hell hle hmod =
      Prop516ExteriorAssembly5.finiteGeometricLaw n ell hell hle hmod := by
  letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  apply ProbabilityMeasure.toMeasure_injective
  change (codeMeasure ell n).map
    (fun p : CodeSample ell n => PLCylinderBall.geometricClass
      (domain p.1 p.2 (drawingData ell n hell p.1))) = _
  have hfun : (fun p : CodeSample ell n => PLCylinderBall.geometricClass
      (domain p.1 p.2 (drawingData ell n hell p.1))) =
      (fun p : CodeSample ell n => PLCylinderBall.geometricClass
        (DLQG1.Palomar.DiskCodeGeometry.domain p.1 p.2
          (drawingData ell n hell p.1).toSource)) := by
    funext p
    rw [domain_eq_source]
  rw [hfun]
  exact (DLQG1.Palomar.DiskCodeGeometry.law_independent_of_drawing
    ell n hell hle hmod (fun c => (drawingData ell n hell c).toSource)).trans
      (congrArg ProbabilityMeasure.toMeasure
        (DLQG1.Palomar.DiskCodeGeometry.finiteLaw_eq_source n ell hell hle hmod))
theorem disk_local_limit (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    Tendsto (fun k => finiteLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop
      (nhds DLQG1.Palomar.GeometryLawMinimal.sourceLaw) := by
  have hfun : (fun k => finiteLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) =
      (fun k => Prop516ExteriorAssembly5.finiteGeometricLaw
        (k + 1) (ell k) (hadm k).1 (hadm k).2.1 (hadm k).2.2) := by
    funext k
    exact finiteLaw_eq_source _ _ _ _ _
  rw [hfun, DLQG1.Palomar.GeometryLawMinimal.sourceLaw_eq_source]
  exact DirectedDistances.Paper.Section5.prop_disk_bs_conv A hA ell hadm hlo hhi
end DLQG1.Palomar.DiskMinimal
