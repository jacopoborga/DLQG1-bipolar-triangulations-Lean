module
public import DirectedDistances.Paper.Section1.BusemannConvergence
import all DirectedDistances.Probability.SkorokhodJ1WholeLineLocal
@[expose] public section
namespace DLQG1.Palomar.Model.Probability
open MeasureTheory Filter TopologicalSpace
open scoped Topology
abbrev J1Window (T : ℝ) := Set.Icc (0 : ℝ) T
abbrev CadlagWindow (T : ℝ) := {f : J1Window T → ℝ // IsCadlag f}
abbrev J1TimeChange (T : ℝ) := OrderIso (J1Window T) (J1Window T)
noncomputable def j1WindowDist {T : ℝ} (_hT : 0 < T) (f g : CadlagWindow T) : ℝ :=
  ⨅ φ : J1TimeChange T, max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
    (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)
abbrev CadlagLocal := {f : Set.Ici (0 : ℝ) → ℝ // IsCadlag f}
noncomputable def localCutoff (n : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  max 0 (min 1 ((n : ℝ) + 1 - (t : ℝ)))
def localWindowTime {T : ℝ} (t : J1Window T) : Set.Ici (0 : ℝ) := ⟨t.1, t.2.1⟩
theorem cutoffWindow_isCadlag (n : ℕ) (x : CadlagLocal) :
    IsCadlag (fun t : J1Window ((n : ℝ) + 1) =>
      x.1 (localWindowTime t) * localCutoff n (localWindowTime t)) :=
  (DirectedDistances.Probability.cutoffWindow n x).property
noncomputable def cutoffWindow (n : ℕ) (x : CadlagLocal) : CadlagWindow ((n : ℝ) + 1) :=
  ⟨fun t => x.1 (localWindowTime t) * localCutoff n (localWindowTime t), cutoffWindow_isCadlag n x⟩
noncomputable def localJ1Term (n : ℕ) (x y : CadlagLocal) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1) * min 1 (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y))
noncomputable def j1LocalDist (x y : CadlagLocal) : ℝ := ∑' n : ℕ, localJ1Term n x y
theorem j1LocalDist_self (x : CadlagLocal) : j1LocalDist x x = 0 := by
  let := DirectedDistances.Probability.j1LocalMetricSpace
  change dist x x = 0
  exact dist_self x
theorem j1LocalDist_symm (x y : CadlagLocal) : j1LocalDist x y = j1LocalDist y x :=
  DirectedDistances.Probability.j1LocalDist_symm x y
theorem j1LocalDist_triangle (x y z : CadlagLocal) :
    j1LocalDist x z ≤ j1LocalDist x y + j1LocalDist y z :=
  DirectedDistances.Probability.j1LocalDist_triangle x y z
theorem j1LocalDist_eq_zero_iff (x y : CadlagLocal) : j1LocalDist x y = 0 ↔ x = y :=
  DirectedDistances.Probability.j1LocalDist_eq_zero_iff x y
@[instance_reducible] noncomputable instance j1LocalMetricSpace : MetricSpace CadlagLocal where
  dist := j1LocalDist
  dist_self := j1LocalDist_self
  dist_comm := j1LocalDist_symm
  dist_triangle := j1LocalDist_triangle
  eq_of_dist_eq_zero := fun h => (j1LocalDist_eq_zero_iff _ _).mp h
@[instance_reducible] noncomputable instance j1LocalTopologicalSpace : TopologicalSpace CadlagLocal :=
  j1LocalMetricSpace.toUniformSpace.toTopologicalSpace
@[instance_reducible] noncomputable instance j1LocalMeasurableSpace : MeasurableSpace CadlagLocal :=
  borel CadlagLocal
instance j1LocalBorelSpace : BorelSpace CadlagLocal := ⟨rfl⟩
abbrev CadlagLocalZero := {x : CadlagLocal // x.1 ⟨0, le_rfl⟩ = 0}
abbrev WholeLineCadlag := {f : ℝ → ℝ // IsCadlag f}
def wholeLineJ1Cutoff (m : ℕ) (t : ℝ) : ℝ := max 0 (min 1 ((m : ℝ) + 1 - |t|))
def wholeLineJ1WindowTime (m : ℕ) (u : J1Window (2 * ((m : ℝ) + 1))) : ℝ :=
  (u : ℝ) - ((m : ℝ) + 1)
theorem wholeLineJ1WindowPath_cadlag (m : ℕ) (f : WholeLineCadlag) :
    IsCadlag (fun u : J1Window (2 * ((m : ℝ) + 1)) =>
      wholeLineJ1Cutoff m (wholeLineJ1WindowTime m u) * f.1 (wholeLineJ1WindowTime m u)) :=
  (DirectedDistances.Probability.wholeLineJ1WindowPath m f).property
noncomputable def wholeLineJ1WindowPath (m : ℕ) (f : WholeLineCadlag) :
    CadlagWindow (2 * ((m : ℝ) + 1)) :=
  ⟨fun u => wholeLineJ1Cutoff m (wholeLineJ1WindowTime m u) *
    f.1 (wholeLineJ1WindowTime m u), wholeLineJ1WindowPath_cadlag m f⟩
noncomputable def wholeLineJ1WindowDistance (m : ℕ) (f g : WholeLineCadlag) : ℝ :=
  j1WindowDist (by positivity : 0 < 2 * ((m : ℝ) + 1))
    (wholeLineJ1WindowPath m f) (wholeLineJ1WindowPath m g)
noncomputable def wholeLineLocalJ1Term (m : ℕ) (f g : WholeLineCadlag) : ℝ :=
  (1 / 2 : ℝ) ^ (m + 1) * min 1 (wholeLineJ1WindowDistance m f g)
noncomputable def wholeLineLocalJ1Distance (f g : WholeLineCadlag) : ℝ :=
  ∑' m : ℕ, wholeLineLocalJ1Term m f g
theorem wholeLineLocalJ1Distance_self (x : WholeLineCadlag) : wholeLineLocalJ1Distance x x = 0 :=
  DirectedDistances.Probability.wholeLineLocalJ1Distance_self x
theorem wholeLineLocalJ1Distance_symm (x y : WholeLineCadlag) :
    wholeLineLocalJ1Distance x y = wholeLineLocalJ1Distance y x :=
  DirectedDistances.Probability.wholeLineLocalJ1Distance_symm x y
theorem wholeLineLocalJ1Distance_triangle (x y z : WholeLineCadlag) :
    wholeLineLocalJ1Distance x z ≤ wholeLineLocalJ1Distance x y + wholeLineLocalJ1Distance y z :=
  DirectedDistances.Probability.wholeLineLocalJ1Distance_triangle x y z
theorem wholeLineLocalJ1Distance_eq_zero_iff (x y : WholeLineCadlag) :
    wholeLineLocalJ1Distance x y = 0 ↔ x = y :=
  DirectedDistances.Probability.wholeLineLocalJ1Distance_eq_zero_iff x y
@[instance_reducible] noncomputable instance wholeLineLocalMetricSpace : MetricSpace WholeLineCadlag where
  dist := wholeLineLocalJ1Distance
  dist_self := wholeLineLocalJ1Distance_self
  dist_comm := wholeLineLocalJ1Distance_symm
  dist_triangle := wholeLineLocalJ1Distance_triangle
  eq_of_dist_eq_zero := fun h => (wholeLineLocalJ1Distance_eq_zero_iff _ _).mp h
@[instance_reducible] noncomputable instance wholeLineLocalTopologicalSpace :
    TopologicalSpace WholeLineCadlag := wholeLineLocalMetricSpace.toUniformSpace.toTopologicalSpace
@[instance_reducible] noncomputable instance wholeLineLocalMeasurableSpace :
    MeasurableSpace WholeLineCadlag := borel WholeLineCadlag
instance wholeLineLocalBorelSpace : BorelSpace WholeLineCadlag := ⟨rfl⟩
noncomputable def leftLimitReversal (y : CadlagLocal) : Set.Ici (0 : ℝ) → ℝ := fun s => y.1.leftLim s
noncomputable def wholeLineGlue (x y : CadlagLocal)
    (_hx0 : x.1 ⟨0, le_rfl⟩ = 0) (_hy0 : y.1 ⟨0, le_rfl⟩ = 0) : ℝ → ℝ :=
  fun t => if ht : t ∈ Set.Ici (0 : ℝ) then x.1 ⟨t, ht⟩ else
    leftLimitReversal y ⟨-t, neg_nonneg.mpr (le_of_lt (lt_of_not_ge (by simpa using ht)))⟩
theorem wholeLineGlue_isCadlag (x y : CadlagLocal)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0) :
    IsCadlag (wholeLineGlue x y hx0 hy0) :=
  DirectedDistances.Probability.wholeLineGlue_isCadlag x y hx0 hy0
noncomputable def wholeLineGlueCadlag (x y : CadlagLocal)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0) : WholeLineCadlag :=
  ⟨wholeLineGlue x y hx0 hy0, wholeLineGlue_isCadlag x y hx0 hy0⟩
noncomputable def wholeLineGlueZero (p : CadlagLocalZero × CadlagLocalZero) : WholeLineCadlag :=
  wholeLineGlueCadlag p.1.val p.2.val p.1.property p.2.property
noncomputable def probabilityProduct {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : ProbabilityMeasure (X × Y) :=
  ⟨(μ : Measure X).prod (ν : Measure Y), inferInstance⟩
theorem local_metric_eq_source :
    j1LocalMetricSpace = DirectedDistances.Probability.j1LocalMetricSpace := rfl
theorem wholeline_metric_eq_source :
    wholeLineLocalMetricSpace = DirectedDistances.Probability.wholeLineLocalMetricSpace := by
  apply MetricSpace.ext
  rfl
theorem glue_eq_source : wholeLineGlueZero = DirectedDistances.Probability.wholeLineGlueZero := rfl
theorem local_topology_eq_source :
    j1LocalTopologicalSpace = DirectedDistances.Probability.j1LocalTopologicalSpace := rfl
theorem local_measurable_eq_source :
    j1LocalMeasurableSpace = DirectedDistances.Probability.j1LocalMeasurableSpace := rfl
theorem wholeline_topology_eq_source :
    wholeLineLocalTopologicalSpace = DirectedDistances.Probability.wholeLineLocalTopologicalSpace := by
  unfold wholeLineLocalTopologicalSpace DirectedDistances.Probability.wholeLineLocalTopologicalSpace
  rw [wholeline_metric_eq_source]
theorem wholeline_measurable_eq_source :
    wholeLineLocalMeasurableSpace = DirectedDistances.Probability.wholeLineLocalMeasurableSpace := by
  unfold wholeLineLocalMeasurableSpace DirectedDistances.Probability.wholeLineLocalMeasurableSpace
  rw [wholeline_topology_eq_source]
end DLQG1.Palomar.Model.Probability

namespace DLQG1.Palomar.Model.PaperProofs.Section1
open MeasureTheory
open DLQG1.Palomar.Model.Probability
@[expose] def StablePartitionLaw (Ψ : ℝ → ℂ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  ∀ (k : ℕ) (t : Fin (k + 1) → Set.Ici (0 : ℝ)),
    (t 0 : ℝ) = 0 → Monotone t → ∀ u : Fin k → ℝ,
    (∫ x : CadlagLocalZero, Complex.exp
      (((∑ j : Fin k, u j *
        (x.1.1 (t j.succ) - x.1.1 (t j.castSucc)) : ℝ) : ℂ) * Complex.I)
        ∂(μ : Measure CadlagLocalZero)) =
      ∏ j : Fin k, Complex.exp
        (-((((t j.succ : ℝ) - (t j.castSucc : ℝ) : ℝ) : ℂ) * Ψ (u j)))


@[expose] def LdpStableHalfLaw (a : ℝ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  0 < a ∧ StablePartitionLaw (fun u =>
    ((a / 2 : ℝ) : ℂ) * (|u| ^ (2 / 3 : ℝ) : ℝ) *
      (1 + Complex.I * (Real.sqrt 3 : ℂ) *
        ((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) : ℂ))) μ


@[expose] def SdpStableHalfLaw (b : ℝ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  0 < b ∧ StablePartitionLaw (fun u =>
    ((b / 2 : ℝ) : ℂ) * (|u| ^ (4 / 3 : ℝ) : ℝ) *
      (1 + Complex.I * (Real.sqrt 3 : ℂ) *
        ((if 0 < u then (1 : ℝ) else if u < 0 then -1 else 0) : ℂ))) μ


@[expose] def SymmetricStableProcessLaw (α c : ℝ)
    (μ : ProbabilityMeasure CadlagLocalZero) : Prop :=
  0 < α ∧ α ≤ 2 ∧ 0 < c ∧
    StablePartitionLaw (fun u => (c : ℂ) * (|u| ^ α : ℝ)) μ


theorem stablePartitionLaw_eq_source :
    StablePartitionLaw = DirectedDistances.PaperProofs.Section1.StablePartitionLaw := rfl
theorem ldpStableHalfLaw_eq_source :
    LdpStableHalfLaw = DirectedDistances.PaperProofs.Section1.LdpStableHalfLaw := rfl
theorem sdpStableHalfLaw_eq_source :
    SdpStableHalfLaw = DirectedDistances.PaperProofs.Section1.SdpStableHalfLaw := rfl
theorem symmetricStableProcessLaw_eq_source :
    SymmetricStableProcessLaw = DirectedDistances.PaperProofs.Section1.SymmetricStableProcessLaw := rfl
end DLQG1.Palomar.Model.PaperProofs.Section1

namespace DLQG1.Palomar.Model.Probability
theorem floorStep_isCadlag (X : ℤ → ℝ) (a b : ℝ) (hb : 0 < b) :
    IsCadlag (fun t : ℝ => a * X ⌊b * t⌋) :=
  DirectedDistances.Probability.floorStep_isCadlag X a b hb
noncomputable def ldpScalingPath (X : ℤ → ℤ) (n : ℕ) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
    (X ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (X j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩
noncomputable def sdpScalingPath (X : ℤ → ℤ) (n : ℕ) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    (X ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (X j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩
theorem source_ldpScalingPath_eq (n : ℕ) (W : ℤ → Fin 3) :
    ldpScalingPath (DirectedDistances.PaperProofs.Section7.identifiedLDPBusemann W) n =
      DirectedDistances.PaperProofs.Section1.identifiedLDPScalingPath n W := rfl
theorem source_sdpScalingPath_eq (n : ℕ) (W : ℤ → Fin 3) :
    sdpScalingPath (DirectedDistances.PaperProofs.Section7.identifiedSDPBusemann W) n =
      DirectedDistances.PaperProofs.Section1.identifiedSDPScalingPath n W := rfl
end DLQG1.Palomar.Model.Probability

namespace DLQG1.Palomar.Model.PaperProofs.Section1
open MeasureTheory Filter
open DLQG1.Palomar.Model.Probability
open scoped Topology
/-- Exact existing scalar processes, viewed in the independently defined path carrier.
This intermediate transport does not define the final Model scalar processes. -/
noncomputable def sourceLDPScalingPath (n : ℕ) (W : ℤ → Fin 3) : WholeLineCadlag :=
  ldpScalingPath (DirectedDistances.PaperProofs.Section7.identifiedLDPBusemann W) n
noncomputable def sourceSDPScalingPath (n : ℕ) (W : ℤ → Fin 3) : WholeLineCadlag :=
  sdpScalingPath (DirectedDistances.PaperProofs.Section7.identifiedSDPBusemann W) n
theorem aemeasurable_sourceLDPScalingPath (n : ℕ) :
    AEMeasurable (sourceLDPScalingPath n) DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure := by
  exact DirectedDistances.PaperProofs.Section1.aemeasurable_identifiedLDPScalingPath n
theorem aemeasurable_sourceSDPScalingPath (n : ℕ) :
    AEMeasurable (sourceSDPScalingPath n) DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure := by
  exact DirectedDistances.PaperProofs.Section1.aemeasurable_identifiedSDPScalingPath n
noncomputable def sourceLDPScalingLaw (n : ℕ) : ProbabilityMeasure WholeLineCadlag :=
  ⟨DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure.map (sourceLDPScalingPath n),
    (Measure.isProbabilityMeasure_map_iff (aemeasurable_sourceLDPScalingPath n)).2 inferInstance⟩
noncomputable def sourceSDPScalingLaw (n : ℕ) : ProbabilityMeasure WholeLineCadlag :=
  ⟨DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure.map (sourceSDPScalingPath n),
    (Measure.isProbabilityMeasure_map_iff (aemeasurable_sourceSDPScalingPath n)).2 inferInstance⟩
theorem full_functional_scaling_source_transport :
    ∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
      SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
      Tendsto sourceLDPScalingLaw atTop (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto sourceSDPScalingLaw atTop (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero)) := by
  exact DirectedDistances.Paper.Section1.thm_busemann_conv.2.2
end DLQG1.Palomar.Model.PaperProofs.Section1
