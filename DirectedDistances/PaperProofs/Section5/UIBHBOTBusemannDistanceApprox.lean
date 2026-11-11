module

public import DirectedDistances.KMSW.KMSWMeasurability
public import DirectedDistances.KMSW.KMSWWholePlaneFaces
public import DirectedDistances.KMSW.UIBHBOTWholePlaneWord
public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.Recursive.CanonicalBusemannMeasurable
public import DirectedDistances.KMSW.DirectedContainHat
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel

/-! Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
This file defines measurable, hit-indexed run approximants. Identifying the selected
vertices with the geometric UIBHBOT boundary and proving their common-target reachability
remain separate obligations. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW MeasureTheory Filter Quiver

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Measurable selection from a countable discrete index, used for the total hit-time labels. -/
private theorem measurable_select {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] (f : ι → Ω → β) (hf : ∀ i, Measurable (f i))
    (g : Ω → ι) (hg : Measurable g) : Measurable (fun ω => f (g ω) ω) := by
  have h : Measurable (fun p : Ω × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The one-sided code read from time `-1`, so its KMSW run represents the UIBHBOT root window. -/
@[expose] def uibhbotRunCode (W : ℤ → Fin 3) : ℕ → Fin 3 :=
  fun i => W ((i : ℤ) - 2)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The code at each fixed index is measurable in the two-sided product code. -/
private theorem measurable_uibhbotRunCode : Measurable uibhbotRunCode := by
  exact measurable_pi_iff.mpr fun i => measurable_pi_apply ((i : ℤ) - 2)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Measurability of the totalized hit-indexed allocation label on one-sided code space. -/
private theorem measurable_busemannBoundaryIdTotal (k : ℤ) :
    Measurable (fun ω => DirectedDistances.Recursive.busemannBoundaryIdTotal ω k) := by
  exact measurable_select
    (fun n ω => (kmswStage (fun i => ω (i + 1)) n).west
      (kmswStage (fun i => ω (i + 1)) n).active)
    (fun n => measurable_kmswStage_shift_comp n (fun s => s.west s.active))
    (fun ω => (DirectedDistances.Recursive.boundaryHitTimeTotal ω k).toNat)
    ((measurable_of_countable ENat.toNat).comp
      (DirectedDistances.Recursive.measurable_boundaryHitTimeTotal k))

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The west-to-east hit-indexed boundary vertex ID, totalized by the existing first-hit selector.
The ID is a run label; geometric identification is recorded as an open obligation below. -/
@[expose] noncomputable def uibhbotBoundaryId (W : ℤ → Fin 3) (k : ℤ) : ℕ :=
  DirectedDistances.Recursive.busemannBoundaryIdTotal (uibhbotRunCode W) k



theorem measurable_uibhbotBoundaryId (k : ℤ) :
    Measurable (fun W => uibhbotBoundaryId W k) := by
  exact (measurable_busemannBoundaryIdTotal k).comp measurable_uibhbotRunCode

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
On coordinate-hit inputs, the selected ID is the usual hit-indexed run boundary label.
This does not identify that run label with the geometric UIBHBOT boundary. -/
theorem uibhbotBoundaryId_eq_hitIndexedRunVertex (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotRunCode W (i + 1))) (k : ℤ) :
    uibhbotBoundaryId W k =
      boundaryVertex (fun i => uibhbotRunCode W (i + 1)) h k := by
  unfold uibhbotBoundaryId
  unfold DirectedDistances.Recursive.busemannBoundaryIdTotal
  rw [DirectedDistances.Recursive.boundaryHitTimeTotal_eq_boundaryHitTime
    (uibhbotRunCode W) h k, ENat.toNat_natCast, boundaryVertex_eq_edgeWest_hit]
  exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The selected run label as a vertex of the UIBHBOT whole-plane colimit carrier.
Its equality with the source's geometric boundary label is not asserted here. -/
@[expose] noncomputable def uibhbotBoundaryVertex (W : ℤ → Fin 3) (k : ℤ) :
    WholePlaneVertex W :=
  wholePlaneVertexι W 1 (uibhbotBoundaryId W k)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Open geometric identification obligation: adjacent selected labels have the distinct
missing boundary edges of the UIBHBOT. This Prop is not assumed by any declaration here. -/
def uibhbotBoundaryLabelsHaveMissingEdges : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∃ e : ℤ → WholePlaneEdge W,
      (∀ k : ℤ,
        wholePlaneEdgeWest W (e k) = uibhbotBoundaryVertex W k ∧
        wholePlaneEdgeEast W (e k) = uibhbotBoundaryVertex W (k + 1) ∧
        ¬ wholePlaneEdgePresent W (e k)) ∧ Function.Injective e

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The finite-stage LDP approximation, with a reachability bit and zero junk length only
when the bit is false. The length coordinate is not a distance in that case. -/
@[expose] noncomputable def uibhbotStageLdpCode
    (ω : ℕ → Fin 3) (n a b : ℕ) : Bool × ℕ := by
  classical
  let w := fun i => ω (i + 1)
  let x : StagePresentVertex w n := ⟨a⟩
  let y : StagePresentVertex w n := ⟨b⟩
  exact (decide (Reachable x y), (ldpSup x y).unbotD 0)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The UIBHBOT finite-stage LDP approximation on the root run. -/
@[expose] noncomputable def uibhbotStageLdp
    (W : ℤ → Fin 3) (n a b : ℕ) : Bool × ℕ :=
  uibhbotStageLdpCode (uibhbotRunCode W) n a b

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The first coordinate records exactly reachability in the finite stage. -/
theorem uibhbotStageLdpCode_reachable_iff (ω : ℕ → Fin 3) (n a b : ℕ) :
    (uibhbotStageLdpCode ω n a b).1 = true ↔
      Reachable (⟨a⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b⟩ := by
  simp [uibhbotStageLdpCode]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Measurability of the finite-stage reachability-aware LDP approximation. -/
private theorem measurable_uibhbotStageLdpCode (n a b : ℕ) :
    Measurable (fun ω => uibhbotStageLdpCode ω n a b) := by
  apply (measurable_to_bool ?_).prodMk
    (measurable_stage_ldpSup_comp n a b fun z => z.unbotD 0)
  convert measurableSet_stage_reachable n a b using 1
  ext ω
  simp

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Measurability of a finite-stage approximation when its endpoint IDs vary measurably. -/
private theorem measurable_uibhbotStageLdpCode_select
    (n : ℕ) (a b : (ℕ → Fin 3) → ℕ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => uibhbotStageLdpCode ω n (a ω) (b ω)) := by
  have hp : Measurable (fun ω => (a ω, b ω)) := ha.prodMk hb
  exact measurable_select
    (fun p ω => uibhbotStageLdpCode ω n p.1 p.2)
    (fun p => measurable_uibhbotStageLdpCode n p.1 p.2)
    (fun ω => (a ω, b ω)) hp

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Measurability of the UIBHBOT finite-stage approximation for measurable endpoint IDs. -/
theorem measurable_uibhbotStageLdp
    (n : ℕ) (a b : (ℤ → Fin 3) → ℕ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun W => uibhbotStageLdp W n (a W) (b W)) := by
  change Measurable (fun W =>
    uibhbotStageLdpCode (uibhbotRunCode W) n (a W) (b W))
  have hp : Measurable (fun W => (a W, b W)) := ha.prodMk hb
  exact measurable_select
    (fun p W => uibhbotStageLdpCode (uibhbotRunCode W) n p.1 p.2)
    (fun p => by
      simpa only [Function.comp_def] using
        (measurable_uibhbotStageLdpCode n p.1 p.2).comp measurable_uibhbotRunCode)
    (fun W => (a W, b W)) hp

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The LDP approximation to the west-to-east boundary target `x_m^bc`. -/
@[expose] noncomputable def uibhbotBoundaryStageLdp
    (W : ℤ → Fin 3) (n : ℕ) (k : ℤ) (m : ℕ) : Bool × ℕ :=
  uibhbotStageLdp W n (uibhbotBoundaryId W k) (uibhbotBoundaryId W (m : ℤ))

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The boundary-target finite-stage approximation is measurable for each index choice. -/
theorem measurable_uibhbotBoundaryStageLdp (n : ℕ) (k : ℤ) (m : ℕ) :
    Measurable (fun W => uibhbotBoundaryStageLdp W n k m) := by
  exact measurable_uibhbotStageLdp n (uibhbotBoundaryId · k)
    (uibhbotBoundaryId · (m : ℤ)) (measurable_uibhbotBoundaryId k)
    (measurable_uibhbotBoundaryId (m : ℤ))

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The finite-stage distance difference, with default zero unless both directed paths exist. -/
@[expose] noncomputable def uibhbotBoundaryStageDifference
    (W : ℤ → Fin 3) (n : ℕ) (k : ℤ) (m : ℕ) : ℤ :=
  if (uibhbotBoundaryStageLdp W n k m).1 &&
      (uibhbotBoundaryStageLdp W n 0 m).1 then
    ((uibhbotBoundaryStageLdp W n k m).2 : ℤ) -
      (uibhbotBoundaryStageLdp W n 0 m).2
  else 0

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The finite-stage boundary distance difference is measurable; the default is used
when either endpoint pair is unreachable in that stage. -/
theorem measurable_uibhbotBoundaryStageDifference (n : ℕ) (k : ℤ) (m : ℕ) :
    Measurable (fun W => uibhbotBoundaryStageDifference W n k m) := by
  have hpair : Measurable (fun W =>
      (uibhbotBoundaryStageLdp W n k m, uibhbotBoundaryStageLdp W n 0 m)) :=
    (measurable_uibhbotBoundaryStageLdp n k m).prodMk
      (measurable_uibhbotBoundaryStageLdp n 0 m)
  have hf : Measurable (fun p : (Bool × ℕ) × (Bool × ℕ) =>
      if p.1.1 && p.2.1 then (p.1.2 : ℤ) - p.2.2 else 0) :=
    measurable_of_countable _
  change Measurable (fun W =>
    if (uibhbotBoundaryStageLdp W n k m).1 &&
      (uibhbotBoundaryStageLdp W n 0 m).1 then
      ((uibhbotBoundaryStageLdp W n k m).2 : ℤ) -
        (uibhbotBoundaryStageLdp W n 0 m).2
    else 0)
  exact hf.comp hpair

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The eventual finite-stage distance difference, defaulting to zero if the values do not
stabilize or either stage distance is unreachable. This is a measurable representative only. -/
@[expose] noncomputable def uibhbotBoundaryLdpDifference
    (W : ℤ → Fin 3) (k : ℤ) (m : ℕ) : ℤ :=
  eventualIntValue 0 (fun n => uibhbotBoundaryStageDifference W n k m)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Each eventual finite-stage boundary distance difference is measurable in the code. -/
theorem measurable_uibhbotBoundaryLdpDifference (k : ℤ) (m : ℕ) :
    Measurable (fun W => uibhbotBoundaryLdpDifference W k m) := by
  exact measurable_eventualIntValue 0 _
    (fun n => measurable_uibhbotBoundaryStageDifference n k m)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Open stabilization obligation: almost surely, each fixed boundary distance difference
is eventually constant over finite stages. This Prop is not assumed by any declaration here. -/
def uibhbotBoundaryStageDifferenceStabilizes : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∀ k : ℤ, ∀ m : ℕ, ∃ z : ℤ,
      ∀ᶠ n in atTop, uibhbotBoundaryStageDifference W n k m = z

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Open reachability obligation: almost surely, every sufficiently far boundary target is
reachable from both selected labels in some common finite stage. This Prop is not assumed
by any declaration here; its proof needs the UIBHBOT future-map path-containment bridge. -/
def uibhbotBoundaryTailStageReachability : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∀ k : ℤ, ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      ∃ n : ℕ,
        (uibhbotBoundaryStageLdp W n k m).1 = true ∧
        (uibhbotBoundaryStageLdp W n 0 m).1 = true

end DirectedDistances.PaperProofs.Section5
