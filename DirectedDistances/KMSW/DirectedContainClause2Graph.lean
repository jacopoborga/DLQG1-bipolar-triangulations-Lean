module

public import DirectedDistances.KMSW.CutWindowP1FamilyGlue
public import DirectedDistances.KMSW.WindowModelHatCodes
public import DirectedDistances.KMSW.HatImageLimit
public import DirectedDistances.KMSW.ShiftedHatCodes
public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.RPhaseLawTransfer
public import DirectedDistances.KMSW.DirectedContainLaw1

/-! # Conditional graph identification and R-code laws at boundary hits

Helpers for the second law clause of `lem-directed-contain`
identification is conditional on the open deterministic `HatInputExists`.
The code laws hold at both left and right coordinate hits. These statements
neither construct the planar-map carrier nor prove the UIQBOT law as a planar
map. The boundary times here are the coordinate-hit-defined times of
`boundaryHitTime`, with the source boundary-order identification still separate. -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory DirectedDistances.RandomWalk

/-- Conditional graph identification at any integer-indexed boundary hit,
using `hatImageLimit`. This is the graph-level component of the use of
The map is injective on allocated vertices, lifts every path, and has range
exactly the root-reachable vertices. The UIQBOT planar-map law is not asserted. -/
theorem hatCodes_graph_at_boundaryHit_of_hatInput
    (hH : HatInputExists) (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ)
    (hτ : HasFlowLineHits
      (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1))) :
    let w := fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1)
    let u := hatCodes w hτ
    ∃ f : PresentVertex u → PresentVertex w,
      (∀ a b, (∃ m, a.id < (kmswStage u m).nextVertex) →
        (∃ m, b.id < (kmswStage u m).nextVertex) → f a = f b → a = b) ∧
      f ⟨0⟩ = ⟨0⟩ ∧
      (∀ a v (q : Path (f a) v),
        ∃ b, (∃ m, b.id < (kmswStage u m).nextVertex) ∧
          ∃ r : Path a b, f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices) ∧
      Set.range f = {v | Reachable (⟨0⟩ : PresentVertex w) v} := by
  obtain ⟨eφ, vφ, hD⟩ := hH _ hτ
  obtain ⟨f, hInjective, hRoot, hLift, hRange, hReach⟩ := hatImageLimit hD
  refine ⟨f, hInjective, hRoot, ?_, ?_⟩
  · intro a v q
    exact hLift a (kmswVertexAllocated_all _ a) v q
  · ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact hReach a (kmswVertexAllocated_all _ a)
    · intro hv
      obtain ⟨a, _ha, hfa⟩ := hRange v hv
      exact ⟨a, hfa⟩

/-- Almost surely the conditional graph identification holds simultaneously
for every witness and every integer boundary index, including positive
indices. Specialization of the countable all-future-times event supplies
`hτ`; no stopping-time measurability is needed for this specialization.
This is graph-level only, conditional on `HatInputExists`, for
`lem-directed-contain` and `prop-future-map-law` -/
theorem iidCodes_ae_hatCodes_graph_at_all_boundaryHits_of_hatInput
    (hH : HatInputExists) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ k : ℤ,
        ∃ hτ : HasFlowLineHits
          (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1)),
          let w := fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1)
          let u := hatCodes w hτ
          ∃ f : PresentVertex u → PresentVertex w,
            (∀ a b, (∃ m, a.id < (kmswStage u m).nextVertex) →
              (∃ m, b.id < (kmswStage u m).nextVertex) → f a = f b → a = b) ∧
            f ⟨0⟩ = ⟨0⟩ ∧
            (∀ a v (q : Path (f a) v),
              ∃ b, (∃ m, b.id < (kmswStage u m).nextVertex) ∧
                ∃ r : Path a b, f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices) ∧
            Set.range f = {v | Reachable (⟨0⟩ : PresentVertex w) v} := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times] with ω hω
  intro h k
  let hτ := hω (boundaryHitTime (fun j => ω (j + 1)) h k)
  exact ⟨hτ, hatCodes_graph_at_boundaryHit_of_hatInput hH ω h k hτ⟩

/-- The shifted R-code realization equals the hatted graph's code input,
for every supplied flow-line-hit witness. This joins the graph identification
to the code laws below (`lem-directed-contain`,
without asserting a planar-map identification. -/
theorem rCodeSequence_codeShift_boundaryHit_eq_hatCodes
    (ω : ℕ → Fin 3) (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ)
    (hτ : HasFlowLineHits
      (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1))) :
    rCodeSequence (codeShift (boundaryHitTime (fun j => ω (j + 1)) h k) ω) =
      hatCodes (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1)) hτ := by
  rw [← rCodeSequence_quadrantTrajectory_eq_hatCodes _ hτ]
  apply rCodeSequence_eq_of_succ_eq
  intro i
  rfl

private theorem measurable_quadrantTrajectoryOfStageCodes :
    Measurable quadrantTrajectoryOfStageCodes := by
  apply Measurable.of_eval
  intro i
  cases i with
  | zero => exact measurable_const
  | succ i => exact measurable_pi_apply i

/-- At a left coordinate hit the shifted R-code sequence has its time-zero
law. This is the code-level strong Markov composition in
`prop-future-map-law` (lines 44–46). The graph interpretation requires
`HatInputExists`; this code law itself is unconditional and is not a
UIQBOT planar-map law. `codeFstFirstHit_eq_boundaryHitTime` identifies the
time with `boundaryHitTime` whenever boundary-hit witnesses are supplied. -/
theorem iidCodeMeasure_map_rCodeSequence_at_leftBoundaryHit
    (k : ℤ) (_hk : k ≤ -1) :
    iidCodeMeasure.map (fun ω => rCodeSequence
      (codeShift (codeFstFirstHit k ω).toNat ω)) =
      iidCodeMeasure.map rCodeSequence := by
  let F := fun w => rCodeSequence (quadrantTrajectoryOfStageCodes w)
  have hF : Measurable F :=
    measurable_rCodeSequence.comp measurable_quadrantTrajectoryOfStageCodes
  calc
    _ = iidCodeMeasure.map (fun ω => F
        (fun i => ω ((codeFstFirstHit k ω).toNat + i + 1))) := by
      congr 1
      funext ω
      apply rCodeSequence_eq_of_succ_eq
      intro i
      rfl
    _ = iidCodeMeasure.map (fun ω => F (fun i => ω (i + 1))) :=
      iidCodeMeasure_map_futureObject_at_leftHit F hF k
    _ = iidCodeMeasure.map rCodeSequence := by
      congr 1
      funext ω
      apply rCodeSequence_eq_of_succ_eq
      intro i
      rfl

/-- The right-hit counterpart of the left-hit R-code law, using the available
second-coordinate strong Markov theorem. This proves a code law only for
`lem-directed-contain` and its use of `prop-future-map-law`
conditional on `HatInputExists`; the planar-map law remains separate.
`codeSndFirstHit_eq_boundaryHitTime` identifies this time with the boundary
time when its witnesses are supplied. -/
theorem iidCodeMeasure_map_rCodeSequence_at_rightBoundaryHit
    (k : ℤ) (_hk : 1 ≤ k) :
    iidCodeMeasure.map (fun ω => rCodeSequence
      (codeShift (codeSndFirstHit (-k) ω).toNat ω)) =
      iidCodeMeasure.map rCodeSequence := by
  let F := fun w => rCodeSequence (quadrantTrajectoryOfStageCodes w)
  have hF : Measurable F :=
    measurable_rCodeSequence.comp measurable_quadrantTrajectoryOfStageCodes
  calc
    _ = iidCodeMeasure.map (fun ω => F
        (fun i => ω ((codeSndFirstHit (-k) ω).toNat + i + 1))) := by
      congr 1
      funext ω
      apply rCodeSequence_eq_of_succ_eq
      intro i
      rfl
    _ = iidCodeMeasure.map (fun ω => F (fun i => ω (i + 1))) :=
      iidCodeMeasure_map_futureObject_at_rightHit F hF k
    _ = iidCodeMeasure.map rCodeSequence := by
      congr 1
      funext ω
      apply rCodeSequence_eq_of_succ_eq
      intro i
      rfl

/-- At left boundary hits the R codes have the Pitman-flipped iid code law
of `map_rCodeSequence`. This is a code-level consequence for
`lem-directed-contain` and `prop-future-map-law`
law as a planar map. -/
theorem iidCodeMeasure_map_rCodeSequence_at_leftBoundaryHit_eq_pitmanCode
    (k : ℤ) (hk : k ≤ -1) :
    iidCodeMeasure.map (fun ω => rCodeSequence
      (codeShift (codeFstFirstHit k ω).toNat ω)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) :=
  (iidCodeMeasure_map_rCodeSequence_at_leftBoundaryHit k hk).trans map_rCodeSequence

/-- At right boundary hits the R codes have the Pitman-flipped iid code law.
This is the right-hit code-level consequence for `lem-directed-contain`
without a planar-map law assertion. -/
theorem iidCodeMeasure_map_rCodeSequence_at_rightBoundaryHit_eq_pitmanCode
    (k : ℤ) (hk : 1 ≤ k) :
    iidCodeMeasure.map (fun ω => rCodeSequence
      (codeShift (codeSndFirstHit (-k) ω).toNat ω)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) :=
  (iidCodeMeasure_map_rCodeSequence_at_rightBoundaryHit k hk).trans map_rCodeSequence

end DirectedDistances.KMSW
