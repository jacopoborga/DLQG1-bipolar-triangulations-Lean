/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusMeasurableClass

/-! # Coordinate measurability of the coherent geometric right side

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`),
permanent-ID fields on the coherent path subtype, not a choice of code preimage. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Decode the path on its coherent subtype measurably. -/
private theorem measurable_coherentPathCode (x : XDP) :
    Measurable (fun q : Coherent x => pathCode q.1) :=
  measurable_pathCode.comp measurable_subtype_coe

/-- Helper toward Lemma 5.5. Each west endpoint is determined by a finite path prefix. -/
theorem measurable_geometricRightSide_west (x : XDP) (n : ℕ) :
    Measurable (fun q : Coherent x =>
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).west n) := by
  exact (measurable_of_factors_prefix (n + 1)
    (fun c => edgeWest (boltzmannKMSWStream c) n) (by
      intro c c' h
      unfold edgeWest boltzmannKMSWStream
      rw [kmswStage_congr (fun i hi => h (i + 1) (by omega))])).comp
        (measurable_coherentPathCode x)

/-- Helper toward Lemma 5.5. Each east endpoint is determined by a finite path prefix. -/
theorem measurable_geometricRightSide_east (x : XDP) (n : ℕ) :
    Measurable (fun q : Coherent x =>
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).east n) := by
  exact (measurable_of_factors_prefix (n + 1)
    (fun c => edgeEast (boltzmannKMSWStream c) n) (by
      intro c c' h
      unfold edgeEast boltzmannKMSWStream
      rw [kmswStage_congr (fun i hi => h (i + 1) (by omega))])).comp
        (measurable_coherentPathCode x)

/-- Helper toward Lemma 5.5. Permanent presence is a countable union of stage events;
missing geometric edges are not discarded by this statement. -/
theorem measurableSet_geometricRightSide_present (x : XDP) (n : ℕ) :
    MeasurableSet {q : Coherent x |
      n ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).present} := by
  change MeasurableSet {q : Coherent x | ∃ j,
    n < (kmswStage (boltzmannKMSWStream (pathCode q.1)) j).nextEdge ∧
      (kmswStage (boltzmannKMSWStream (pathCode q.1)) j).present n = true}
  have hstage (j : ℕ) : MeasurableSet {q : Coherent x |
      n < (kmswStage (boltzmannKMSWStream (pathCode q.1)) j).nextEdge ∧
        (kmswStage (boltzmannKMSWStream (pathCode q.1)) j).present n = true} := by
    exact (measurableSet_of_factors_prefix (j + 1)
      (fun c => n < (kmswStage (boltzmannKMSWStream c) j).nextEdge ∧
        (kmswStage (boltzmannKMSWStream c) j).present n = true) (by
      intro c c' h
      unfold boltzmannKMSWStream
      rw [kmswStage_congr (fun i hi => h (i + 1) (by omega))])).preimage
        (measurable_coherentPathCode x)
  simpa only [Set.iUnion_ofPred] using MeasurableSet.iUnion hstage

/-- Helper toward Lemma 5.5. The Boolean presence coordinate is measurable. -/
theorem measurable_geometricRightSide_present (x : XDP) (n : ℕ) :
    Measurable (fun q : Coherent x => decide
      (n ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).present)) := by
  have heq : (fun q : Coherent x => decide
      (n ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).present)) =
      (fun q : Coherent x =>
        if n ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).present
        then true else false) := by
    funext q
    split <;> simp_all only [decide_true, decide_false]
  rw [heq]
  exact measurable_const.ite (measurableSet_geometricRightSide_present x n) measurable_const

/-- Helper toward Lemma 5.5. The source root is the constant permanent vertex ID zero. -/
theorem measurable_geometricRightSide_root (x : XDP) :
    Measurable (fun q : Coherent x =>
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).root) :=
  measurable_const

/-- Helper toward Lemma 5.5. Select a right record using measurable count thresholds. -/
private theorem measurable_rightRecordSelect (i : ℕ) :
    Measurable (fun c : ℕ → Fin 3 => natSelect
      (fun m => ∀ j, j < m →
        R (boltzmannKMSWStream c) m < R (boltzmannKMSWStream c) j) i) := by
  let P : (ℕ → Fin 3) → ℕ → Prop := fun c m =>
    ∀ j, j < m → R (boltzmannKMSWStream c) m < R (boltzmannKMSWStream c) j
  have hP (m : ℕ) : MeasurableSet {c | P c m} := by
    exact measurableSet_of_factors_prefix (m + 1) _ (by
      intro c c' h
      have hr (j : ℕ) (hj : j ≤ m) :
          R (boltzmannKMSWStream c) j = R (boltzmannKMSWStream c') j :=
        R_congr (fun k hk => h (k + 1) (by omega))
      unfold P
      constructor <;> intro hc j hj
      · rw [← hr m le_rfl, ← hr j (by omega)]
        exact hc j hj
      · rw [hr m le_rfl, hr j (by omega)]
        exact hc j hj)
  have hcount (n : ℕ) : Measurable (fun q => Nat.count (P q) n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      simp only [Nat.count_succ]
      exact ih.add (measurable_const.ite (hP n) measurable_const)
  have hthreshold (m : ℕ) : MeasurableSet {q | i < Nat.count (P q) (m + 1)} :=
    (hcount (m + 1)) (Set.to_countable {n : ℕ | i < n}).measurableSet
  have hE : MeasurableSet {q | ∃ m, i < Nat.count (P q) (m + 1)} := by
    simpa only [Set.iUnion_ofPred] using MeasurableSet.iUnion hthreshold
  have hfind : Measurable (fun q : {q : (ℕ → Fin 3) | ∃ m, i < Nat.count (P q) (m + 1)} =>
      Nat.find q.2) :=
    measurable_find (fun q => q.2) (fun m => (hthreshold m).preimage measurable_subtype_coe)
  convert hfind.dite measurable_const hE using 1
  funext c
  simp only [natSelect, P]
  congr 2

/-- Helper toward Lemma 5.5. Read the active edge at a selected right record. -/
private theorem measurable_rightBoundaryEdge (i : ℕ) :
    Measurable (fun c : ℕ → Fin 3 => kmswRightBoundaryEdge (boltzmannKMSWStream c) i) := by
  have hact (m : ℕ) :
      Measurable (fun c : ℕ → Fin 3 => act (boltzmannKMSWStream c) m) := by
    refine measurable_of_factors_prefix (m + 1) _ ?_
    intro c c' h
    unfold act boltzmannKMSWStream
    rw [kmswStage_congr (fun k hk => h (k + 1) (by omega))]
  have hpair : Measurable (fun z : ℕ × (ℕ → Fin 3) =>
      act (boltzmannKMSWStream z.2) z.1) :=
    measurable_from_prod_countable_right hact
  simpa only [kmswRightBoundaryEdge, Function.comp_def, id_eq] using
    hpair.comp ((measurable_rightRecordSelect i).prodMk measurable_id)

/-- Helper toward Lemma 5.5. Each right boundary dart is read from a measurable
right-record index and a finite stage, retaining its permanent edge ID. -/
theorem measurable_geometricRightSide_boundary (x : XDP) (i : ℕ) :
    Measurable (fun q : Coherent x =>
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).boundary i) := by
  have heq : (fun q : Coherent x =>
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).boundary i) =
      (fun q : Coherent x =>
        (kmswRightBoundaryEdge (boltzmannKMSWStream (pathCode q.1)) i, false)) := by
    funext q
    exact ancestor_boundaryDart_eq _
      (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q) .right i
  rw [heq]
  exact ((measurable_rightBoundaryEdge i).comp (measurable_coherentPathCode x)).prodMk
    measurable_const

/-- Helper toward Lemma 5.5. The complete endpoint, presence, root and boundary
field families are jointly measurable, with the product sigma algebras. -/
theorem measurable_geometricRightSide_incidenceCode (x : XDP) :
    Measurable (fun q : Coherent x =>
      let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
      (M.west, M.east, (fun n => decide (n ∈ M.present)), M.root, M.boundary)) := by
  exact (measurable_pi_iff.mpr (measurable_geometricRightSide_west x)).prodMk
    ((measurable_pi_iff.mpr (measurable_geometricRightSide_east x)).prodMk
      ((measurable_pi_iff.mpr (measurable_geometricRightSide_present x)).prodMk
        ((measurable_geometricRightSide_root x).prodMk
          (measurable_pi_iff.mpr (measurable_geometricRightSide_boundary x)))))





























































end DirectedDistances.PaperProofs.Section5
