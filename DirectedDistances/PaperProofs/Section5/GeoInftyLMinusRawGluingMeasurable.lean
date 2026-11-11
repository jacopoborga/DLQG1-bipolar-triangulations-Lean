/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusClassLocality

/-! raw edge labels, this records measurability of the actual cross-block gluing
generator: a permanent primed boundary edge label agrees with the hatted
left-boundary edge at the same boundary index. The statement retains raw edge
identity and does not assert measurability of the generated quotient class. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The concrete raw-token gluing event for fixed
primed and hatted edge labels. The second code is the hatted path itself;
`pathCode` is used by the existing coherent-side construction. -/
@[expose] def lMinusRawCodeEdgeGluing
    {x : XDP} (r : LMinusSidePresentation x) (q : ℕ → ℤ × ℤ)
    (a b : ℕ) : Prop :=
  ∃ i, lMinusPrimedBoundaryEdge r.code.1 i a ∧
    kmswLeftBoundaryEdge (boltzmannKMSWStream (pathCode q)) i = b

/-- Helper toward Lemma 5.5. For a coherent hatted path, the raw-token event
is exactly the existing decoder-4 edge-gluing generator. -/
theorem lMinusRawCodeEdgeGluing_iff_codeEdgeGluing
    {x : XDP} (r : LMinusSidePresentation x) (q : Coherent x)
    (a : ℕ) (b : (lMinusCoherentLeftSide x q).edges) :
    lMinusRawCodeEdgeGluing r q.1 a b.val ↔
      lMinusCodeEdgeGluing r (lMinusCoherentLeftSide x q)
        (.inl a) (.inr b) := by
  simp only [lMinusRawCodeEdgeGluing, lMinusCodeEdgeGluing]
  rfl

/-- Helper toward Lemma 5.5. Each fixed primed boundary-edge event is
measurable, by expressing permanence as a countable union of finite-stage
prefix tests. -/
private theorem measurableSet_lMinusPrimedBoundaryEdge_code (i e : ℕ) :
    MeasurableSet {p : ℕ → Fin 3 | lMinusPrimedBoundaryEdge p i e} := by
  have hstage (n : ℕ) : Measurable
      (fun p : ℕ → Fin 3 => (kmswStage p n).UR.reverse[i]? = some e) := by
    apply measurable_of_factors_prefix n
    intro p p' hp
    rw [kmswStage_congr hp]
  apply measurableSet_setOfPred.mpr
  change Measurable (fun p : ℕ → Fin 3 =>
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (kmswStage p n).UR.reverse[i]? = some e)
  exact Measurable.exists (fun N => Measurable.forall (fun n =>
    measurable_const.imp (hstage n)))

/-- Helper toward Lemma 5.5. The hatted left-boundary edge at a fixed index
is measurable as a function of its path code. The record predicate is a
countable intersection of measurable coordinate inequalities, and the
selected record is obtained by measurable count thresholds. -/
private theorem measurable_lMinusLeftBoundaryEdge (i : ℕ) :
    Measurable (fun c : ℕ → Fin 3 =>
      kmswLeftBoundaryEdge (boltzmannKMSWStream c) i) := by
  let P : (ℕ → Fin 3) → ℕ → Prop := fun c m =>
    ∀ j, m < j → L (boltzmannKMSWStream c) m + 1 ≤
      L (boltzmannKMSWStream c) j
  have hL (n : ℕ) : Measurable (fun c : ℕ → Fin 3 =>
      L (boltzmannKMSWStream c) n) := by
    refine measurable_of_factors_prefix (n + 1) _ ?_
    intro c c' hc
    apply L_congr
    intro j hj
    simpa only [boltzmannKMSWStream] using hc (j + 1) (by omega)
  have hP (m : ℕ) : MeasurableSet {c : ℕ → Fin 3 | P c m} := by
    have hset : {c : ℕ → Fin 3 | P c m} =
        ⋂ j : ℕ, ⋂ (_ : m < j),
          {c : ℕ → Fin 3 |
            L (boltzmannKMSWStream c) m + 1 ≤
              L (boltzmannKMSWStream c) j} := by
      ext c
      simp only [Set.mem_iInter, Set.mem_setOf_eq, P]
    rw [hset]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
      measurableSet_le ((hL m).add_const 1) (hL j)))
  have hcount (n : ℕ) : Measurable (fun c : ℕ → Fin 3 => Nat.count (P c) n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      simp only [Nat.count_succ]
      exact ih.add (measurable_const.ite (hP n) measurable_const)
  have hthreshold (m : ℕ) : MeasurableSet {c : ℕ → Fin 3 |
      i < Nat.count (P c) (m + 1)} :=
    (hcount (m + 1)) (Set.to_countable {n : ℕ | i < n}).measurableSet
  have hE : MeasurableSet {c : ℕ → Fin 3 |
      ∃ m, i < Nat.count (P c) (m + 1)} := by
    simpa only [Set.iUnion_ofPred] using MeasurableSet.iUnion hthreshold
  have hfind : Measurable (fun c : {c : ℕ → Fin 3 |
      ∃ m, i < Nat.count (P c) (m + 1)} => Nat.find c.2) :=
    measurable_find (fun c => c.2) (fun m =>
      (hthreshold m).preimage measurable_subtype_coe)
  have hselect : Measurable (fun c : ℕ → Fin 3 => natSelect (P c) i) := by
    convert hfind.dite measurable_const hE using 1
    funext c
    simp only [natSelect, P]
    congr 2
  have hact (m : ℕ) : Measurable (fun c : ℕ → Fin 3 =>
      act (boltzmannKMSWStream c) m) := by
    refine measurable_of_factors_prefix (m + 1) _ ?_
    intro c c' hc
    unfold act boltzmannKMSWStream
    rw [kmswStage_congr (fun j hj => hc (j + 1) (by omega))]
  have hpair : Measurable (fun z : ℕ × (ℕ → Fin 3) =>
      act (boltzmannKMSWStream z.2) z.1) :=
    measurable_from_prod_countable_right hact
  simpa only [kmswLeftBoundaryEdge, P, Function.comp_def, id_eq] using
    hpair.comp (hselect.prodMk measurable_id)

/-- Helper toward Lemma 5.5. For every fixed pair of raw edge labels, the
actual gluing-generator relation is measurable on presentation/path pairs. -/
theorem measurableSet_lMinusRawCodeEdgeGluing
    (x : XDP) (a b : ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      lMinusRawCodeEdgeGluing z.1 z.2 a b} := by
  have hprimed (i : ℕ) : MeasurableSet
      {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
        lMinusPrimedBoundaryEdge z.1.code.1 i a} := by
    exact (measurableSet_lMinusPrimedBoundaryEdge_code i a).preimage
      ((measurable_lMinusSidePresentation_code x).fst.comp measurable_fst)
  have hhatted (i : ℕ) : MeasurableSet
      {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
        kmswLeftBoundaryEdge (boltzmannKMSWStream (pathCode z.2)) i = b} := by
    have hm : Measurable (fun z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) =>
        kmswLeftBoundaryEdge (boltzmannKMSWStream (pathCode z.2)) i) :=
      (measurable_lMinusLeftBoundaryEdge i).comp
        (measurable_pathCode.comp measurable_snd)
    exact (hm.eq_const b).setOf
  have hset : {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      lMinusRawCodeEdgeGluing z.1 z.2 a b} =
      ⋃ i : ℕ,
        {z | lMinusPrimedBoundaryEdge z.1.code.1 i a} ∩
        {z | kmswLeftBoundaryEdge
          (boltzmannKMSWStream (pathCode z.2)) i = b} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq,
      lMinusRawCodeEdgeGluing]
  rw [hset]
  exact MeasurableSet.iUnion (fun i => (hprimed i).inter (hhatted i))

/-- Helper toward Lemma 5.5. For each fixed pair of raw edge labels, the
concrete gluing-generator indicator is a.e.-measurable as a function of the
iid source code. -/
theorem aemeasurable_lMinusRawCodeEdgeGluing_source
    (x : XDP) (k : ℤ) (a b : ℕ) :
    AEMeasurable (fun W : ℤ → Fin 3 =>
      decide (lMinusRawCodeEdgeGluing
        (decodeLMinus x k (leftSideObsNonpos x k W))
        (boundaryFutureHattedPath k W) a b)) wholePlaneIIDCodeMeasure := by
  have hbool : Measurable
      (fun z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) =>
        decide (lMinusRawCodeEdgeGluing z.1 z.2 a b)) := by
    apply measurable_to_bool
    change MeasurableSet {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      decide (lMinusRawCodeEdgeGluing z.1 z.2 a b) = true}
    simpa only [decide_eq_true_eq] using
      measurableSet_lMinusRawCodeEdgeGluing x a b
  have hpair : AEMeasurable (fun W : ℤ → Fin 3 =>
      (decodeLMinus x k (leftSideObsNonpos x k W),
        boundaryFutureHattedPath k W)) wholePlaneIIDCodeMeasure :=
    (aemeasurable_decodeLMinus_leftSideObsNonpos x k).prodMk
      (aemeasurable_boundaryFutureHattedPath k)
  exact hbool.comp_aemeasurable hpair

end DirectedDistances.PaperProofs.Section5
