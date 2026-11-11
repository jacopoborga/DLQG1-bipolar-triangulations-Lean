/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceObservable
public import DirectedDistances.PaperProofs.Section5.GeoSlicePresentationReconstruction2
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Final






public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: a countable encoding of an eventually-seam
edge sequence consists of a finite prefix and the seam offset after it. -/
abbrev GeoSliceSeamRayCode := List ℕ × ℕ

/-- Helper toward Lemma 5.6: decode an eventually-seam edge sequence.
The prefix retains individual edge IDs, including parallel edges. -/
@[expose] def geoSliceSeamRayEdge (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (i : ℕ) : ℕ :=
  if hi : i < p.1.length then p.1[i] else
    (M.seam (p.2 + (i - p.1.length))).1

/-- Helper toward Lemma 5.6: every coordinate of a fixed eventually-seam
code is measurable in the complete side code. -/
theorem measurable_geoSliceSeamRayEdge (p : GeoSliceSeamRayCode) (i : ℕ) :
    Measurable (fun M => geoSliceSeamRayEdge M p i) := by
  by_cases hi : i < p.1.length
  · simp only [geoSliceSeamRayEdge, dite_eq_left hi]
    exact measurable_const
  · simp only [geoSliceSeamRayEdge, dite_eq_right hi]
    exact ((comap_measurable geometricSideCode).snd.snd.snd.snd.snd.snd.snd.snd.snd.eval
      (a := p.2 + (i - p.1.length))).fst

/-- Helper toward Lemma 5.6: evaluation at a varying countable coordinate
is measurable. -/
private theorem measurable_geoSliceOneSide_eval {ι α : Type*}
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace α] :
    Measurable (fun z : (ι → α) × ι => z.1 z.2) :=
  measurable_from_prod_countable_left fun i => measurable_pi_apply i

/-- Helper toward Lemma 5.6: initial vertices of the decoded forward
darts are measurable without any directed-presence convention for missing edges. -/
theorem measurable_geoSliceSeamRayVertex (p : GeoSliceSeamRayCode) (i : ℕ) :
    Measurable (fun M : GeometricSideSubmap => M.west (geoSliceSeamRayEdge M p i)) :=
  measurable_geoSliceOneSide_eval.comp
    ((comap_measurable geometricSideCode).snd.snd.fst.prodMk
      (measurable_geoSliceSeamRayEdge p i))




@[expose] def geoSliceRawWalk (M : GeometricSideSubmap) : ℕ → ℕ → ℕ → Prop
  | 0, u, v => u = v ∧ u ∈ M.vertices
  | n + 1, u, v => u ∈ M.vertices ∧ ∃ e : ℕ,
      e ∈ M.edges ∧ e ∈ M.present ∧ M.west e = u ∧
        geoSliceRawWalk M n (M.east e) v

/-- Helper toward Lemma 5.6: the finite raw walk test is Borel, using
only countably many edge witnesses and the ten stored fields. -/
theorem measurableSet_geoSliceRawWalk (n u v : ℕ) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawWalk M n u v} := by
  have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
  have hv (a : ℕ) : MeasurableSet {M : GeometricSideSubmap | a ∈ M.vertices} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      ((hcode.fst.eval (a := a)).eq_const true).setOf
  induction n generalizing u v with
  | zero =>
    change MeasurableSet {M : GeometricSideSubmap | u = v ∧ u ∈ M.vertices}
    exact (MeasurableSet.const (u = v)).inter (hv u)
  | succ n ih =>
    have hw (e : ℕ) :
        MeasurableSet {M : GeometricSideSubmap | geoSliceRawWalk M n (M.east e) v} := by
      have heq : {M : GeometricSideSubmap | geoSliceRawWalk M n (M.east e) v} =
          ⋃ a : ℕ, {M | M.east e = a} ∩ {M | geoSliceRawWalk M n a v} := by
        ext M
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => ⟨M.east e, rfl, h⟩, fun ⟨a, ha, h⟩ => ha ▸ h⟩
      rw [heq]
      exact MeasurableSet.iUnion fun a =>
        ((hcode.snd.snd.snd.fst.eval (a := e)).eq_const a).setOf.inter (ih a v)
    change MeasurableSet {M : GeometricSideSubmap | u ∈ M.vertices ∧ ∃ e : ℕ,
      e ∈ M.edges ∧ e ∈ M.present ∧ M.west e = u ∧
        geoSliceRawWalk M n (M.east e) v}
    simp only [Set.ofPred_and, Set.ofPred_exists]
    apply (hv u).inter
    apply MeasurableSet.iUnion
    intro e
    have he : MeasurableSet {M : GeometricSideSubmap | e ∈ M.edges} := by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        ((hcode.snd.fst.eval (a := e)).eq_const true).setOf
    have hp : MeasurableSet {M : GeometricSideSubmap | e ∈ M.present} := by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        ((hcode.snd.snd.snd.snd.fst.eval (a := e)).eq_const true).setOf
    exact he.inter (hp.inter
      (((hcode.snd.snd.fst.eval (a := e)).eq_const u).setOf.inter (hw e)))

/-- Helper toward Lemma 5.6: raw walk tests admit measurable varying
endpoints, by a countable union over their values. -/
theorem measurableSet_geoSliceRawWalk_varying {u v : GeometricSideSubmap → ℕ}
    (hu : Measurable u) (hv : Measurable v) (n : ℕ) :
    MeasurableSet {M | geoSliceRawWalk M n (u M) (v M)} := by
  have he : {M | geoSliceRawWalk M n (u M) (v M)} =
      ⋃ a : ℕ, ⋃ b : ℕ,
        {M | u M = a} ∩ {M | v M = b} ∩ {M | geoSliceRawWalk M n a b} := by
    ext M
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨u M, v M, ⟨rfl, rfl⟩, h⟩,
      fun ⟨a, b, ⟨ha, hb⟩, h⟩ => ha ▸ hb ▸ h⟩
  rw [he]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
    (((hu.eq_const a).setOf).inter (hv.eq_const b).setOf).inter
      (measurableSet_geoSliceRawWalk n a b)

/-- Helper toward Lemma 5.6: the countable raw test is exactly the
intrinsic directed-walk relation on allocated vertices. -/
theorem geoSliceRawWalk_iff (M : GeometricSideSubmap) (n : ℕ)
    (u v : M.vertices) :
    geoSliceRawWalk M n u.val v.val ↔
      GeometricSideDirectedWalk M n (.inl u) (.inl v) := by
  induction n generalizing u v with
  | zero =>
    constructor
    · rintro ⟨he, _⟩
      have huv : u = v := Subtype.ext he
      subst v
      exact .nil _
    · intro hw
      cases hw
      exact ⟨rfl, u.property⟩
  | succ n ih =>
    constructor
    · rintro ⟨_, e, he, hp, hw, ht⟩
      have hm : M.east e ∈ M.vertices := by
        cases n with
        | zero => exact ht.2
        | succ n => exact ht.1
      let w : M.vertices := ⟨M.east e, hm⟩
      exact .cons ((geometricSideDirectedStep_vertices_iff M u w).2
        ⟨e, he, hp, hw, rfl⟩) ((ih w v).1 ht)
    · intro hw
      cases hw with
      | @cons _ _ w _ hs ht =>
        cases w with
        | inr w =>
          obtain ⟨d, e, _, _, _, hinc⟩ := hs
          cases e <;> exact False.elim hinc
        | inl w =>
          obtain ⟨e, he, hp, hw, htgt⟩ :=
            (geometricSideDirectedStep_vertices_iff M u w).1 hs
          refine ⟨u.property, e, he, hp, hw, ?_⟩
          rw [htgt]
          exact (ih w v).2 ht

/-- Helper toward Lemma 5.6: a countably coded adjacent metric candidate.
It begins at exterior-boundary dart 1 and every attained segment is optimal
among walks in the side. This predicate makes no leftmostness assertion. -/
@[expose] def geoSliceSeamRayCandidate (longest : Bool)
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) : Prop :=
  (∀ i : ℕ, geoSliceSeamRayEdge M p i ∈ M.edges ∧
    geoSliceSeamRayEdge M p i ∈ M.present ∧
    M.west (geoSliceSeamRayEdge M p i) ∈ M.vertices ∧
    M.east (geoSliceSeamRayEdge M p i) = M.west (geoSliceSeamRayEdge M p (i + 1))) ∧
  ((M.boundary 1).1 ∈ M.edges ∧
    geometricSideDartInitial M (M.boundary 1) = M.west (geoSliceSeamRayEdge M p 0)) ∧
  ∀ i n m : ℕ, geoSliceRawWalk M m
    (M.west (geoSliceSeamRayEdge M p i))
    (M.west (geoSliceSeamRayEdge M p (i + n))) →
      if longest then m ≤ n else n ≤ m

/-- Helper toward Lemma 5.6: adjacent candidates with a finite seam-tail
encoding have measurable validity tests; all searches here are countable. -/
theorem measurableSet_geoSliceSeamRayCandidate (longest : Bool)
    (p : GeoSliceSeamRayCode) :
    MeasurableSet {M | geoSliceSeamRayCandidate longest M p} := by
  have hc : Measurable geometricSideCode := comap_measurable geometricSideCode
  have hmem (f : GeometricSideSubmap → ℕ) (hf : Measurable f)
      (c : GeometricSideCode → (ℕ → Bool)) (hcm : Measurable c) :
      MeasurableSet {M | (c (geometricSideCode M)) (f M) = true} :=
    ((measurable_geoSliceOneSide_eval.comp ((hcm.comp hc).prodMk hf)).eq_const true).setOf
  have hedge (i : ℕ) := hmem _ (measurable_geoSliceSeamRayEdge p i)
    (fun c => c.2.1) measurable_snd.fst
  have hpresent (i : ℕ) := hmem _ (measurable_geoSliceSeamRayEdge p i)
    (fun c => c.2.2.2.2.1) measurable_snd.snd.snd.snd.fst
  have hvert (i : ℕ) := hmem _ (measurable_geoSliceSeamRayVertex p i)
    Prod.fst measurable_fst
  have heast (i : ℕ) : Measurable (fun M : GeometricSideSubmap =>
      M.east (geoSliceSeamRayEdge M p i)) :=
    measurable_geoSliceOneSide_eval.comp
      (hc.snd.snd.snd.fst.prodMk (measurable_geoSliceSeamRayEdge p i))
  have hb : Measurable (fun M : GeometricSideSubmap =>
      geometricSideDartInitial M (M.boundary 1)) := by
    have hd := hc.snd.snd.snd.snd.snd.snd.snd.snd.fst.eval (a := 1)
    have hw := measurable_geoSliceOneSide_eval.comp (hc.snd.snd.fst.prodMk hd.fst)
    have he := measurable_geoSliceOneSide_eval.comp (hc.snd.snd.snd.fst.prodMk hd.fst)
    exact he.ite (hd.snd.eq_const true).setOf hw
  have hpath : MeasurableSet {M : GeometricSideSubmap | ∀ i : ℕ,
      geoSliceSeamRayEdge M p i ∈ M.edges ∧
      geoSliceSeamRayEdge M p i ∈ M.present ∧
      M.west (geoSliceSeamRayEdge M p i) ∈ M.vertices ∧
      M.east (geoSliceSeamRayEdge M p i) = M.west (geoSliceSeamRayEdge M p (i + 1))} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    apply MeasurableSet.iInter
    intro i
    have he : MeasurableSet {M : GeometricSideSubmap |
        geoSliceSeamRayEdge M p i ∈ M.edges} := by
      simpa only [geometricSideCode, decide_eq_true_eq] using hedge i
    have hp : MeasurableSet {M : GeometricSideSubmap |
        geoSliceSeamRayEdge M p i ∈ M.present} := by
      simpa only [geometricSideCode, decide_eq_true_eq] using hpresent i
    have hv : MeasurableSet {M : GeometricSideSubmap |
        M.west (geoSliceSeamRayEdge M p i) ∈ M.vertices} := by
      simpa only [geometricSideCode, decide_eq_true_eq] using hvert i
    exact he.inter (hp.inter (hv.inter
      ((heast i).eq (measurable_geoSliceSeamRayVertex p (i + 1))).setOf))
  have hopt : MeasurableSet {M : GeometricSideSubmap | ∀ i n m : ℕ,
      geoSliceRawWalk M m (M.west (geoSliceSeamRayEdge M p i))
        (M.west (geoSliceSeamRayEdge M p (i + n))) →
        if longest then m ≤ n else n ≤ m} := by
    simp only [Set.ofPred_forall]
    simp_rw [imp_iff_not_or, Set.ofPred_or, ← Set.compl_ofPred]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun m =>
        (measurableSet_geoSliceRawWalk_varying (measurable_geoSliceSeamRayVertex p i)
          (measurable_geoSliceSeamRayVertex p (i + n)) m).compl.union
            (MeasurableSet.const _)
  have hboundary : MeasurableSet {M : GeometricSideSubmap | (M.boundary 1).1 ∈ M.edges} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      hmem _ (hc.snd.snd.snd.snd.snd.snd.snd.snd.fst.eval (a := 1)).fst
        (fun c => c.2.1) measurable_snd.fst
  exact hpath.inter ((hboundary.inter
    (hb.eq (measurable_geoSliceSeamRayVertex p 0)).setOf).inter hopt)

/-- Helper toward Lemma 5.6: the vertices of a valid countable candidate,
as cells of its side. -/
@[expose] def geoSliceSeamRayVertexCells {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) (i : ℕ) : GeometricSideCell M :=
  .inl ⟨M.west (geoSliceSeamRayEdge M p i), (hc.1 i).2.2.1⟩

/-- Helper toward Lemma 5.6: the directed darts of a valid countable
candidate, retaining the individual geometric edge. -/
@[expose] def geoSliceSeamRayDartCells {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) (i : ℕ) : GeometricSideCell M :=
  .inr ⟨(geoSliceSeamRayEdge M p i, false), (hc.1 i).1⟩

/-- Helper toward Lemma 5.6: a valid countable candidate is an intrinsic
adjacent metric candidate, with every segment attained and optimal. -/
theorem geoSliceSeamRayCandidate_intrinsic {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) :
    geometricSideAdjacentGeodesicCandidate M longest
      (geoSliceSeamRayVertexCells hc) (geoSliceSeamRayDartCells hc) := by
  have hr : geometricSideDirectedRay M
      (geoSliceSeamRayVertexCells hc) (geoSliceSeamRayDartCells hc) := by
    intro i
    exact ⟨⟨(hc.1 i).2.1, rfl⟩, rfl,
      .inr ⟨(geoSliceSeamRayEdge M p i, true), (hc.1 i).1⟩,
      rfl, (hc.1 i).2.2.2⟩
  refine ⟨hr, ⟨.inr ⟨M.boundary 1, hc.2.1.1⟩, rfl, hc.2.1.2⟩, ?_⟩
  intro i n
  refine ⟨geometricSideDirectedRay_walk hr i n, ?_⟩
  intro m hm
  exact hc.2.2 i n m ((geoSliceRawWalk_iff M m _ _).2 hm)

/-- Helper toward Lemma 5.6: the incoming dart for a forward coded ray,
starting with exterior-boundary dart 1 and then reversing its previous edge. -/
@[expose] def geoSliceSeamRayIncoming (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) : ℕ → ℕ × Bool
  | 0 => M.boundary 1
  | i + 1 => (geoSliceSeamRayEdge M p i, true)

/-- Helper toward Lemma 5.6: every coded incoming-corner coordinate is measurable. -/
theorem measurable_geoSliceSeamRayIncoming (p : GeoSliceSeamRayCode) (i : ℕ) :
    Measurable (fun M => geoSliceSeamRayIncoming M p i) := by
  cases i with
  | zero =>
    exact (comap_measurable geometricSideCode).snd.snd.snd.snd.snd.snd.snd.snd.fst.eval
      (a := 1)
  | succ i => exact (measurable_geoSliceSeamRayEdge p i).prodMk measurable_const

/-- Helper toward Lemma 5.6: first-admissible scanning among the countable
family of eventually-seam candidates. A scan is finite data, and the test
does not quantify over arbitrary infinite competitor sequences. -/
@[expose] def geoSliceSeamRayFirst (longest : Bool)
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) : Prop :=
  geoSliceSeamRayCandidate longest M p ∧
  ∀ i : ℕ, ∃ n : ℕ, ∃ f : Fin (n + 1) → ℕ × Bool,
    f 0 = geoSliceSeamRayIncoming M p i ∧
    (∀ j, (f j).1 ∈ M.edges) ∧
    (∀ j : Fin n, M.rotation (f ⟨j + 1, by omega⟩) (f ⟨j, by omega⟩)) ∧
    f ⟨n, by omega⟩ = (geoSliceSeamRayEdge M p i, false) ∧
    ∀ p' : GeoSliceSeamRayCode, geoSliceSeamRayCandidate longest M p' →
      (∀ j : ℕ, j < i → geoSliceSeamRayEdge M p' j = geoSliceSeamRayEdge M p j) →
      ∀ j : Fin (n + 1), j.val < n → f j ≠ (geoSliceSeamRayEdge M p' i, false)

/-- Helper toward Lemma 5.6: the first-admissible finite-scan test is
measurable in the side code, including its countable competitor search. -/
theorem measurableSet_geoSliceSeamRayFirst (longest : Bool) (p : GeoSliceSeamRayCode) :
    MeasurableSet {M | geoSliceSeamRayFirst longest M p} := by
  have hc : Measurable geometricSideCode := comap_measurable geometricSideCode
  simp only [geoSliceSeamRayFirst, Set.ofPred_and]
  apply (measurableSet_geoSliceSeamRayCandidate longest p).inter
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro f
  have hstart : MeasurableSet {M : GeometricSideSubmap |
      f 0 = geoSliceSeamRayIncoming M p i} :=
    (measurable_const.eq (measurable_geoSliceSeamRayIncoming p i)).setOf
  have hedges : MeasurableSet {M : GeometricSideSubmap | ∀ j, (f j).1 ∈ M.edges} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        ((hc.snd.fst.eval (a := (f j).1)).eq_const true).setOf
  have hrot : MeasurableSet {M : GeometricSideSubmap | ∀ j : Fin n,
      M.rotation (f ⟨j + 1, by omega⟩) (f ⟨j, by omega⟩)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        (((hc.snd.snd.snd.snd.snd.fst.eval (a := f ⟨j + 1, by omega⟩)).eval
          (a := f ⟨j, by omega⟩)).eq_const true).setOf
  have hend : MeasurableSet {M : GeometricSideSubmap |
      f ⟨n, by omega⟩ = (geoSliceSeamRayEdge M p i, false)} :=
    (measurable_const.eq ((measurable_geoSliceSeamRayEdge p i).prodMk measurable_const)).setOf
  have hfirst : MeasurableSet {M : GeometricSideSubmap |
      ∀ p' : GeoSliceSeamRayCode, geoSliceSeamRayCandidate longest M p' →
      (∀ j : ℕ, j < i → geoSliceSeamRayEdge M p' j = geoSliceSeamRayEdge M p j) →
      ∀ j : Fin (n + 1), j.val < n → f j ≠ (geoSliceSeamRayEdge M p' i, false)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro p'
    apply (measurableSet_geoSliceSeamRayCandidate longest p').imp
    have hprefix : MeasurableSet {M : GeometricSideSubmap | ∀ j : ℕ,
        j < i → geoSliceSeamRayEdge M p' j = geoSliceSeamRayEdge M p j} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        ((measurable_geoSliceSeamRayEdge p' j).eq (measurable_geoSliceSeamRayEdge p j)).setOf
    apply hprefix.imp
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((measurable_const.eq
        ((measurable_geoSliceSeamRayEdge p' i).prodMk measurable_const)).setOf.compl)
  exact hstart.inter (hedges.inter (hrot.inter (hend.inter hfirst)))

/-- Helper toward Lemma 5.6: finite first-admissible scans determine
the edge sequence uniquely when clockwise succession is functional on
retained darts. Different finite encodings of the same ray are permitted. -/
theorem geoSliceSeamRayFirst_edges_unique (longest : Bool) (M : GeometricSideSubmap)
    (hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ M.edges → b.1 ∈ M.edges → c.1 ∈ M.edges →
      M.rotation b a → M.rotation c a → b = c)
    {p q : GeoSliceSeamRayCode}
    (hp : geoSliceSeamRayFirst longest M p)
    (hq : geoSliceSeamRayFirst longest M q) :
    ∀ i, geoSliceSeamRayEdge M p i = geoSliceSeamRayEdge M q i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    obtain ⟨n, f, hf0, hfe, hfr, hfn, hfirst⟩ := hp.2 i
    obtain ⟨m, g, hg0, hge, hgr, hgm, hfirst'⟩ := hq.2 i
    have hcorner : geoSliceSeamRayIncoming M p i = geoSliceSeamRayIncoming M q i := by
      cases i with
      | zero => rfl
      | succ i => exact congrArg (fun e => (e, true)) (ih i (Nat.lt_succ_self i))
    have hsync : ∀ t (htn : t ≤ n) (htm : t ≤ m),
        f ⟨t, by omega⟩ = g ⟨t, by omega⟩ := by
      intro t
      induction t with
      | zero => intro _ _; exact hf0.trans (hcorner.trans hg0.symm)
      | succ t ht =>
        intro htn htm
        have he := ht (by omega) (by omega)
        apply hrot (f ⟨t, by omega⟩) _ _ (hfe _) (hfe _) (hge _)
          (hfr ⟨t, by omega⟩)
        rw [he]
        exact hgr ⟨t, by omega⟩
    have hend : f ⟨n, by omega⟩ = g ⟨m, by omega⟩ := by
      rcases lt_trichotomy n m with hnm | hnm | hmn
      · exact False.elim (hfirst' p hp.1 (fun j hj => ih j hj) ⟨n, by omega⟩ hnm
          ((hsync n le_rfl hnm.le).symm.trans hfn))
      · subst m
        exact hsync n le_rfl le_rfl
      · exact False.elim (hfirst q hq.1 (fun j hj => (ih j hj).symm)
          ⟨m, by omega⟩ hmn ((hsync m hmn.le le_rfl).trans hgm))
    exact congrArg Prod.fst (hfn.symm.trans (hend.trans hgm))

/-- Helper toward Lemma 5.6: a finite rotation scan starting at a dart
contains only darts up to its endpoint. -/
theorem geometricSideClockwiseScan_isDart {M : GeometricSideSubmap}
    {a : {d : ℕ × Bool // d.1 ∈ M.edges}} {f : ℕ → GeometricSideCell M} {n : ℕ}
    (hf : geometricSideClockwiseScan M (.inr a) f n) (j : ℕ) (hj : j ≤ n) :
    ∃ d, f j = .inr d := by
  cases j with
  | zero => exact ⟨a, hf.1⟩
  | succ j =>
    have hr := hf.2 j (by omega)
    cases he : f (j + 1) with
    | inl v => rw [he] at hr; exact False.elim hr
    | inr d => exact ⟨d, rfl⟩

/-- Helper toward Lemma 5.6: forget the subtype certificate of a dart
cell. The vertex branch is used only outside certified finite dart scans. -/
@[expose] def geoSliceCellDartValue {M : GeometricSideSubmap} :
    GeometricSideCell M → ℕ × Bool
  | .inl _ => (0, false)
  | .inr d => d.val

/-- Helper toward Lemma 5.6: first-admissible codes at a prescribed
natural encoding index. This is a countable search predicate. -/
@[expose] def geoSliceSeamRayIndexValid (longest : Bool)
    (M : GeometricSideSubmap) (n : ℕ) : Prop :=
  ∃ p : GeoSliceSeamRayCode, Encodable.encode p = n ∧ geoSliceSeamRayFirst longest M p

/-- Helper toward Lemma 5.6: every index-validity event is measurable. -/
theorem measurableSet_geoSliceSeamRayIndexValid (longest : Bool) (n : ℕ) :
    MeasurableSet {M | geoSliceSeamRayIndexValid longest M n} := by
  simp only [geoSliceSeamRayIndexValid, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun p => (MeasurableSet.const _).inter
    (measurableSet_geoSliceSeamRayFirst longest p)

/-- Helper toward Lemma 5.6: choose the least valid natural encoding
index, with `none` precisely when no first-admissible coded ray exists. -/
@[expose] noncomputable def geoSliceOneSideRayIndexOption (longest : Bool)
    (M : GeometricSideSubmap) : Option ℕ :=
  if h : ∃ n, geoSliceSeamRayIndexValid longest M n then some (Nat.find h) else none

local instance : MeasurableSpace (Option ℕ) := ⊤

/-- Helper toward Lemma 5.6: the exact graph of the least valid index. -/
theorem geoSliceOneSideRayIndexOption_eq_some_iff (longest : Bool)
    (M : GeometricSideSubmap) (n : ℕ) :
    geoSliceOneSideRayIndexOption longest M = some n ↔
      geoSliceSeamRayIndexValid longest M n ∧
        ∀ j, j < n → ¬geoSliceSeamRayIndexValid longest M j := by
  by_cases h : ∃ n, geoSliceSeamRayIndexValid longest M n
  · simp only [geoSliceOneSideRayIndexOption, dite_eq_left h, Option.some.injEq]
    exact Nat.find_eq_iff h
  · simp only [geoSliceOneSideRayIndexOption, dite_eq_right h]
    constructor
    · intro he
      cases he
    · rintro ⟨hn, _⟩
      exact (h ⟨n, hn⟩).elim

/-- Helper toward Lemma 5.6: least valid index selection is measurable;
its singletons are countable Boolean combinations of validity events. -/
theorem measurable_geoSliceOneSideRayIndexOption (longest : Bool) :
    Measurable (geoSliceOneSideRayIndexOption longest) := by
  apply measurable_to_countable'
  intro n
  cases n with
  | none =>
    have he : (geoSliceOneSideRayIndexOption longest) ⁻¹' {none} =
        (⋃ n : ℕ, {M | geoSliceSeamRayIndexValid longest M n})ᶜ := by
      ext M
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        geoSliceOneSideRayIndexOption, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      split <;> simp_all only [Option.some_ne_none, not_true_eq_false,
        not_false_eq_true]
    rw [he]
    exact (MeasurableSet.iUnion fun n =>
      measurableSet_geoSliceSeamRayIndexValid longest n).compl
  | some n =>
    have he : (geoSliceOneSideRayIndexOption longest) ⁻¹' {some n} =
        {M | geoSliceSeamRayIndexValid longest M n ∧
          ∀ j, j < n → ¬geoSliceSeamRayIndexValid longest M j} := by
      ext M
      exact geoSliceOneSideRayIndexOption_eq_some_iff longest M n
    rw [he]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (measurableSet_geoSliceSeamRayIndexValid longest n).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        (measurableSet_geoSliceSeamRayIndexValid longest j).compl)

local instance : MeasurableSpace GeoSliceSeamRayCode := ⊤
local instance : MeasurableSpace (Option GeoSliceSeamRayCode) := ⊤

/-- Helper toward Lemma 5.6: a fixed optional countable ray decoder
on a single side. It returns a first-admissible eventually-seam code. -/
@[expose] noncomputable def geoSliceOneSideRayCodeOption (longest : Bool)
    (M : GeometricSideSubmap) : Option GeoSliceSeamRayCode :=
  (geoSliceOneSideRayIndexOption longest M).bind (Encodable.decode (α := GeoSliceSeamRayCode))

/-- Helper toward Lemma 5.6: the one-side countable ray-code selector
is measurable on the full side-code space. -/
theorem measurable_geoSliceOneSideRayCodeOption (longest : Bool) :
    Measurable (geoSliceOneSideRayCodeOption longest) :=
  (measurable_of_countable (fun n : Option ℕ =>
    n.bind (Encodable.decode (α := GeoSliceSeamRayCode)))).comp
      (measurable_geoSliceOneSideRayIndexOption longest)

/-- Helper toward Lemma 5.6: whenever a first-admissible coded ray exists,
the fixed decoder returns such a code, rather than a default ray. -/
theorem geoSliceOneSideRayCodeOption_spec (longest : Bool) (M : GeometricSideSubmap)
    (hex : ∃ p, geoSliceSeamRayFirst longest M p) :
    ∃ p, geoSliceOneSideRayCodeOption longest M = some p ∧
      geoSliceSeamRayFirst longest M p := by
  have hex' : ∃ n, geoSliceSeamRayIndexValid longest M n := by
    obtain ⟨p, hp⟩ := hex
    exact ⟨Encodable.encode p, p, rfl, hp⟩
  obtain ⟨p, hp, hfirst⟩ := Nat.find_spec hex'
  refine ⟨p, ?_, hfirst⟩
  simp only [geoSliceOneSideRayCodeOption, geoSliceOneSideRayIndexOption,
    dite_eq_left hex', Option.bind_some, ← hp, Encodable.encodek]

/-- Helper toward Lemma 5.6: the complete graph of the optional code
reader is the least encoding among first-admissible seam-tail candidates. -/
theorem geoSliceOneSideRayCodeOption_eq_some_iff (longest : Bool)
    (M : GeometricSideSubmap) (p : GeoSliceSeamRayCode) :
    geoSliceOneSideRayCodeOption longest M = some p ↔
      geoSliceSeamRayFirst longest M p ∧
      ∀ q, geoSliceSeamRayFirst longest M q → Encodable.encode p ≤ Encodable.encode q := by
  constructor
  · intro hread
    unfold geoSliceOneSideRayCodeOption geoSliceOneSideRayIndexOption at hread
    split at hread
    · rename_i h
      simp only [Option.bind_some] at hread
      obtain ⟨q, hq, hqfirst⟩ := Nat.find_spec h
      have hdec : Encodable.decode (Nat.find h) = some q := by
        rw [← hq]
        exact Encodable.encodek q
      have hqp : q = p := Option.some.inj (hdec.symm.trans hread)
      subst q
      refine ⟨hqfirst, fun q hqfirst' => ?_⟩
      rw [hq]
      exact Nat.find_min' h ⟨q, rfl, hqfirst'⟩
    · cases hread
  · rintro ⟨hfirst, hmin⟩
    have hindex : geoSliceOneSideRayIndexOption longest M = some (Encodable.encode p) := by
      apply (geoSliceOneSideRayIndexOption_eq_some_iff longest M _).2
      refine ⟨⟨p, rfl, hfirst⟩, ?_⟩
      intro j hj hjvalid
      obtain ⟨q, hq, hqfirst⟩ := hjvalid
      exact (not_le_of_gt hj) (hq ▸ hmin q hqfirst)
    simp only [geoSliceOneSideRayCodeOption, hindex, Option.bind_some, Encodable.encodek]

/-- Helper toward Lemma 5.6: failure of the optional ray reader is
exactly absence of any first-admissible eventually-seam candidate. -/
theorem geoSliceOneSideRayCodeOption_eq_none_iff (longest : Bool)
    (M : GeometricSideSubmap) :
    geoSliceOneSideRayCodeOption longest M = none ↔
      ¬∃ p, geoSliceSeamRayFirst longest M p := by
  constructor
  · intro hnone hex
    obtain ⟨p, hp, _⟩ := geoSliceOneSideRayCodeOption_spec longest M hex
    rw [hnone] at hp
    cases hp
  · intro hnone
    cases he : geoSliceOneSideRayCodeOption longest M with
    | none => rfl
    | some p =>
      exact (hnone ⟨p, ((geoSliceOneSideRayCodeOption_eq_some_iff longest M p).1 he).1⟩).elim

/-- Helper toward Lemma 5.6: the selected ray's individual edge coordinate,
with `none` when the side has no first-admissible eventually-seam candidate. -/
@[expose] noncomputable def geoSliceOneSideRayEdgeOption (longest : Bool)
    (i : ℕ) (M : GeometricSideSubmap) : Option ℕ :=
  (geoSliceOneSideRayCodeOption longest M).map (fun p => geoSliceSeamRayEdge M p i)

/-- Helper toward Lemma 5.6: every selected edge coordinate is a
measurable function of the single side code. -/
theorem measurable_geoSliceOneSideRayEdgeOption (longest : Bool) (i : ℕ) :
    Measurable (geoSliceOneSideRayEdgeOption longest i) := by
  let f (z : GeometricSideSubmap × Option GeoSliceSeamRayCode) : Option ℕ :=
    z.2.map (fun p => geoSliceSeamRayEdge z.1 p i)
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro p
    cases p with
    | none => exact measurable_const
    | some p =>
      exact (measurable_of_countable (some : ℕ → Option ℕ)).comp
        (measurable_geoSliceSeamRayEdge p i)
  exact hf.comp (measurable_id.prodMk (measurable_geoSliceOneSideRayCodeOption longest))

/-- Helper toward Lemma 5.6: replace only the seam by a decoded forward
ray. This auxiliary marked side is used solely by the two-seam offset test;
it is not asserted to be the other geometric side of the ray. -/
@[expose] def geoSliceSeamRayMarkedSide (p : GeoSliceSeamRayCode)
    (M : GeometricSideSubmap) : GeometricSideSubmap :=
  { M with seam := fun i => (geoSliceSeamRayEdge M p i, false) }

/-- Helper toward Lemma 5.6: inserting a fixed countable ray code as a
seam preserves measurability of every stored field. -/
theorem measurable_geoSliceSeamRayMarkedSide (p : GeoSliceSeamRayCode) :
    Measurable (geoSliceSeamRayMarkedSide p) := by
  apply measurable_comap_iff.mpr
  have hc : Measurable geometricSideCode := comap_measurable geometricSideCode
  exact hc.fst.prodMk (hc.snd.fst.prodMk (hc.snd.snd.fst.prodMk
    (hc.snd.snd.snd.fst.prodMk (hc.snd.snd.snd.snd.fst.prodMk
    (hc.snd.snd.snd.snd.snd.fst.prodMk (hc.snd.snd.snd.snd.snd.snd.fst.prodMk
    (hc.snd.snd.snd.snd.snd.snd.snd.fst.prodMk
    (hc.snd.snd.snd.snd.snd.snd.snd.snd.fst.prodMk
      (measurable_pi_iff.mpr fun i =>
        (measurable_geoSliceSeamRayEdge p i).prodMk measurable_const)))))))))

/-- Helper toward Lemma 5.6: read the least aligned-tail offsets between
a decoded ray and the side's original seam. The existing pair selector uses
only these two seams; its other input fields play no role in this definition. -/
@[expose] noncomputable def geoSliceSeamRayOffsets (p : GeoSliceSeamRayCode)
    (M : GeometricSideSubmap) : Option (ℕ × ℕ) :=
  geoSliceSidePairOffsets ((geoSliceSeamRayMarkedSide p M, M), id)

local instance : MeasurableSpace (Option (ℕ × ℕ)) := ⊤

/-- Helper toward Lemma 5.6: the two least offsets are measurable in
one side when its eventually-seam ray code is fixed. -/
theorem measurable_geoSliceSeamRayOffsets (p : GeoSliceSeamRayCode) :
    Measurable (geoSliceSeamRayOffsets p) :=
  measurable_geoSliceSidePairOffsets.comp
    (((measurable_geoSliceSeamRayMarkedSide p).prodMk measurable_id).prodMk measurable_const)

/-- Helper toward Lemma 5.6: the single-side reader's joint least offsets,
with `none` if selection or least aligned-tail coalescence fails. -/
@[expose] noncomputable def geoSliceOneSideOffsetsOption (longest : Bool)
    (M : GeometricSideSubmap) : Option (ℕ × ℕ) :=
  (geoSliceOneSideRayCodeOption longest M).bind (fun p => geoSliceSeamRayOffsets p M)

/-- Helper toward Lemma 5.6: least offsets selected from a single side
are measurable, by countable coding and the measurable seam-tail tests. -/
theorem measurable_geoSliceOneSideOffsetsOption (longest : Bool) :
    Measurable (geoSliceOneSideOffsetsOption longest) := by
  let f (z : GeometricSideSubmap × Option GeoSliceSeamRayCode) : Option (ℕ × ℕ) :=
    z.2.bind (fun p => geoSliceSeamRayOffsets p z.1)
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro p
    cases p with
    | none => exact measurable_const
    | some p => exact measurable_geoSliceSeamRayOffsets p
  exact hf.comp (measurable_id.prodMk (measurable_geoSliceOneSideRayCodeOption longest))

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: the preceding source geodesic has a finite
prefix/seam-tail encoding at every aligned coalescence pair. -/
theorem geoSliceSeamRayEdge_source_eq
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b) (i : ℕ) :
    geoSliceSeamRayEdge (m0GeodesicSide hp (P k) .left)
      (List.ofFn (fun j : Fin a => (P (k - 1)).codePath.edge j), b) i =
        (P (k - 1)).codePath.edge i := by
  by_cases hi : i < a
  · simp only [geoSliceSeamRayEdge, List.length_ofFn, hi, dite_eq_left,
      List.getElem_ofFn]
  · simp only [geoSliceSeamRayEdge, List.length_ofFn, hi]
    exact (wholePlaneEdgeι_injective W 0 (hab (i - a))).symm.trans
      (congrArg (fun n => (P (k - 1)).codePath.edge n)
        (Nat.add_sub_of_le (Nat.le_of_not_gt hi)))

/-- Helper toward Lemma 5.6: a coalescing source ray satisfies the
countable metric-candidate test. The geometric containment used here is
the existing source side-containment fact, not a selection premise. -/
theorem geoSliceSeamRayCandidate_source
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    geoSliceSeamRayCandidate longest (m0GeodesicSide hp (P k) .left)
      (List.ofFn (fun j : Fin a => (P (k - 1)).codePath.edge j), b) := by
  simp only [geoSliceSeamRayCandidate, geoSliceSeamRayEdge_source_eq hp P k a b hab]
  let w := shiftedStream W 0
  have hout (i : ℕ) := (P (k - 1)).codePath.edge_outgoing_at_initial w i
  refine ⟨?_, ⟨m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1, ?_⟩, ?_⟩
  · intro i
    refine ⟨(hcontain i).1, (hout i).1, ?_, ?_⟩
    · change edgeWest w ((P (k - 1)).codePath.edge i) ∈ _
      rw [(hout i).2]
      exact (hcontain i).2
    · change edgeEast w ((P (k - 1)).codePath.edge i) =
        edgeWest w ((P (k - 1)).codePath.edge (i + 1))
      exact ((P (k - 1)).codePath.edge_incoming_at_succ w i).2.trans
        (hout (i + 1)).2.symm
  · exact (m0GeodesicLeftSide_adjacent_start hp (P k)).trans
      ((m0Geodesic_initial_zero (P (k - 1))).symm.trans (hout 0).2.symm)
  · intro i n m hm
    change geoSliceRawWalk _ m (edgeWest w ((P (k - 1)).codePath.edge i))
      (edgeWest w ((P (k - 1)).codePath.edge (i + n))) at hm
    rw [(hout i).2, (hout (i + n)).2] at hm
    exact (m0GeodesicSide_realized_adjacentCandidate hp P k hcontain).2.2 i n |>.2 m
      ((geoSliceRawWalk_iff _ m
        ⟨_, (hcontain i).2⟩ ⟨_, (hcontain (i + n)).2⟩).1 hm)

/-- Helper toward Lemma 5.6: the actual preceding geodesic passes the
countable first-admissible scan. The unrestricted intrinsic selector excludes
every earlier eventually-seam competitor, so no extension hypothesis is added. -/
theorem geoSliceSeamRayFirst_source
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    geoSliceSeamRayFirst longest (m0GeodesicSide hp (P k) .left)
      (List.ofFn (fun j : Fin a => (P (k - 1)).codePath.edge j), b) := by
  let M := m0GeodesicSide hp (P k) .left
  let p : GeoSliceSeamRayCode :=
    (List.ofFn (fun j : Fin a => (P (k - 1)).codePath.edge j), b)
  have heq (i : ℕ) : geoSliceSeamRayEdge M p i = (P (k - 1)).codePath.edge i :=
    geoSliceSeamRayEdge_source_eq hp P k a b hab i
  refine ⟨geoSliceSeamRayCandidate_source hp P k a b hab hcontain, ?_⟩
  intro i
  obtain ⟨c, f, n, hcorner, hf, hend, hfirst⟩ :=
    (m0GeodesicSide_realizedAdjacent_is_intrinsic hp P T hleft k hcontain).2 i
  have hc : ∃ d, c = .inr d := by
    cases i with
    | zero => cases c with
      | inl v => exact False.elim hcorner
      | inr d => exact ⟨d, rfl⟩
    | succ i => cases c with
      | inl v => exact False.elim hcorner
      | inr d => exact ⟨d, rfl⟩
  obtain ⟨c, rfl⟩ := hc
  let g (j : Fin (n + 1)) := geoSliceCellDartValue (f j)
  have hfg (j : Fin (n + 1)) : ∃ d,
      f j = .inr d ∧ g j = d.val := by
    obtain ⟨d, hd⟩ := geometricSideClockwiseScan_isDart hf j (by omega)
    exact ⟨d, hd, by simp only [g, hd, geoSliceCellDartValue]⟩
  refine ⟨n, g, ?_, ?_, ?_, ?_, ?_⟩
  · change geoSliceCellDartValue (f 0) = geoSliceSeamRayIncoming M p i
    rw [hf.1]
    change c.val = geoSliceSeamRayIncoming M p i
    cases i with
    | zero => exact hcorner.symm
    | succ i =>
      change ((P (k - 1)).codePath.edge i, true) = c.val at hcorner
      simpa only [geoSliceSeamRayIncoming, heq] using hcorner.symm
  · intro j
    obtain ⟨d, _, hd⟩ := hfg j
    rw [hd]
    exact d.property
  · intro j
    obtain ⟨d, hd, hgd⟩ := hfg ⟨j + 1, by omega⟩
    obtain ⟨e, he, hge⟩ := hfg ⟨j, by omega⟩
    rw [hgd, hge]
    have hr := hf.2 j j.isLt
    rw [hd, he] at hr
    exact hr
  · change geoSliceCellDartValue (f n) = (geoSliceSeamRayEdge M p i, false)
    rw [hend, heq]
    rfl
  · intro q hq hpref j hj hgj
    have hprefix : ∀ t, t < i → geoSliceSeamRayDartCells hq t =
        m0GeodesicSideAdjacentDarts hp P k hcontain t := by
      intro t ht
      apply congrArg Sum.inr
      apply Subtype.ext
      change (geoSliceSeamRayEdge M q t, false) = ((P (k - 1)).codePath.edge t, false)
      rw [hpref t ht, heq]
    apply hfirst (geoSliceSeamRayVertexCells hq) (geoSliceSeamRayDartCells hq)
      (geoSliceSeamRayCandidate_intrinsic hq) hprefix j hj
    obtain ⟨d, hd, hgd⟩ := hfg j
    rw [hd]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact hgd.symm.trans hgj

/-- Helper toward Lemma 5.6: the countable first-admissible test identifies
the actual preceding ray on a realized left side, using the proved rotation
law rather than assuming one on an arbitrary submap. -/
theorem geoSliceSeamRayFirst_source_edges
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {p : GeoSliceSeamRayCode}
    (hpfirst : geoSliceSeamRayFirst longest (m0GeodesicSide hp (P k) .left) p) :
    ∀ i, geoSliceSeamRayEdge (m0GeodesicSide hp (P k) .left) p i =
      (P (k - 1)).codePath.edge i := by
  have hrot : ∀ a b c : ℕ × Bool,
      a.1 ∈ (m0GeodesicSide hp (P k) .left).edges →
      b.1 ∈ (m0GeodesicSide hp (P k) .left).edges →
      c.1 ∈ (m0GeodesicSide hp (P k) .left).edges →
      (m0GeodesicSide hp (P k) .left).rotation b a →
      (m0GeodesicSide hp (P k) .left).rotation c a → b = c := by
    intro a b c ha hb hc hba hca
    have he := m0GeodesicSide_clockwiseStep_unique hp (P k) .left
      (.inr ⟨a, ha⟩) (.inr ⟨b, hb⟩) (.inr ⟨c, hc⟩) hba hca
    exact congrArg Subtype.val (Sum.inr.inj he)
  intro i
  exact (geoSliceSeamRayFirst_edges_unique longest _ hrot hpfirst
    (geoSliceSeamRayFirst_source hp P T hleft k a b hab hcontain) i).trans
      (geoSliceSeamRayEdge_source_eq hp P k a b hab i)

/-- Helper toward Lemma 5.6: the fixed measurable single-side ray reader
returns the individual edges of `P (k - 1)` on every source side with its
proved containment and coalescence facts. -/
theorem geoSliceOneSideRayEdgeOption_source
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutEdgeTailsCoalesce (P (k - 1)) (P k) a b)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) (i : ℕ) :
    geoSliceOneSideRayEdgeOption longest i (m0GeodesicSide hp (P k) .left) =
      some ((P (k - 1)).codePath.edge i) := by
  obtain ⟨p, hread, hfirst⟩ := geoSliceOneSideRayCodeOption_spec longest _
    ⟨_, geoSliceSeamRayFirst_source hp P T hleft k a b hab hcontain⟩
  simp only [geoSliceOneSideRayEdgeOption, hread, Option.map_some,
    geoSliceSeamRayFirst_source_edges hp P T hleft k a b hab hcontain hfirst]

/-- Helper toward Lemma 5.6: the measurable one-side offset reader returns
the source's joint least coalescence pair, in the order theta-minus, theta. -/
theorem geoSliceOneSideOffsetsOption_source
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    geoSliceOneSideOffsetsOption longest (m0GeodesicSide hp (P k) .left) = some (a, b) := by
  obtain ⟨p, hread, hfirst⟩ := geoSliceOneSideRayCodeOption_spec longest _
    ⟨_, geoSliceSeamRayFirst_source hp P T hleft k a b hab.1 hcontain⟩
  simp only [geoSliceOneSideOffsetsOption, hread, Option.bind_some, geoSliceSeamRayOffsets]
  apply (geoSliceSidePairOffsets_eq_some_iff _ a b).2
  have htail (i j : ℕ) :
      geoSliceSidePairTailsCoalesce
        ((geoSliceSeamRayMarkedSide p (m0GeodesicSide hp (P k) .left),
          m0GeodesicSide hp (P k) .left), id) i j ↔
        M0CutEdgeTailsCoalesce (P (k - 1)) (P k) i j := by
    simp only [geoSliceSidePairTailsCoalesce, geoSliceSeamRayMarkedSide,
      geoSliceSeamRayFirst_source_edges hp P T hleft k a b hab.1 hcontain hfirst]
    constructor
    · intro hco n
      exact congrArg (wholePlaneEdgeι W 0) (hco n)
    · intro hco n
      exact wholePlaneEdgeι_injective W 0 (hco n)
  exact ⟨(htail a b).2 hab.1, fun i j hij => hab.2 i j ((htail i j).1 hij)⟩

/-- Helper toward Lemma 5.6: on one full-measure event for both metrics
and every integer cut, the single-side ray and offset readers recover the
preceding geodesic and the source's joint least pair. All side-containment
premises of the pointwise identifications are discharged on this event. -/
theorem m0Cut_ae_oneSideRay_and_offsets :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
      ∀ k : ℤ, ∃ a b : ℕ,
        ∃ _hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b,
        geoSliceOneSideOffsetsOption longest (m0GeodesicSide hp (P k) .left) = some (a, b) ∧
        ∀ i : ℕ, geoSliceOneSideRayEdgeOption longest i
          (m0GeodesicSide hp (P k) .left) = some ((P (k - 1)).codePath.edge i) := by
  filter_upwards [m0Cut_ae_realizedLeftSideSlice_eq] with W hW
  obtain ⟨H, h, hLL, hp, hmodes⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, hc, hcontain, _⟩ := hmodes longest
  refine ⟨P, T, hleft, fun k => ?_⟩
  obtain ⟨a, b, hab⟩ := hc k
  have hinside := hcontain (k - 1) k (by omega)
  exact ⟨a, b, hab, geoSliceOneSideOffsetsOption_source hp P T hleft k a b hab hinside,
    geoSliceOneSideRayEdgeOption_source hp P T hleft k a b hab.1 hinside⟩

/-- Helper toward Lemma 5.6: the offset reader composes measurably with
the certified L-minus canonical side. This is an offset-valued observation,
not a slice-class observation. -/
theorem measurable_geoSliceOneSideOffsetsOption_lMinus (x : XDP) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      geoSliceOneSideOffsetsOption (if x = XDP.ldp then true else false)
        (lMinusCanonicalSideOnCoherent x z)) :=
  (measurable_geoSliceOneSideOffsetsOption _).comp
    (measurable_lMinusCanonicalSideOnCoherent x)

/-- Helper toward Lemma 5.6: the offset reader composes measurably with
the certified L-plus canonical side at every index. -/
theorem measurable_geoSliceOneSideOffsetsOption_lPlus (x : XDP) (k : ℤ) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      geoSliceOneSideOffsetsOption (if x = XDP.ldp then true else false)
        (lPlusCanonicalSideOnCertifiedPair x k z)) :=
  (measurable_geoSliceOneSideOffsetsOption _).comp
    (measurable_lPlusCanonicalSideOnCertifiedPair x k)
























































/- exited 0 for all 48 named declarations in this file (including its private
evaluation lemma, definitions and abbreviation). Their transitive axiom sets
are contained in {propext, Classical.choice, Quot.sound}; no custom axiom or
sorryAx occurred. All probes were removed before the final production compile. -/

end DirectedDistances.PaperProofs.Section5
