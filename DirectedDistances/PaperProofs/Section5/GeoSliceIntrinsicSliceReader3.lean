/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceIntrinsicSliceReader2

/-! Raw-ID versions of the slit relations separate their measurable tests from
the dependent side-cell carriers. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: raw codes for a vertex or an oriented dart of
a geometric side. Dart codes retain both the edge ID and orientation. -/
abbrev GeoSliceRawCell := Sum ℕ (ℕ × Bool)

/-- Helper toward Lemma 5.6: the carrier test for a raw cell code. -/
@[expose] def geoSliceRawCellMem (M : GeometricSideSubmap) :
    GeoSliceRawCell → Prop
  | .inl v => v ∈ M.vertices
  | .inr d => d.1 ∈ M.edges

/-- Helper toward Lemma 5.6: decode a raw cell once its exact side-carrier
membership is supplied. -/
@[expose] def geoSliceRawCellToCell (M : GeometricSideSubmap)
    (c : GeoSliceRawCell) (hc : geoSliceRawCellMem M c) : GeometricSideCell M :=
  match c with
  | .inl v => .inl ⟨v, hc⟩
  | .inr d => .inr ⟨d, hc⟩

/-- Helper toward Lemma 5.6: forget the dependent proof from a side cell. -/
@[expose] def geoSliceCellToRawCell {M : GeometricSideSubmap} :
    GeometricSideCell M → GeoSliceRawCell
  | .inl v => .inl v.1
  | .inr d => .inr d.1

/-- Helper toward Lemma 5.6: the raw code of a dependent cell satisfies its
raw carrier test. -/
theorem geoSliceCellToRawCell_mem {M : GeometricSideSubmap}
    (c : GeometricSideCell M) : geoSliceRawCellMem M (geoSliceCellToRawCell c) := by
  cases c with
  | inl v => exact v.2
  | inr d => exact d.2

/-- Helper toward Lemma 5.6: decoding a dependent cell's raw code recovers
that cell. -/
theorem geoSliceRawCellToCell_toRawCell {M : GeometricSideSubmap}
    (c : GeometricSideCell M) :
    geoSliceRawCellToCell M (geoSliceCellToRawCell c)
      (geoSliceCellToRawCell_mem c) = c := by
  cases c <;> rfl

/-- Helper toward Lemma 5.6: raw face succession includes precisely the
edge-carrier premises present in the dependent side-cell relation. -/
@[expose] def geoSliceRawFaceNext (M : GeometricSideSubmap)
    (c e : GeoSliceRawCell) : Prop :=
  match c, e with
  | .inr d, .inr f => d.1 ∈ M.edges ∧ f.1 ∈ M.edges ∧ M.faceNext d f
  | _, _ => False

/-- Helper toward Lemma 5.6: raw opposite-dart relation preserves the
orientation bit and the individual geometric edge ID. -/
@[expose] def geoSliceRawOpposite (M : GeometricSideSubmap)
    (c e : GeoSliceRawCell) : Prop :=
  match c, e with
  | .inr d, .inr f => d.1 ∈ M.edges ∧ f.1 ∈ M.edges ∧ (d.1, !d.2) = f
  | _, _ => False

/-- Helper toward Lemma 5.6: raw incidence is measured by the stored west
and east endpoint fields. -/
@[expose] def geoSliceRawIncident (M : GeometricSideSubmap)
    (c e : GeoSliceRawCell) : Prop :=
  match c, e with
  | .inr d, .inl v => d.1 ∈ M.edges ∧ v ∈ M.vertices ∧
      (if d.2 then M.east d.1 else M.west d.1) = v
  | _, _ => False

/-- Helper toward Lemma 5.6: face succession on valid raw codes agrees with
`geometricSideRelation` on their dependent cells. -/
theorem geoSliceRawFaceNext_eq_cell {M : GeometricSideSubmap}
    (c e : GeoSliceRawCell) (hc : geoSliceRawCellMem M c)
    (he : geoSliceRawCellMem M e) :
    geoSliceRawFaceNext M c e ↔ geometricSideRelation M .faceNext
      (geoSliceRawCellToCell M c hc) (geoSliceRawCellToCell M e he) := by
  cases c with
  | inl v => cases e <;> simp [geoSliceRawFaceNext, geoSliceRawCellToCell,
      geometricSideRelation]
  | inr d => cases e with
    | inl v => simp [geoSliceRawFaceNext, geoSliceRawCellToCell,
        geometricSideRelation]
    | inr f =>
      simp only [geoSliceRawCellMem] at hc he
      simp [geoSliceRawFaceNext, geoSliceRawCellToCell, geometricSideRelation,
        hc, he]

/-- Helper toward Lemma 5.6: opposite-dart relation on valid raw codes
agrees with the dependent geometric relation. -/
theorem geoSliceRawOpposite_eq_cell {M : GeometricSideSubmap}
    (c e : GeoSliceRawCell) (hc : geoSliceRawCellMem M c)
    (he : geoSliceRawCellMem M e) :
    geoSliceRawOpposite M c e ↔ geometricSideRelation M .opposite
      (geoSliceRawCellToCell M c hc) (geoSliceRawCellToCell M e he) := by
  cases c with
  | inl v => cases e <;> simp [geoSliceRawOpposite, geoSliceRawCellToCell,
      geometricSideRelation]
  | inr d => cases e with
    | inl v => simp [geoSliceRawOpposite, geoSliceRawCellToCell,
        geometricSideRelation]
    | inr f =>
      simp only [geoSliceRawCellMem] at hc he
      simp [geoSliceRawOpposite, geoSliceRawCellToCell, geometricSideRelation,
        hc, he]

/-- Helper toward Lemma 5.6: incidence on valid raw codes agrees with the
dependent geometric relation, including the dart orientation. -/
theorem geoSliceRawIncident_eq_cell {M : GeometricSideSubmap}
    (c e : GeoSliceRawCell) (hc : geoSliceRawCellMem M c)
    (he : geoSliceRawCellMem M e) :
    geoSliceRawIncident M c e ↔ geometricSideRelation M .incident
      (geoSliceRawCellToCell M c hc) (geoSliceRawCellToCell M e he) := by
  cases c with
  | inl v => cases e <;> simp [geoSliceRawIncident, geoSliceRawCellToCell,
      geometricSideRelation]
  | inr d => cases e with
    | inr f => simp [geoSliceRawIncident, geoSliceRawCellToCell,
        geometricSideRelation]
    | inl v =>
      simp only [geoSliceRawCellMem] at hc he
      simp [geoSliceRawIncident, geoSliceRawCellToCell, geometricSideRelation,
        hc, he]

/-- Helper toward Lemma 5.6: raw ray-vertex codes are the west endpoints
of the individual edges decoded by the one-side ray reader. -/
@[expose] def geoSliceRawRayVertex (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (i : ℕ) : GeoSliceRawCell :=
  .inl (M.west (geoSliceSeamRayEdge M p i))

/-- Helper toward Lemma 5.6: raw ray-dart codes retain the forward dart of
each decoded edge. -/
@[expose] def geoSliceRawRayDart (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (i : ℕ) : GeoSliceRawCell :=
  .inr (geoSliceSeamRayEdge M p i, false)

/-- Helper toward Lemma 5.6: membership in the coded ray-vertex sequence. -/
@[expose] def geoSliceRawRayVertexPred (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c : GeoSliceRawCell) : Prop :=
  ∃ i, c = geoSliceRawRayVertex M p i

/-- Helper toward Lemma 5.6: membership in either orientation of a coded
ray edge. -/
@[expose] def geoSliceRawRayDartPred (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c : GeoSliceRawCell) : Prop :=
  ∃ i, c = geoSliceRawRayDart M p i ∨
    geoSliceRawOpposite M (geoSliceRawRayDart M p i) c

/-- Helper toward Lemma 5.6: the first raw relation test is measurable for
fixed side-cell codes. -/
theorem measurableSet_geoSliceRawFaceNext (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawFaceNext M c e} := by
  cases c with
  | inl v => cases e <;> simp [geoSliceRawFaceNext]
  | inr d => cases e with
    | inl v => simp [geoSliceRawFaceNext]
    | inr f =>
      have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
      have he : MeasurableSet {M : GeometricSideSubmap | d.1 ∈ M.edges} := by
        simpa only [geometricSideCode, decide_eq_true_eq] using
          ((hcode.snd.fst.eval (a := d.1)).eq_const true).setOf
      have hf : MeasurableSet {M : GeometricSideSubmap | f.1 ∈ M.edges} := by
        simpa only [geometricSideCode, decide_eq_true_eq] using
          ((hcode.snd.fst.eval (a := f.1)).eq_const true).setOf
      have hface : MeasurableSet {M : GeometricSideSubmap | M.faceNext d f} := by
        have hfaceFn : Measurable (fun M : GeometricSideSubmap =>
            decide (M.faceNext d f)) := by
          simpa only [geometricSideCode] using
            (hcode.snd.snd.snd.snd.snd.snd.fst.eval (a := d)).eval (a := f)
        simpa only [decide_eq_true_eq] using (hfaceFn.eq_const true).setOf
      exact he.inter (hf.inter hface)

/-- Helper toward Lemma 5.6: the opposite-dart test is measurable for
fixed raw codes. -/
theorem measurableSet_geoSliceRawOpposite (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawOpposite M c e} := by
  cases c with
  | inl v => cases e <;> simp [geoSliceRawOpposite]
  | inr d => cases e with
    | inl v => simp [geoSliceRawOpposite]
    | inr f =>
      have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
      have he : MeasurableSet {M : GeometricSideSubmap | d.1 ∈ M.edges} := by
        simpa only [geometricSideCode, decide_eq_true_eq] using
          ((hcode.snd.fst.eval (a := d.1)).eq_const true).setOf
      have hf : MeasurableSet {M : GeometricSideSubmap | f.1 ∈ M.edges} := by
        simpa only [geometricSideCode, decide_eq_true_eq] using
          ((hcode.snd.fst.eval (a := f.1)).eq_const true).setOf
      change MeasurableSet {M : GeometricSideSubmap |
        d.1 ∈ M.edges ∧ f.1 ∈ M.edges ∧ (d.1, !d.2) = f}
      exact he.inter (hf.inter (MeasurableSet.const ((d.1, !d.2) = f)))

/-- Helper toward Lemma 5.6: incidence on fixed raw IDs is measurable in
the complete side code. -/
theorem measurableSet_geoSliceRawIncident (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawIncident M c e} := by
  cases c with
  | inl v => cases e <;> simp [geoSliceRawIncident]
  | inr d => cases e with
    | inr f => simp [geoSliceRawIncident]
    | inl v =>
      have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
      have he : MeasurableSet {M : GeometricSideSubmap | d.1 ∈ M.edges} := by
        simpa only [geometricSideCode, decide_eq_true_eq] using
          ((hcode.snd.fst.eval (a := d.1)).eq_const true).setOf
      have hv : MeasurableSet {M : GeometricSideSubmap | v ∈ M.vertices} := by
        simpa only [geometricSideCode, decide_eq_true_eq] using
          ((hcode.fst.eval (a := v)).eq_const true).setOf
      have hw : Measurable (fun M : GeometricSideSubmap => M.west d.1) :=
        hcode.snd.snd.fst.eval (a := d.1)
      have hx : Measurable (fun M : GeometricSideSubmap => M.east d.1) :=
        hcode.snd.snd.snd.fst.eval (a := d.1)
      have hend : Measurable (fun M : GeometricSideSubmap =>
          if d.2 then M.east d.1 else M.west d.1) :=
        hx.ite (MeasurableSet.const d.2) hw
      exact he.inter (hv.inter (hend.eq_const v).setOf)

/-- Helper toward Lemma 5.6: evaluation of a countable coordinate family
at a measurable countable index. -/
private theorem measurable_geoSliceRawEval {ι α : Type*}
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace α] :
    Measurable (fun z : (ι → α) × ι => z.1 z.2) :=
  measurable_from_prod_countable_left fun i => measurable_pi_apply i

/-- Helper toward Lemma 5.6: a coded ray edge belongs to the side carrier
on a measurable set, including when the edge index depends on the side. -/
theorem measurableSet_geoSliceRawRayEdgeMem (p : GeoSliceSeamRayCode)
    (i : ℕ) :
    MeasurableSet {M : GeometricSideSubmap |
      geoSliceSeamRayEdge M p i ∈ M.edges} := by
  have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
  have hedge : Measurable (fun M : GeometricSideSubmap =>
      decide (geoSliceSeamRayEdge M p i ∈ M.edges)) := by
    have hm : Measurable (fun M : GeometricSideSubmap =>
        ((geometricSideCode M).2.1) (geoSliceSeamRayEdge M p i)) :=
      measurable_geoSliceRawEval.comp
        (hcode.snd.fst.prodMk (measurable_geoSliceSeamRayEdge p i))
    simpa only [geometricSideCode, decide_eq_true_eq] using hm
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    (hedge.eq_const true).setOf

/-- Helper toward Lemma 5.6: every fixed raw ray-vertex membership test is
measurable as a countable union of coordinate equalities. -/
theorem measurableSet_geoSliceRawRayVertexPred (p : GeoSliceSeamRayCode)
    (c : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawRayVertexPred M p c} := by
  cases c with
  | inl v =>
    simp only [geoSliceRawRayVertexPred, geoSliceRawRayVertex,
      Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    simpa only [Sum.inl.injEq, eq_comm] using
      ((measurable_geoSliceSeamRayVertex p i).eq_const v).setOf
  | inr d => simp [geoSliceRawRayVertexPred, geoSliceRawRayVertex]

/-- Helper toward Lemma 5.6: each raw ray-dart test is a countable union
of measurable fixed-coordinate edge and carrier tests. -/
theorem measurableSet_geoSliceRawRayDartPred (p : GeoSliceSeamRayCode)
    (c : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawRayDartPred M p c} := by
  cases c with
  | inl v => simp [geoSliceRawRayDartPred, geoSliceRawRayDart,
      geoSliceRawOpposite]
  | inr d =>
    rcases d with ⟨e, b⟩
    simp only [geoSliceRawRayDartPred, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    have heq : MeasurableSet {M : GeometricSideSubmap |
        geoSliceSeamRayEdge M p i = e} := by
      simpa only [eq_comm] using
        (measurable_geoSliceSeamRayEdge p i).eq_const e |>.setOf
    have hmem := measurableSet_geoSliceRawRayEdgeMem p i
    have hfixed : MeasurableSet {M : GeometricSideSubmap | e ∈ M.edges} := by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        ((comap_measurable geometricSideCode).snd.fst.eval (a := e)
          |>.eq_const true).setOf
    have hdirectEq : {M : GeometricSideSubmap |
        Sum.inr (e, b) = geoSliceRawRayDart M p i} =
        {M | e = geoSliceSeamRayEdge M p i} ∩ {M | b = false} := by
      ext M
      simp [geoSliceRawRayDart, Sum.inr.injEq, Prod.mk.injEq,
        Set.mem_inter_iff]
    have hdirect : MeasurableSet {M : GeometricSideSubmap |
        Sum.inr (e, b) = geoSliceRawRayDart M p i} := by
      rw [hdirectEq]
      have heq' : MeasurableSet {M : GeometricSideSubmap |
          e = geoSliceSeamRayEdge M p i} := by
        simpa only [eq_comm] using heq
      exact heq'.inter (MeasurableSet.const (b = false))
    have hopEq : {M : GeometricSideSubmap |
        geoSliceRawOpposite M (geoSliceRawRayDart M p i) (Sum.inr (e, b))} =
        {M | geoSliceSeamRayEdge M p i ∈ M.edges} ∩
          ({M | e ∈ M.edges} ∩
            ({M | geoSliceSeamRayEdge M p i = e} ∩ {M | true = b})) := by
      ext M
      simp [geoSliceRawRayDart, geoSliceRawOpposite, Sum.inr.injEq,
        Prod.mk.injEq, Set.mem_inter_iff, Bool.not_false]
    have hop : MeasurableSet {M : GeometricSideSubmap |
        geoSliceRawOpposite M (geoSliceRawRayDart M p i) (Sum.inr (e, b))} := by
      rw [hopEq]
      exact hmem.inter (hfixed.inter (heq.inter (MeasurableSet.const _)))
    exact hdirect.union hop

/-- Helper toward Lemma 5.6: a fixed raw cell's carrier membership is a
measurable coordinate of the complete side code. -/
theorem measurableSet_geoSliceRawCellMem (c : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawCellMem M c} := by
  cases c with
  | inl v =>
    simpa only [geoSliceRawCellMem, geometricSideCode, decide_eq_true_eq] using
      (((comap_measurable geometricSideCode).fst.eval (a := v)).eq_const true).setOf
  | inr d =>
    simpa only [geoSliceRawCellMem, geometricSideCode, decide_eq_true_eq] using
      (((comap_measurable geometricSideCode).snd.fst.eval (a := d.1)).eq_const true).setOf

/-- Helper toward Lemma 5.6: decoding preserves equality of raw codes on
the valid side-cell carrier. -/
theorem geoSliceRawCellToCell_eq_iff {M : GeometricSideSubmap}
    (c e : GeoSliceRawCell) (hc : geoSliceRawCellMem M c)
    (he : geoSliceRawCellMem M e) :
    geoSliceRawCellToCell M c hc = geoSliceRawCellToCell M e he ↔ c = e := by
  constructor
  · intro h
    cases c with
    | inl v =>
      cases e with
      | inl w =>
        simp only [geoSliceRawCellToCell] at h
        exact congrArg Sum.inl (congrArg Subtype.val (Sum.inl.inj h))
      | inr f =>
        simp only [geoSliceRawCellToCell] at h
        cases h
    | inr d =>
      cases e with
      | inl v =>
        simp only [geoSliceRawCellToCell] at h
        cases h
      | inr f =>
        simp only [geoSliceRawCellToCell] at h
        exact congrArg Sum.inr (congrArg Subtype.val (Sum.inr.inj h))
  · intro h
    subst e
    have hproof : hc = he := Subsingleton.elim _ _
    subst he
    rfl

/-- Helper toward Lemma 5.6: raw ray-vertex membership exactly decodes to
the dependent ray-vertex test under a valid ray candidate. -/
theorem geoSliceRawRayVertexPred_iff_cell {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hcand : geoSliceSeamRayCandidate longest M p)
    (c : GeoSliceRawCell) (hmem : geoSliceRawCellMem M c) :
    geoSliceRawRayVertexPred M p c ↔
      geometricSide_ray_vertex M (geoSliceSeamRayVertexCells hcand)
        (geoSliceRawCellToCell M c hmem) := by
  constructor
  · rintro ⟨i, hi⟩
    have hri : geoSliceRawCellMem M (geoSliceRawRayVertex M p i) := by
      simpa [geoSliceRawRayVertex, geoSliceRawCellMem] using (hcand.1 i).2.2.1
    have hcell : geoSliceRawCellToCell M (geoSliceRawRayVertex M p i) hri =
        geoSliceSeamRayVertexCells hcand i := by
      rfl
    exact ⟨i, ((geoSliceRawCellToCell_eq_iff c _ hmem hri).2 hi).trans hcell⟩
  · rintro ⟨i, hi⟩
    have hri : geoSliceRawCellMem M (geoSliceRawRayVertex M p i) := by
      simpa [geoSliceRawRayVertex, geoSliceRawCellMem] using (hcand.1 i).2.2.1
    have hcell : geoSliceRawCellToCell M (geoSliceRawRayVertex M p i) hri =
        geoSliceSeamRayVertexCells hcand i := by
      rfl
    refine ⟨i, (geoSliceRawCellToCell_eq_iff c _ hmem hri).1 ?_⟩
    exact hi.trans hcell.symm

/-- Helper toward Lemma 5.6: raw ray-dart membership exactly decodes to
both orientations of the dependent ray darts. -/
theorem geoSliceRawRayDartPred_iff_cell {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hcand : geoSliceSeamRayCandidate longest M p)
    (c : GeoSliceRawCell) (hmem : geoSliceRawCellMem M c) :
    geoSliceRawRayDartPred M p c ↔
      geometricSide_ray_dart M (geoSliceSeamRayDartCells hcand)
        (geoSliceRawCellToCell M c hmem) := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · have hri : geoSliceRawCellMem M (geoSliceRawRayDart M p i) := by
        simpa [geoSliceRawRayDart, geoSliceRawCellMem] using (hcand.1 i).1
      have hcell : geoSliceRawCellToCell M (geoSliceRawRayDart M p i) hri =
          geoSliceSeamRayDartCells hcand i := by
        rfl
      exact ⟨i, Or.inl ((geoSliceRawCellToCell_eq_iff c _ hmem hri).2 hi
        |>.trans hcell)⟩
    · have hri : geoSliceRawCellMem M (geoSliceRawRayDart M p i) := by
        simpa [geoSliceRawRayDart, geoSliceRawCellMem] using (hcand.1 i).1
      have hcell : geoSliceRawCellToCell M (geoSliceRawRayDart M p i) hri =
          geoSliceSeamRayDartCells hcand i := by
        rfl
      exact ⟨i, Or.inr ((geoSliceRawOpposite_eq_cell _ _ hri hmem).1 hi)⟩
  · rintro ⟨i, hi | hi⟩
    · have hri : geoSliceRawCellMem M (geoSliceRawRayDart M p i) := by
        simpa [geoSliceRawRayDart, geoSliceRawCellMem] using (hcand.1 i).1
      have hcell : geoSliceRawCellToCell M (geoSliceRawRayDart M p i) hri =
          geoSliceSeamRayDartCells hcand i := by
        rfl
      exact ⟨i, Or.inl ((geoSliceRawCellToCell_eq_iff c _ hmem hri).1
        (hi.trans hcell.symm))⟩
    · have hri : geoSliceRawCellMem M (geoSliceRawRayDart M p i) := by
        simpa [geoSliceRawRayDart, geoSliceRawCellMem] using (hcand.1 i).1
      have hcell : geoSliceRawCellToCell M (geoSliceRawRayDart M p i) hri =
          geoSliceSeamRayDartCells hcand i := by
        rfl
      exact ⟨i, Or.inr ((geoSliceRawOpposite_eq_cell _ _ hri hmem).2 hi)⟩

/-- Helper toward Lemma 5.6: raw slit adjacency mirrors the face, opposite
and incidence steps while excluding the same ray darts and vertices. -/
@[expose] def geoSliceRawSlitStep (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c e : GeoSliceRawCell) : Prop :=
  geoSliceRawFaceNext M c e ∨ geoSliceRawFaceNext M e c ∨
    (geoSliceRawOpposite M c e ∧ ¬ geoSliceRawRayDartPred M p c) ∨
    (geoSliceRawIncident M c e ∧ ¬ geoSliceRawRayVertexPred M p e) ∨
    (geoSliceRawIncident M e c ∧ ¬ geoSliceRawRayVertexPred M p c)

/-- Helper toward Lemma 5.6: raw slit adjacency agrees with the dependent
side relation on valid cells and a valid ray candidate. -/
theorem geoSliceRawSlitStep_eq_cell {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hcand : geoSliceSeamRayCandidate longest M p)
    (c e : GeoSliceRawCell) (hc : geoSliceRawCellMem M c)
    (he : geoSliceRawCellMem M e) :
    geoSliceRawSlitStep M p c e ↔
      geometricSide_slit_step M (geoSliceSeamRayVertexCells hcand)
        (geoSliceSeamRayDartCells hcand)
        (geoSliceRawCellToCell M c hc) (geoSliceRawCellToCell M e he) := by
  simp only [geoSliceRawSlitStep, geometricSide_slit_step,
    geoSliceRawFaceNext_eq_cell c e hc he,
    geoSliceRawFaceNext_eq_cell e c he hc,
    geoSliceRawOpposite_eq_cell c e hc he,
    geoSliceRawIncident_eq_cell c e hc he,
    geoSliceRawIncident_eq_cell e c he hc,
    geoSliceRawRayDartPred_iff_cell hcand c hc,
    geoSliceRawRayVertexPred_iff_cell hcand c hc,
    geoSliceRawRayVertexPred_iff_cell hcand e he]

/-- Helper toward Lemma 5.6: each fixed raw slit-step relation is
measurable, by the already measurable raw face, opposite, incident and ray
tests. -/
theorem measurableSet_geoSliceRawSlitStep (p : GeoSliceSeamRayCode)
    (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawSlitStep M p c e} := by
  have hface := measurableSet_geoSliceRawFaceNext c e
  have hface' := measurableSet_geoSliceRawFaceNext e c
  have hop := measurableSet_geoSliceRawOpposite c e
  have hinc := measurableSet_geoSliceRawIncident c e
  have hinc' := measurableSet_geoSliceRawIncident e c
  have hrd := measurableSet_geoSliceRawRayDartPred p c
  have hrv := measurableSet_geoSliceRawRayVertexPred p c
  have hrv' := measurableSet_geoSliceRawRayVertexPred p e
  simp only [geoSliceRawSlitStep, Set.ofPred_or, Set.ofPred_and,
    ← Set.compl_ofPred]
  exact hface.union (hface'.union ((hop.inter hrd.compl).union
    ((hinc.inter hrv'.compl).union (hinc'.inter hrv.compl))))

/-- Helper toward Lemma 5.6: positive finite reachability certificates on
raw cell IDs, using the same finite-index encoding as Reader2. -/
@[expose] def geoSliceRawFiniteChain (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c e : GeoSliceRawCell) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ f : Fin (n + 1) → GeoSliceRawCell,
    f 0 = c ∧ f ⟨n, Nat.lt_succ_self n⟩ = e ∧
      ∀ j : Fin n,
        geoSliceRawSlitStep M p (f (Fin.castSucc j)) (f (Fin.succ j))

/-- Helper toward Lemma 5.6: positive finite raw-chain certificates are
measurable by the generic countable-certificate theorem. -/
theorem measurableSet_geoSliceRawFiniteChain (p : GeoSliceSeamRayCode)
    (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawFiniteChain M p c e} := by
  change MeasurableSet {M : GeometricSideSubmap | ∃ n : ℕ, 0 < n ∧
    ∃ f : Fin (n + 1) → GeoSliceRawCell,
      f 0 = c ∧ f ⟨n, Nat.lt_succ_self n⟩ = e ∧
        ∀ j : Fin n,
          geoSliceRawSlitStep M p (f (Fin.castSucc j)) (f (Fin.succ j))}
  exact measurableSet_existsFiniteChain (fun M => geoSliceRawSlitStep M p)
    (fun x y => measurableSet_geoSliceRawSlitStep p x y) c e

/-- Helper toward Lemma 5.6: reflexive raw slit reachability is equality or
a positive finite certificate. -/
@[expose] def geoSliceRawSlitReaches (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c e : GeoSliceRawCell) : Prop :=
  c = e ∨ geoSliceRawFiniteChain M p c e

/-- Helper toward Lemma 5.6: raw slit reachability is measurable through
the generic finite-chain certificate. -/
theorem measurableSet_geoSliceRawSlitReaches (p : GeoSliceSeamRayCode)
    (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawSlitReaches M p c e} := by
  simp only [geoSliceRawSlitReaches, Set.ofPred_or]
  exact (MeasurableSet.const (c = e)).union
    (measurableSet_geoSliceRawFiniteChain p c e)

/-- Helper toward Lemma 5.6: the raw right-face seed test starts at the
reverse dart of the coded ray and requires a retained face successor. -/
@[expose] def geoSliceRawRightFaceSeed (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c : GeoSliceRawCell) : Prop :=
  ∃ i, geoSliceRawOpposite M (geoSliceRawRayDart M p i) c ∧
    ∃ e, geoSliceRawFaceNext M c e

/-- Helper toward Lemma 5.6: the raw opposite test from a coded ray dart to
a fixed cell is measurable. -/
theorem measurableSet_geoSliceRawRayOpposite (p : GeoSliceSeamRayCode)
    (i : ℕ) (c : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap |
      geoSliceRawOpposite M (geoSliceRawRayDart M p i) c} := by
  cases c with
  | inl v => simp [geoSliceRawOpposite, geoSliceRawRayDart]
  | inr d =>
    rcases d with ⟨e, b⟩
    have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
    have hmem := measurableSet_geoSliceRawRayEdgeMem p i
    have heq : MeasurableSet {M : GeometricSideSubmap |
        geoSliceSeamRayEdge M p i = e} := by
      exact ((measurable_geoSliceSeamRayEdge p i).eq_const e).setOf
    have hfixed : MeasurableSet {M : GeometricSideSubmap | e ∈ M.edges} := by
      simpa only [geometricSideCode, decide_eq_true_eq] using
        ((hcode.snd.fst.eval (a := e)).eq_const true).setOf
    have hset : {M : GeometricSideSubmap |
        geoSliceRawOpposite M (geoSliceRawRayDart M p i) (Sum.inr (e, b))} =
        {M | geoSliceSeamRayEdge M p i ∈ M.edges} ∩
          ({M | e ∈ M.edges} ∩
            ({M | geoSliceSeamRayEdge M p i = e} ∩ {M | true = b})) := by
      ext M
      simp [geoSliceRawOpposite, geoSliceRawRayDart, Set.mem_inter_iff,
        Bool.not_false]
    rw [hset]
    exact hmem.inter (hfixed.inter (heq.inter (MeasurableSet.const _)))

/-- Helper toward Lemma 5.6: raw right-face seed tests are measurable by
countable unions over coded ray indices and opposite darts. -/
theorem measurableSet_geoSliceRawRightFaceSeed (p : GeoSliceSeamRayCode)
    (c : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceRawRightFaceSeed M p c} := by
  simp only [geoSliceRawRightFaceSeed, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro i
  apply (measurableSet_geoSliceRawRayOpposite p i c).inter
  exact MeasurableSet.iUnion fun e => measurableSet_geoSliceRawFaceNext c e

/-- Helper toward Lemma 5.6: the raw intrinsic-right candidate uses the
same ray, right-face seeds, and reflexive-transitive slit reachability as
the dependent-cell definition. -/
@[expose] def geoSliceIntrinsicRightRaw (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c : GeoSliceRawCell) : Prop :=
  geoSliceRawRayVertexPred M p c ∨ geoSliceRawRayDartPred M p c ∨
    ∃ a, geoSliceRawRightFaceSeed M p a ∧
      geoSliceRawSlitReaches M p a c

/-- Helper toward Lemma 5.6: every fixed raw intrinsic-right membership
test is measurable on the complete geometric-side code. -/
theorem measurableSet_geoSliceIntrinsicRightRaw (p : GeoSliceSeamRayCode)
    (c : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceIntrinsicRightRaw M p c} := by
  have hrv := measurableSet_geoSliceRawRayVertexPred p c
  have hrd := measurableSet_geoSliceRawRayDartPred p c
  simp only [geoSliceIntrinsicRightRaw, Set.ofPred_or, Set.ofPred_exists,
    Set.ofPred_and]
  apply hrv.union
  apply hrd.union
  apply MeasurableSet.iUnion
  intro a
  exact (measurableSet_geoSliceRawRightFaceSeed p a).inter
    (measurableSet_geoSliceRawSlitReaches p a c)





















end DirectedDistances.PaperProofs.Section5
