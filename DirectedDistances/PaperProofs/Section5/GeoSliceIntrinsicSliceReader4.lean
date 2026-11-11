/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceIntrinsicSliceReader3

/-! Raw slit chains carry the same cell-carrier information as the dependent
side-cell relation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: one raw slit step has valid source and target
codes. Each raw face, opposite, and incidence test carries its required
geometric-side carrier tests. -/
theorem geoSliceRawSlitStep_mem {M : GeometricSideSubmap}
    {p : GeoSliceSeamRayCode} {c e : GeoSliceRawCell}
    (h : geoSliceRawSlitStep M p c e) :
    geoSliceRawCellMem M c ∧ geoSliceRawCellMem M e := by
  rcases h with h | h | h | h | h
  · cases c <;> cases e <;> simp_all [geoSliceRawFaceNext, geoSliceRawCellMem]
  · cases c <;> cases e <;> simp_all [geoSliceRawFaceNext, geoSliceRawCellMem]
  · cases c <;> cases e <;> simp_all [geoSliceRawOpposite, geoSliceRawCellMem]
  · cases c <;> cases e <;> simp_all [geoSliceRawIncident, geoSliceRawCellMem]
  · cases c <;> cases e <;> simp_all [geoSliceRawIncident, geoSliceRawCellMem]

/-- Helper toward Lemma 5.6: raw reflexive-transitive reachability propagates
a valid start code to a valid end code. -/
theorem geoSliceRawSlitReaches_mem {M : GeometricSideSubmap}
    {p : GeoSliceSeamRayCode} {c e : GeoSliceRawCell}
    (h : Relation.ReflTransGen (geoSliceRawSlitStep M p) c e)
    (hc : geoSliceRawCellMem M c) : geoSliceRawCellMem M e := by
  induction h with
  | refl => exact hc
  | @tail b e hcb hbe ih =>
      exact (geoSliceRawSlitStep_mem hbe).2

/-- Helper toward Lemma 5.6: reflexive-transitive raw chains from valid codes
are exactly the dependent side-cell chains. -/
theorem geoSliceRawSlitReflTransGen_iff_cell {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hcand : geoSliceSeamRayCandidate longest M p)
    (c e : GeoSliceRawCell) (hc : geoSliceRawCellMem M c)
    (he : geoSliceRawCellMem M e) :
    Relation.ReflTransGen (geoSliceRawSlitStep M p) c e ↔
      Relation.ReflTransGen
        (geometricSide_slit_step M (geoSliceSeamRayVertexCells hcand)
          (geoSliceSeamRayDartCells hcand))
        (geoSliceRawCellToCell M c hc) (geoSliceRawCellToCell M e he) := by
  constructor
  · intro h
    induction h generalizing hc with
    | refl =>
      have hp : hc = he := Subsingleton.elim _ _
      subst he
      exact Relation.ReflTransGen.refl
    | @tail b e hcb hbe ih =>
      have hb := geoSliceRawSlitReaches_mem hcb hc
      have hprev := ih hc hb
      have he' := (geoSliceRawSlitStep_mem hbe).2
      have hstep :=
        (geoSliceRawSlitStep_eq_cell hcand b e hb he').1 hbe
      have hchain := Relation.ReflTransGen.tail hprev hstep
      have hp : he' = he := Subsingleton.elim _ _
      subst he
      exact hchain
  · intro h
    have hstep : ∀ x y : GeometricSideCell M,
        geometricSide_slit_step M (geoSliceSeamRayVertexCells hcand)
          (geoSliceSeamRayDartCells hcand) x y →
        geoSliceRawSlitStep M p (geoSliceCellToRawCell x)
          (geoSliceCellToRawCell y) := by
      intro x y hxy
      have hx := geoSliceRawCellToCell_toRawCell x
      have hy := geoSliceRawCellToCell_toRawCell y
      rw [← hx, ← hy] at hxy
      exact (geoSliceRawSlitStep_eq_cell hcand
        (geoSliceCellToRawCell x) (geoSliceCellToRawCell y)
        (geoSliceCellToRawCell_mem x) (geoSliceCellToRawCell_mem y)).2 hxy
    have hlift := Relation.ReflTransGen.lift geoSliceCellToRawCell hstep
      (geoSliceRawCellToCell M c hc) (geoSliceRawCellToCell M e he) h
    have hback : ∀ x (hx : geoSliceRawCellMem M x),
        geoSliceCellToRawCell (geoSliceRawCellToCell M x hx) = x := by
      intro x hx
      cases x <;> rfl
    change Relation.ReflTransGen (geoSliceRawSlitStep M p)
      (geoSliceCellToRawCell (geoSliceRawCellToCell M c hc))
      (geoSliceCellToRawCell (geoSliceRawCellToCell M e he)) at hlift
    rw [hback c hc, hback e he] at hlift
    exact hlift













































end DirectedDistances.PaperProofs.Section5

