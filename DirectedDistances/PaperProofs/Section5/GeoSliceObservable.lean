/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRotationAngleBridge
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Assembly2

/-! The actual slice-class family is chosen on the simultaneous witness event,
with `none` outside that event. Its almost-sure source characterization is
separate from the remaining measurability and presentation reconstruction. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: source witnesses for the entire leftmost
geodesic family and its adjacent least-coalescence offsets. The two offset
coordinates retain the order `theta_k^-`, `theta_k` of `eqn-coalesce`. -/
structure M0CutGeodesicSliceWitness (W : ℤ → Fin 3) (x : XDP) where
  H : WholePlaneRotationHypothesis W
  h : BoundaryHitWitnesses (shiftedStream W 0)
  hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))
  hp : BoundaryHitWitnesses (kmswPastCode W)
  T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k)
  P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k
    (if x = XDP.ldp then true else false)
  hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL
    (if x = XDP.ldp then true else false) k (P k) (T k)
  huniq : ∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL
    (if x = XDP.ldp then true else false) k Q (T k) → Q = P k
  thetaMinus : ℤ → ℕ
  theta : ℤ → ℕ
  least : ∀ k, M0CutLeastEdgeCoalescence (P (k - 1)) (P k)
    (thetaMinus k) (theta k)

/-- Helper toward Lemma 5.6: the existing simultaneous containment event
provides all witnesses required for the slice-class choice. -/
theorem ae_m0CutGeodesicSliceWitness (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      Nonempty (M0CutGeodesicSliceWitness W x) := by
  filter_upwards [m0Cut_ae_geodesicSlice_left_right_side_containment] with W hW
  obtain ⟨H, h, hLL, hp, hall⟩ := hW
  obtain ⟨P, T, hleft, huniq, hc, _⟩ :=
    hall (if x = XDP.ldp then true else false)
  choose a b hab using hc
  exact ⟨⟨H, h, hLL, hp, T, P, hleft, huniq, a, b, hab⟩⟩

/-- Helper toward Lemma 5.6: choose the source slice class on the event
where the full leftmost family and its least offsets exist, and return
`none` outside. A single witness is used simultaneously for every `k`. -/
@[expose] noncomputable def m0CutGeodesicSliceClassOption (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : Option GeometricSideClass :=
  if hW : Nonempty (M0CutGeodesicSliceWitness W x) then
    let s := Classical.choice hW
    some (geometricSideClass
      (m0CutGeodesicSlice (hp := s.hp) s.P k
        (s.thetaMinus k) (s.theta k) (s.least k)))
  else none

/-- Helper toward Lemma 5.6: the optional class is present exactly on its
source witness event, independently of the boundary index. -/
theorem m0CutGeodesicSliceClassOption_isSome_iff (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) :
    (m0CutGeodesicSliceClassOption x k W).isSome ↔
      Nonempty (M0CutGeodesicSliceWitness W x) := by
  by_cases hW : Nonempty (M0CutGeodesicSliceWitness W x)
  · simp only [m0CutGeodesicSliceClassOption, dite_eq_left hW, Option.isSome_some,
      true_iff]
    exact hW
  · simp only [m0CutGeodesicSliceClassOption, dite_eq_right hW, Option.isSome_none,
      Bool.false_eq_true, false_iff]
    exact hW

/-- Helper toward Lemma 5.6: on one event of full measure, the chosen
classes are precisely the candidate geometric slice carriers, with all
leftmost, uniqueness and least-coalescence binders of the intended target. -/
theorem m0Cut_ae_geodesicSlice_class (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k
        (if x = XDP.ldp then true else false),
      (∀ k, Xdp.CutLeftmostXdp W H h hp hLL
        (if x = XDP.ldp then true else false) k (P k) (T k)) ∧
      (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL
        (if x = XDP.ldp then true else false) k Q (T k) → Q = P k) ∧
      ∀ k : ℤ, ∃ a b : ℕ,
        ∃ hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b,
        m0CutGeodesicSliceClassOption x k W = some (geometricSideClass
          (m0CutGeodesicSlice (hp := hp) P k a b hab)) := by
  filter_upwards [ae_m0CutGeodesicSliceWitness x] with W hW
  let s := Classical.choice hW
  refine ⟨s.H, s.h, s.hLL, s.hp, s.T, s.P, s.hleft, s.huniq, ?_⟩
  intro k
  exact ⟨s.thetaMinus k, s.theta k, s.least k,
    dite_eq_left hW⟩

/-- Helper toward Lemma 5.6: labeled data sufficient for the literal
slice construction. The two sides use one common vertex and edge numbering;
the next entries are the ambient rotation, the two initial-vertex sequences,
and the two coalescence offsets. This does not assert that selected source
witnesses are measurable functions of the random stream. -/
abbrev GeoSliceLabeledData :=
  (GeometricSideSubmap × GeometricSideSubmap) ×
    ((ℕ × Bool → ℕ × Bool) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × ℕ)

/-- Helper toward Lemma 5.6: the common-side overlap after deleting both
edge tails starting at the specified offsets. Missing geometric edges are
retained independently of their directed presence. -/
@[expose] def geoSliceLabeledEdges (z : GeoSliceLabeledData) : Set ℕ :=
  (z.1.1.edges ∩ z.1.2.edges) \
    (Set.range (fun n => (z.1.1.seam (z.2.2.2.2.1 + n)).1) ∪
      Set.range (fun n => (z.1.2.seam (z.2.2.2.2.2 + n)).1))

/-- Helper toward Lemma 5.6: the exact ten-field slice operation on
common labeled side and path data. The vertex tails are strict, the edge
tails start at the offsets, and face succession is the intersection of the
two side relations, as in `m0CutGeodesicSlice`. -/
@[expose] def geoSliceOfLabeledData (z : GeoSliceLabeledData) :
    GeometricSideSubmap where
  vertices := (z.1.1.vertices ∩ z.1.2.vertices) \
    ({v | ∃ n, z.2.2.2.2.1 < n ∧ v = z.2.2.1 n} ∪
      {v | ∃ n, z.2.2.2.2.2 < n ∧ v = z.2.2.2.1 n})
  edges := geoSliceLabeledEdges z
  west := z.1.1.west
  east := z.1.1.east
  present := z.1.1.present
  rotation d e := ∃ n : ℕ, 0 < n ∧ z.2.1^[n] d = e ∧
    ∀ j : ℕ, 0 < j → j < n → (z.2.1^[j] d).1 ∉ geoSliceLabeledEdges z
  faceNext d e := z.1.1.faceNext d e ∧ z.1.2.faceNext d e
  root := z.1.1.root
  boundary := z.1.1.seam
  seam := z.1.2.seam

/-- Helper toward Lemma 5.6: the labeled operation recovers the literal
candidate slice, including rotation, represented faces and both full marks. -/
theorem geoSliceOfLabeledData_source_eq
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    geoSliceOfLabeledData
      ((m0GeodesicSide hp (P (k - 1)) .right,
          m0GeodesicSide hp (P k) .left),
        ((kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool),
          (fun n => ((P (k - 1)).codePath.initial n).1.id),
          (fun n => ((P k).codePath.initial n).1.id), a, b)) =
      m0CutGeodesicSlice (hp := hp) P k a b hab := by
  rfl

/-- Helper toward Lemma 5.6: evaluation at a varying countable coordinate
is measurable for the product coordinate sigma algebra. -/
private theorem measurable_geoSlice_eval {ι α : Type*}
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace α] :
    Measurable (fun z : (ι → α) × ι => z.1 z.2) :=
  measurable_from_prod_countable_left fun i => measurable_pi_apply i

/-- Helper toward Lemma 5.6: the first complete side code is a measurable
coordinate of the labeled input. -/
private theorem measurable_geoSlice_leftCode :
    Measurable (fun z : GeoSliceLabeledData => geometricSideCode z.1.1) :=
  (comap_measurable geometricSideCode).comp measurable_fst.fst

/-- Helper toward Lemma 5.6: the second complete side code is a measurable
coordinate of the labeled input. -/
private theorem measurable_geoSlice_rightCode :
    Measurable (fun z : GeoSliceLabeledData => geometricSideCode z.1.2) :=
  (comap_measurable geometricSideCode).comp measurable_fst.snd

/-- Helper toward Lemma 5.6: each ambient rotation iterate is jointly
measurable in the labeled data. -/
private theorem measurable_geoSlice_rotationIterate (n : ℕ) (d : ℕ × Bool) :
    Measurable (fun z : GeoSliceLabeledData => z.2.1^[n] d) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simpa only [Function.iterate_succ_apply', Function.comp_def] using
      measurable_geoSlice_eval.comp (measurable_snd.fst.prodMk ih)

/-- Helper toward Lemma 5.6: every geometric edge coordinate of the
finite-tail cut is measurable, including both deleted tails. -/
theorem measurableSet_geoSliceLabeledEdges (e : ℕ) :
    MeasurableSet {z : GeoSliceLabeledData | e ∈ geoSliceLabeledEdges z} := by
  have hL := measurable_geoSlice_leftCode
  have hR := measurable_geoSlice_rightCode
  have heL : MeasurableSet {z : GeoSliceLabeledData | e ∈ z.1.1.edges} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      ((hL.snd.fst.eval (a := e)).eq_const true).setOf
  have heR : MeasurableSet {z : GeoSliceLabeledData | e ∈ z.1.2.edges} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      ((hR.snd.fst.eval (a := e)).eq_const true).setOf
  have htailL (n : ℕ) : Measurable (fun z : GeoSliceLabeledData =>
      (z.1.1.seam (z.2.2.2.2.1 + n)).1) := by
    exact (measurable_geoSlice_eval.comp
      (hL.snd.snd.snd.snd.snd.snd.snd.snd.snd.prodMk
        (measurable_snd.snd.snd.snd.fst.add_const n))).fst
  have htailR (n : ℕ) : Measurable (fun z : GeoSliceLabeledData =>
      (z.1.2.seam (z.2.2.2.2.2 + n)).1) := by
    exact (measurable_geoSlice_eval.comp
      (hR.snd.snd.snd.snd.snd.snd.snd.snd.snd.prodMk
        (measurable_snd.snd.snd.snd.snd.add_const n))).fst
  have hTL : MeasurableSet {z : GeoSliceLabeledData |
      e ∈ Set.range (fun n => (z.1.1.seam (z.2.2.2.2.1 + n)).1)} := by
    simp only [Set.mem_range, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => ((htailL n).eq_const e).setOf
  have hTR : MeasurableSet {z : GeoSliceLabeledData |
      e ∈ Set.range (fun n => (z.1.2.seam (z.2.2.2.2.2 + n)).1)} := by
    simp only [Set.mem_range, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => ((htailR n).eq_const e).setOf
  exact (heL.inter heR).diff (hTL.union hTR)

/-- Helper toward Lemma 5.6: all vertex coordinates of the strict-tail
cut are measurable. The terminal meeting vertex is not deleted. -/
theorem measurableSet_geoSliceOfLabeledData_vertices (v : ℕ) :
    MeasurableSet {z : GeoSliceLabeledData |
      v ∈ (geoSliceOfLabeledData z).vertices} := by
  have hL := measurable_geoSlice_leftCode
  have hR := measurable_geoSlice_rightCode
  have hvL : MeasurableSet {z : GeoSliceLabeledData | v ∈ z.1.1.vertices} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      ((hL.fst.eval (a := v)).eq_const true).setOf
  have hvR : MeasurableSet {z : GeoSliceLabeledData | v ∈ z.1.2.vertices} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      ((hR.fst.eval (a := v)).eq_const true).setOf
  have hTL : MeasurableSet {z : GeoSliceLabeledData |
      ∃ n, z.2.2.2.2.1 < n ∧ v = z.2.2.1 n} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion fun n =>
      (measurable_snd.snd.snd.snd.fst.lt measurable_const).setOf.inter
        (measurable_const.eq (measurable_snd.snd.fst.eval (a := n))).setOf
  have hTR : MeasurableSet {z : GeoSliceLabeledData |
      ∃ n, z.2.2.2.2.2 < n ∧ v = z.2.2.2.1 n} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion fun n =>
      (measurable_snd.snd.snd.snd.snd.lt measurable_const).setOf.inter
        (measurable_const.eq (measurable_snd.snd.snd.fst.eval (a := n))).setOf
  exact (hvL.inter hvR).diff (hTL.union hTR)

/-- Helper toward Lemma 5.6: the induced rotation on the overlap is
measurable by countable first-return certificates in the ambient rotation. -/
theorem measurableSet_geoSliceOfLabeledData_rotation (d e : ℕ × Bool) :
    MeasurableSet {z : GeoSliceLabeledData |
      (geoSliceOfLabeledData z).rotation d e} := by
  have hEdges : Measurable (fun z : GeoSliceLabeledData =>
      fun i => decide (i ∈ geoSliceLabeledEdges z)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_geoSliceLabeledEdges i
  have hAvoid (j : ℕ) : MeasurableSet {z : GeoSliceLabeledData |
      (z.2.1^[j] d).1 ∉ geoSliceLabeledEdges z} := by
    have hm := measurable_geoSlice_eval.comp
      (hEdges.prodMk (measurable_geoSlice_rotationIterate j d).fst)
    simpa only [Function.comp_def, decide_eq_false_iff_not] using
      (hm.eq_const false).setOf
  change MeasurableSet {z : GeoSliceLabeledData |
    ∃ n : ℕ, 0 < n ∧ z.2.1^[n] d = e ∧
      ∀ j : ℕ, 0 < j → j < n → (z.2.1^[j] d).1 ∉ geoSliceLabeledEdges z}
  simp only [Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
  exact MeasurableSet.iUnion fun n => (MeasurableSet.const (0 < n)).inter
    (((measurable_geoSlice_rotationIterate n d).eq_const e).setOf.inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ => hAvoid j))

/-- Helper toward Lemma 5.6: the represented face-successor intersection
is measurable in both complete labeled sides. -/
theorem measurableSet_geoSliceOfLabeledData_faceNext (d e : ℕ × Bool) :
    MeasurableSet {z : GeoSliceLabeledData |
      (geoSliceOfLabeledData z).faceNext d e} := by
  have hL : MeasurableSet {z : GeoSliceLabeledData | z.1.1.faceNext d e} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      ((measurable_geoSlice_leftCode.snd.snd.snd.snd.snd.snd.fst.eval
        (a := d) |>.eval (a := e)).eq_const true).setOf
  have hR : MeasurableSet {z : GeoSliceLabeledData | z.1.2.faceNext d e} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      ((measurable_geoSlice_rightCode.snd.snd.snd.snd.snd.snd.fst.eval
        (a := d) |>.eval (a := e)).eq_const true).setOf
  exact hL.inter hR

/-- Helper toward Lemma 5.6: the complete ten-field slice code is a
measurable function of common labeled sides, path vertices, ambient rotation
and least-coalescence offsets. This proves the cutting operation itself
measurable without a measurability or reconstruction premise. -/
theorem measurable_geoSliceOfLabeledData_code :
    Measurable (fun z : GeoSliceLabeledData =>
      geometricSideCode (geoSliceOfLabeledData z)) := by
  have hBool (P : GeoSliceLabeledData → Prop)
      (hP : MeasurableSet {z | P z}) : Measurable (fun z => decide (P z)) := by
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hP
  have hV := measurable_pi_iff.mpr fun n =>
    hBool _ (measurableSet_geoSliceOfLabeledData_vertices n)
  have hE := measurable_pi_iff.mpr fun n =>
    hBool _ (measurableSet_geoSliceLabeledEdges n)
  have hR := measurable_pi_iff.mpr fun d => measurable_pi_iff.mpr fun e =>
    hBool _ (measurableSet_geoSliceOfLabeledData_rotation d e)
  have hF := measurable_pi_iff.mpr fun d => measurable_pi_iff.mpr fun e =>
    hBool _ (measurableSet_geoSliceOfLabeledData_faceNext d e)
  have hL := measurable_geoSlice_leftCode
  have hN := measurable_geoSlice_rightCode
  exact hV.prodMk (hE.prodMk (hL.snd.snd.fst.prodMk
    (hL.snd.snd.snd.fst.prodMk (hL.snd.snd.snd.snd.fst.prodMk
      (hR.prodMk (hF.prodMk (hL.snd.snd.snd.snd.snd.snd.snd.fst.prodMk
        (hL.snd.snd.snd.snd.snd.snd.snd.snd.snd.prodMk
          hN.snd.snd.snd.snd.snd.snd.snd.snd.snd))))))))

/-- Helper toward Lemma 5.6: the literal slice operation is measurable
for the complete-field measurable structure on geometric submaps. -/
theorem measurable_geoSliceOfLabeledData : Measurable geoSliceOfLabeledData :=
  measurable_comap_iff.mpr measurable_geoSliceOfLabeledData_code

/-- Helper toward Lemma 5.6: passing from the literal measurable slice
operation to its marked-isomorphism class preserves measurability. -/
theorem measurable_geoSliceOfLabeledData_class :
    Measurable (fun z => geometricSideClass (geoSliceOfLabeledData z)) :=
  measurable_geometricSideClass.comp measurable_geoSliceOfLabeledData

/-- Helper toward Lemma 5.6: a pair of closed sides in common ambient
coordinates, together with the ambient rotation on those coordinates. -/
abbrev GeoSliceSidePairData :=
  (GeometricSideSubmap × GeometricSideSubmap) × (ℕ × Bool → ℕ × Bool)

/-- Helper toward Lemma 5.6: equality of the two marked edge tails at
specified offsets, retaining geometric edge identity. -/
@[expose] def geoSliceSidePairTailsCoalesce (z : GeoSliceSidePairData)
    (a b : ℕ) : Prop :=
  ∀ n : ℕ, (z.1.1.seam (a + n)).1 = (z.1.2.seam (b + n)).1

/-- Helper toward Lemma 5.6: the coordinatewise least aligned tail
offsets, with the same two clauses as `M0CutLeastEdgeCoalescence`. -/
@[expose] def geoSliceSidePairLeastCoalescence (z : GeoSliceSidePairData)
    (a b : ℕ) : Prop :=
  geoSliceSidePairTailsCoalesce z a b ∧
    ∀ i j, geoSliceSidePairTailsCoalesce z i j → a ≤ i ∧ b ≤ j

/-- Helper toward Lemma 5.6: the least pair, when it exists, is unique
in both coordinates. -/
theorem geoSliceSidePairLeastCoalescence_unique {z : GeoSliceSidePairData}
    {a b c d : ℕ} (hab : geoSliceSidePairLeastCoalescence z a b)
    (hcd : geoSliceSidePairLeastCoalescence z c d) : a = c ∧ b = d :=
  ⟨Nat.le_antisymm (hab.2 c d hcd.1).1 (hcd.2 a b hab.1).1,
    Nat.le_antisymm (hab.2 c d hcd.1).2 (hcd.2 a b hab.1).2⟩

/-- Helper toward Lemma 5.6: select the unique least pair when present,
and return `none` if the marked edge streams have no least aligned tails. -/
@[expose] noncomputable def geoSliceSidePairOffsets (z : GeoSliceSidePairData) :
    Option (ℕ × ℕ) :=
  if h : ∃ a b, geoSliceSidePairLeastCoalescence z a b then
    some (h.choose, h.choose_spec.choose)
  else none

/-- Helper toward Lemma 5.6: the offset selector has exactly the least
coalescence relation as its graph. -/
theorem geoSliceSidePairOffsets_eq_some_iff (z : GeoSliceSidePairData) (a b : ℕ) :
    geoSliceSidePairOffsets z = some (a, b) ↔
      geoSliceSidePairLeastCoalescence z a b := by
  by_cases h : ∃ a b, geoSliceSidePairLeastCoalescence z a b
  · simp only [geoSliceSidePairOffsets, dite_eq_left h, Option.some.injEq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨ha, hb⟩
      rw [← ha, ← hb]
      exact h.choose_spec.choose_spec
    · intro hab
      exact geoSliceSidePairLeastCoalescence_unique h.choose_spec.choose_spec hab
  · simp only [geoSliceSidePairOffsets, dite_eq_right h]
    constructor
    · intro he
      cases he
    · intro hab
      exact (h ⟨a, b, hab⟩).elim

/-- Helper toward Lemma 5.6: each aligned-tail event is measurable by
countably many equality tests on the marked seams. -/
theorem measurableSet_geoSliceSidePairTailsCoalesce (a b : ℕ) :
    MeasurableSet {z : GeoSliceSidePairData | geoSliceSidePairTailsCoalesce z a b} := by
  have hL : Measurable (fun z : GeoSliceSidePairData => geometricSideCode z.1.1) :=
    (comap_measurable geometricSideCode).comp measurable_fst.fst
  have hR : Measurable (fun z : GeoSliceSidePairData => geometricSideCode z.1.2) :=
    (comap_measurable geometricSideCode).comp measurable_fst.snd
  simp only [geoSliceSidePairTailsCoalesce, Set.ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    ((hL.snd.snd.snd.snd.snd.snd.snd.snd.snd.eval (a := a + n)).fst.eq
      (hR.snd.snd.snd.snd.snd.snd.snd.snd.snd.eval (a := b + n)).fst).setOf

/-- Helper toward Lemma 5.6: least-coalescence events are measurable;
leastness quantifies only over the countable pair of natural offsets. -/
theorem measurableSet_geoSliceSidePairLeastCoalescence (a b : ℕ) :
    MeasurableSet {z : GeoSliceSidePairData |
      geoSliceSidePairLeastCoalescence z a b} := by
  have he : {z : GeoSliceSidePairData | geoSliceSidePairLeastCoalescence z a b} =
      {z | geoSliceSidePairTailsCoalesce z a b} ∩
        ⋂ i : ℕ, ⋂ j : ℕ,
          ({z | geoSliceSidePairTailsCoalesce z i j}ᶜ ∪
            {z | a ≤ i ∧ b ≤ j}) := by
    ext z
    simp only [geoSliceSidePairLeastCoalescence, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq,
      ← imp_iff_not_or]
  rw [he]
  exact (measurableSet_geoSliceSidePairTailsCoalesce a b).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      (measurableSet_geoSliceSidePairTailsCoalesce i j).compl.union
        (MeasurableSet.const (a ≤ i ∧ b ≤ j)))

local instance : MeasurableSpace (Option (ℕ × ℕ)) := ⊤

/-- Helper toward Lemma 5.6: classical choice of the least offsets is
measurable because its graph is measurable and its value is unique in a
countable space. No measurable-choice assumption is used. -/
theorem measurable_geoSliceSidePairOffsets : Measurable geoSliceSidePairOffsets := by
  apply measurable_to_countable'
  intro p
  cases p with
  | none =>
    have he : geoSliceSidePairOffsets ⁻¹' {none} =
        (⋃ a : ℕ, ⋃ b : ℕ,
          {z | geoSliceSidePairLeastCoalescence z a b})ᶜ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, geoSliceSidePairOffsets,
        Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      split <;> simp_all only [Option.some_ne_none, not_true_eq_false,
        not_false_eq_true]
    rw [he]
    exact (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      measurableSet_geoSliceSidePairLeastCoalescence a b).compl
  | some p =>
    have he : geoSliceSidePairOffsets ⁻¹' {some p} =
        {z | geoSliceSidePairLeastCoalescence z p.1 p.2} := by
      ext z
      exact geoSliceSidePairOffsets_eq_some_iff z p.1 p.2
    rw [he]
    exact measurableSet_geoSliceSidePairLeastCoalescence p.1 p.2

/-- Helper toward Lemma 5.6: recover the initial-vertex sequences from
the west endpoints of the forward marked seams, and insert a pair of offsets
into the labeled cutting data. Source seams are forward darts. -/
@[expose] def geoSliceSidePairLabeledData (z : GeoSliceSidePairData) (p : ℕ × ℕ) :
    GeoSliceLabeledData :=
  (z.1, z.2, (fun n => z.1.1.west (z.1.1.seam n).1),
    (fun n => z.1.2.west (z.1.2.seam n).1), p.1, p.2)

/-- Helper toward Lemma 5.6: recovering the seam vertices and inserting
fixed offsets is measurable in the common labeled side-pair data. -/
theorem measurable_geoSliceSidePairLabeledData (p : ℕ × ℕ) :
    Measurable (fun z => geoSliceSidePairLabeledData z p) := by
  have hL : Measurable (fun z : GeoSliceSidePairData => geometricSideCode z.1.1) :=
    (comap_measurable geometricSideCode).comp measurable_fst.fst
  have hR : Measurable (fun z : GeoSliceSidePairData => geometricSideCode z.1.2) :=
    (comap_measurable geometricSideCode).comp measurable_fst.snd
  have hvL : Measurable (fun z : GeoSliceSidePairData =>
      fun n => z.1.1.west (z.1.1.seam n).1) :=
    measurable_pi_iff.mpr fun n => measurable_geoSlice_eval.comp
      (hL.snd.snd.fst.prodMk
        (hL.snd.snd.snd.snd.snd.snd.snd.snd.snd.eval (a := n)).fst)
  have hvR : Measurable (fun z : GeoSliceSidePairData =>
      fun n => z.1.2.west (z.1.2.seam n).1) :=
    measurable_pi_iff.mpr fun n => measurable_geoSlice_eval.comp
      (hR.snd.snd.fst.prodMk
        (hR.snd.snd.snd.snd.snd.snd.snd.snd.snd.eval (a := n)).fst)
  exact measurable_fst.prodMk (measurable_snd.prodMk
    (hvL.prodMk (hvR.prodMk (measurable_const.prodMk measurable_const))))

/-- Helper toward Lemma 5.6: a fixed reader on common labeled side
pairs. It computes the least offsets from the two seams and returns their
slice class, or `none` when no least pair exists. -/
@[expose] noncomputable def geoSliceSidePairClassOption (z : GeoSliceSidePairData) :
    Option GeometricSideClass :=
  match geoSliceSidePairOffsets z with
  | none => none
  | some p => some (geometricSideClass
      (geoSliceOfLabeledData (geoSliceSidePairLabeledData z p)))

/-- Helper toward Lemma 5.6: the fixed class reader is measurable on
the entire common labeled side-pair space. -/
theorem measurable_geoSliceSidePairClassOption :
    Measurable geoSliceSidePairClassOption := by
  let f (z : GeoSliceSidePairData × Option (ℕ × ℕ)) : Option GeometricSideClass :=
    match z.2 with
    | none => none
    | some p => some (geometricSideClass
        (geoSliceOfLabeledData (geoSliceSidePairLabeledData z.1 p)))
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro p
    cases p with
    | none => exact measurable_const
    | some p =>
      exact measurable_some_geometricSideClass.comp
        (measurable_geoSliceOfLabeledData_class.comp
          (measurable_geoSliceSidePairLabeledData p))
  exact hf.comp (measurable_id.prodMk measurable_geoSliceSidePairOffsets)

/-- Helper toward Lemma 5.6: the common labeled reader recovers the
actual candidate slice for every source family and every least pair. All
ten fields are retained, and no measurability premise is added. -/
theorem geoSliceSidePairClassOption_source_eq
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    geoSliceSidePairClassOption
      ((m0GeodesicSide hp (P (k - 1)) .right,
          m0GeodesicSide hp (P k) .left),
        (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)) =
      some (geometricSideClass (m0CutGeodesicSlice (hp := hp) P k a b hab)) := by
  let z : GeoSliceSidePairData :=
    ((m0GeodesicSide hp (P (k - 1)) .right, m0GeodesicSide hp (P k) .left),
      (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool))
  have htail (i j : ℕ) : geoSliceSidePairTailsCoalesce z i j ↔
      M0CutEdgeTailsCoalesce (P (k - 1)) (P k) i j := by
    constructor
    · intro hco n
      exact congrArg (wholePlaneEdgeι W 0) (hco n)
    · intro hco n
      exact wholePlaneEdgeι_injective W 0 (hco n)
  have hleast : geoSliceSidePairLeastCoalescence z a b :=
    ⟨(htail a b).mpr hab.1, fun i j hij => hab.2 i j ((htail i j).mp hij)⟩
  have hoff := (geoSliceSidePairOffsets_eq_some_iff z a b).mpr hleast
  change geoSliceSidePairClassOption z = _
  unfold geoSliceSidePairClassOption
  rw [hoff]
  change some (geometricSideClass
    (geoSliceOfLabeledData (geoSliceSidePairLabeledData z (a, b)))) = _
  have hvL : (fun n => edgeWest (shiftedStream W 0)
      ((P (k - 1)).codePath.edge n)) =
        (fun n => ((P (k - 1)).codePath.initial n).1.id) :=
    funext fun n => ((P (k - 1)).codePath.edge_outgoing_at_initial
      (shiftedStream W 0) n).2
  have hvR : (fun n => edgeWest (shiftedStream W 0) ((P k).codePath.edge n)) =
      (fun n => ((P k).codePath.initial n).1.id) :=
    funext fun n => ((P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) n).2
  have hdata : geoSliceSidePairLabeledData z (a, b) =
      ((m0GeodesicSide hp (P (k - 1)) .right, m0GeodesicSide hp (P k) .left),
        ((kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool),
          (fun n => ((P (k - 1)).codePath.initial n).1.id),
          (fun n => ((P k).codePath.initial n).1.id), a, b)) := by
    change (z.1, z.2, _, _, a, b) = (z.1, z.2, _, _, a, b)
    rw [show (fun n => z.1.1.west (z.1.1.seam n).1) = _ from hvL,
      show (fun n => z.1.2.west (z.1.2.seam n).1) = _ from hvR]
  rw [hdata, geoSliceOfLabeledData_source_eq hp P k a b hab]

/-- Helper toward Lemma 5.6: the common labeled side pair associated
with one source witness and one adjacent pair of geodesics. -/
@[expose] noncomputable def M0CutGeodesicSliceWitness.sidePairData
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    GeoSliceSidePairData :=
  ((m0GeodesicSide s.hp (s.P (k - 1)) .right,
      m0GeodesicSide s.hp (s.P k) .left),
    (kmswInfRot (shiftedStream W 0) (s.H.1 0) : (ℕ × Bool) → ℕ × Bool))

/-- Helper toward Lemma 5.6: the fixed measurable reader returns the
source slice class for every member of a source witness family. -/
theorem M0CutGeodesicSliceWitness.sidePairData_class
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    geoSliceSidePairClassOption (s.sidePairData k) =
      some (geometricSideClass (m0CutGeodesicSlice (hp := s.hp) s.P k
        (s.thetaMinus k) (s.theta k) (s.least k))) :=
  geoSliceSidePairClassOption_source_eq s.hp s.P k
    (s.thetaMinus k) (s.theta k) (s.least k)





theorem m0Cut_ae_geodesicSlice_class_reader (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ k : ℤ,
        m0CutGeodesicSliceClassOption x k W =
          geoSliceSidePairClassOption (s.sidePairData k) := by
  filter_upwards [ae_m0CutGeodesicSliceWitness x] with W hW
  let s := Classical.choice hW
  refine ⟨s, fun k => ?_⟩
  rw [s.sidePairData_class k]
  exact dite_eq_left hW













































/- All 25 proved theorems (including the four private lemmas), and the nine
supporting definitions probed, use at most propext, Classical.choice and
Quot.sound. No custom axiom or sorryAx occurred. The probes were removed
scheduled fresh-kernel check remain with the sole coordinator. -/

end DirectedDistances.PaperProofs.Section5
