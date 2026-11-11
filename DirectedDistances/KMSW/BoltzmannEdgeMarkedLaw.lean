/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoltzmannMarkedRightLawProcedure











public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators









@[expose] noncomputable def LeftEdgeMarkedBoltzmannSpace (r : ℕ) :=
  Σ q : AllBoltzmannSpace r, Fin q.1

noncomputable instance (r : ℕ) :
    MeasurableSpace (LeftEdgeMarkedBoltzmannSpace r) := ⊤

instance (r : ℕ) : Countable (LeftEdgeMarkedBoltzmannSpace r) := by
  unfold LeftEdgeMarkedBoltzmannSpace
  infer_instance




@[expose] noncomputable def leftEdgeMarkEdge {r : ℕ}
    (q : AllBoltzmannSpace r) (i : Fin q.1) :
    CombinatorialMap.EdgeQuotient q.2.2.out.B.map.toCombinatorialMap :=
  Quotient.mk _ (q.2.2.out.B.leftPath.darts.get
    ⟨i.val, by rw [q.2.2.out.B.leftPath.darts_length]; exact i.isLt⟩)

/-- Every boundary-preserving isomorphism carries the indexed left-boundary
dart to the same position in the target representative. This uses preservation
of the ordered left path, as required by `def-bipolar-bdy` -/
theorem leftBoundaryDart_eq_of_baseIso {ℓ r n : ℕ}
    {R R' : KMSWMapRep ℓ r n} (I : BipolarBoundaryBaseIso R.B R'.B)
    (i : Fin ℓ) :
    I.toEquiv (R.B.leftPath.darts.get
      ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩) =
      R'.B.leftPath.darts.get
        ⟨i.val, by rw [R'.B.leftPath.darts_length]; exact i.isLt⟩ := by
  simp only [List.get_eq_getElem, ← I.leftDarts, List.getElem_map]





theorem leftBoundaryEdge_eq_of_baseIso {ℓ r n : ℕ}
    {R R' : KMSWMapRep ℓ r n} (I : BipolarBoundaryBaseIso R.B R'.B)
    (i : Fin ℓ) :
    I.edgeEquiv (Quotient.mk _ (R.B.leftPath.darts.get
      ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩)) =
      Quotient.mk _ (R'.B.leftPath.darts.get
        ⟨i.val, by rw [R'.B.leftPath.darts_length]; exact i.isLt⟩) := by
  change Quotient.mk _ (I.toEquiv (R.B.leftPath.darts.get _)) =
    Quotient.mk _ (R'.B.leftPath.darts.get _)
  exact congrArg (Quotient.mk _) (leftBoundaryDart_eq_of_baseIso I i)




theorem leftEdgeMarkEdge_map {r : ℕ} (q : AllBoltzmannSpace r)
    {R : KMSWMapRep q.1 r q.2.1}
    (I : BipolarBoundaryBaseIso q.2.2.out.B R.B) (i : Fin q.1) :
    I.edgeEquiv (leftEdgeMarkEdge q i) =
      Quotient.mk _ (R.B.leftPath.darts.get
        ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩) :=
  leftBoundaryEdge_eq_of_baseIso I i




@[expose] noncomputable def leftEdgeMarkedWeight {r : ℕ}
    (p : LeftEdgeMarkedBoltzmannSpace r) : ENNReal :=
  allBoltzmannWeight p.1




@[expose] noncomputable def leftEdgeMarkedPartition (r : ℕ) : ENNReal :=
  ∑' p : LeftEdgeMarkedBoltzmannSpace r, leftEdgeMarkedWeight p




@[expose] noncomputable def leftEdgeMarkedBoltzmannLaw (r : ℕ) :
    Measure (LeftEdgeMarkedBoltzmannSpace r) :=
  (leftEdgeMarkedPartition r)⁻¹ •
    Measure.sum (fun p : LeftEdgeMarkedBoltzmannSpace r =>
      leftEdgeMarkedWeight p • Measure.dirac p)

/-- Summing over the `ℓ` abstract left-boundary positions multiplies a map's
weight by its left-boundary length. Each position selects a geometric edge orbit
on the chosen representative, and selection transports through every boundary
isomorphism. The all-outer-boundary-edge variant is not covered because this
carrier supplies no right-boundary marks. Helper toward Lemma 3.12
paper result. -/
theorem leftEdgeMarkedPartition_eq_tsum (r : ℕ) :
    leftEdgeMarkedPartition r =
      ∑' q : AllBoltzmannSpace r,
        (q.1 : ENNReal) * allBoltzmannWeight q := by
  classical
  rw [leftEdgeMarkedPartition]
  change (∑' p : (Σ q : AllBoltzmannSpace r, Fin q.1),
      allBoltzmannWeight p.1) = _
  rw [tsum_sigma']
  apply tsum_congr
  intro q
  rw [tsum_fintype]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Every map class has at least one abstract left-boundary position. This
follows from the positive left-path length on each representative. The
positions select geometric edge orbits on the chosen representative, compatibly
with every boundary isomorphism. All outer-boundary edges are not covered
because this carrier supplies no right-boundary marks. Helper toward Lemma 3.12 -/
theorem allBoltzmannSpace_leftBoundaryLength_pos (r : ℕ)
    (q : AllBoltzmannSpace r) : 1 ≤ q.1 := by
  rcases q with ⟨ell, q⟩
  rcases q with ⟨n, c⟩
  change 1 ≤ ell
  exact KMSWMapIsoClass.ind (motive := fun _ => 1 ≤ ell)
    (fun R => R.B.left_length_pos) c

/-- The sum over left-edge marks is bounded by the left-vertex-marked
the two mark carriers and normalizers remain distinct; not the paper result. -/
theorem leftEdgeMarkedPartition_le_rightVertexMarkedPartition (r : ℕ) :
    leftEdgeMarkedPartition r ≤ rightVertexMarkedPartition r := by
  rw [leftEdgeMarkedPartition_eq_tsum, rightVertexMarkedPartition_eq_tsum]
  apply tsum_le_tsum
  intro q
  have hcount : (q.1 : ENNReal) ≤ ((q.1 + 1 : ℕ) : ENNReal) := by
    exact_mod_cast Nat.le_succ q.1
  exact mul_le_mul_of_nonneg_right hcount (by positivity)

/-- The left-edge-marked partition is finite for positive right boundary
the bound uses the independently defined vertex-marked partition, with no
identification of the two carriers; not the paper result. -/
theorem leftEdgeMarkedPartition_lt_top (r : ℕ) (hr : 1 ≤ r) :
    leftEdgeMarkedPartition r < ⊤ := by
  exact lt_of_le_of_lt
    (leftEdgeMarkedPartition_le_rightVertexMarkedPartition r)
    (rightVertexMarkedPartition_normalizer_procedureReading r hr).2

/-- The edge-marked partition is positive for positive right boundary
length. Positivity comes from a positive-weight map class and its nonempty
left edge set. Helper toward Lemma 3.12
normalizer and is not the paper result. -/
theorem leftEdgeMarkedPartition_pos (r : ℕ) (hr : 1 ≤ r) :
    0 < leftEdgeMarkedPartition r := by
  have hvertex := rightVertexMarkedPartition_normalizer_procedureReading r hr
  have hq : ∃ q : AllBoltzmannSpace r, 0 < allBoltzmannWeight q := by
    by_contra hq
    have hweight : ∀ q : AllBoltzmannSpace r, allBoltzmannWeight q = 0 := by
      intro q
      have hnot : ¬ 0 < allBoltzmannWeight q := by
        intro hpos
        exact hq ⟨q, hpos⟩
      exact le_antisymm (le_of_not_gt hnot) bot_le
    have hzero : rightVertexMarkedPartition r = 0 := by
      rw [rightVertexMarkedPartition_eq_tsum]
      apply tsum_eq_zero_iff.mpr
      intro q
      simp [hweight q]
    exact (ne_of_gt hvertex.1) hzero
  rcases hq with ⟨q, hweight⟩
  have hlength := allBoltzmannSpace_leftBoundaryLength_pos r q
  have hterm : 0 < (q.1 : ENNReal) * allBoltzmannWeight q := by
    positivity
  have hle : (q.1 : ENNReal) * allBoltzmannWeight q ≤
      ∑' p : AllBoltzmannSpace r,
        (p.1 : ENNReal) * allBoltzmannWeight p :=
    le_tsum
      (fun p : AllBoltzmannSpace r =>
        (p.1 : ENNReal) * allBoltzmannWeight p) q
  rw [← leftEdgeMarkedPartition_eq_tsum] at hle
  exact lt_of_lt_of_le hterm hle

/-- The left-edge-marked partition is positive and finite for positive right
boundary length. Helper toward Lemma 3.12
Definition 1.10 vertex-marked normalizer; not the paper result. -/
theorem leftEdgeMarkedPartition_normalizer_procedureReading (r : ℕ)
    (hr : 1 ≤ r) :
    0 < leftEdgeMarkedPartition r ∧ leftEdgeMarkedPartition r < ⊤ :=
  ⟨leftEdgeMarkedPartition_pos r hr, leftEdgeMarkedPartition_lt_top r hr⟩

/-- The normalized law on left-edge-marked maps is a probability measure for
positive right boundary length. Helper toward Lemma 3.12
distinct from the Definition 1.10 vertex-marked law; not the paper result. -/
theorem leftEdgeMarkedBoltzmannLaw_isProbabilityMeasure (r : ℕ)
    (hr : 1 ≤ r) :
    IsProbabilityMeasure (leftEdgeMarkedBoltzmannLaw r) := by
  refine ⟨?_⟩
  rw [leftEdgeMarkedBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  change (leftEdgeMarkedPartition r)⁻¹ *
    (∑' p : LeftEdgeMarkedBoltzmannSpace r, leftEdgeMarkedWeight p) = 1
  rw [← leftEdgeMarkedPartition]
  rcases leftEdgeMarkedPartition_normalizer_procedureReading r hr with
    ⟨hpos, htop⟩
  exact ENNReal.inv_mul_cancel (pos_iff_ne_zero.mp hpos) htop.ne








theorem leftEdgeMarkedWeight_fiber (r : ℕ) (q : AllBoltzmannSpace r)
    (mark : Fin q.1) :
    leftEdgeMarkedWeight (⟨q, mark⟩ : LeftEdgeMarkedBoltzmannSpace r) =
      allBoltzmannWeight q := rfl

end DirectedDistances.KMSW
