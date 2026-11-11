/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarInverseWalk

/-! # Characterization helpers for the inverse KMSW walk

Helpers toward Definition 3.7 (`defn:KMSW-inv`), -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
unit increments along the selected upper-left parent edges is uniquely the
canonical upper-left height. -/
theorem canonicalULHeight_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (h : MapVertex B.map → ℕ)
    (h₀ : h B.source = 0)
    (hstep : ∀ v, v ≠ B.source →
      h v = h (ulParent B (canonicalULSelector B) v) + 1) :
    h = canonicalULHeight B := by
  funext v
  have haux : ∀ n, ∀ v, canonicalULHeight B v = n →
      h v = canonicalULHeight B v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro v hv
        by_cases hsource : v = B.source
        · subst v
          have hcan : canonicalULHeight B B.source = 0 := by
            simpa [canonicalULHeight] using
              ulHeight_source B (canonicalULSelector B)
          rw [h₀, hcan]
        · let p := ulParent B (canonicalULSelector B) v
          have hrec : canonicalULHeight B v = canonicalULHeight B p + 1 := by
            simpa only [canonicalULHeight, p] using
              ulHeight_parent B (canonicalULSelector B) hsource
          have hp_lt : canonicalULHeight B p < n := by
            rw [← hv, hrec]
            omega
          have hp := ih (canonicalULHeight B p) hp_lt p rfl
          calc
            h v = h p + 1 := by
              simpa only [p] using hstep v hsource
            _ = canonicalULHeight B p + 1 := by rw [hp]
            _ = canonicalULHeight B v := hrec.symm
  exact haux (canonicalULHeight B v) v rfl

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
unit increments along the selected lower-right parent edges is uniquely the
canonical lower-right height. -/
theorem canonicalLRHeight_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (h : MapVertex B.map → ℕ)
    (h₀ : h B.sink = 0)
    (hstep : ∀ v, v ≠ B.sink →
      h v = h (lrParent B (canonicalLRSelector B) v) + 1) :
    h = canonicalLRHeight B := by
  funext v
  have haux : ∀ n, ∀ v, canonicalLRHeight B v = n →
      h v = canonicalLRHeight B v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro v hv
        by_cases hsink : v = B.sink
        · subst v
          have hcan : canonicalLRHeight B B.sink = 0 := by
            simpa [canonicalLRHeight] using
              lrHeight_sink B (canonicalLRSelector B)
          rw [h₀, hcan]
        · let p := lrParent B (canonicalLRSelector B) v
          have hrec : canonicalLRHeight B v = canonicalLRHeight B p + 1 := by
            simpa only [canonicalLRHeight, p] using
              lrHeight_parent B (canonicalLRSelector B) hsink
          have hp_lt : canonicalLRHeight B p < n := by
            rw [← hv, hrec]
            omega
          have hp := ih (canonicalLRHeight B p) hp_lt p rfl
          calc
            h v = h p + 1 := by
              simpa only [p] using hstep v hsink
            _ = canonicalLRHeight B p + 1 := by rw [hp]
            _ = canonicalLRHeight B v := hrec.symm
  exact haux (canonicalLRHeight B v) v rfl

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
upper-left parent edge is the leftmost incoming edge, expressed using the
project's reverse-dart representation of `leftmostIncoming`. -/
theorem canonicalULParentEdge_leftmostIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hv : v ≠ B.source) :
    (canonicalULSelector B v hv).val =
      B.map.toCombinatorialMap.edgeInv (leftmostIncoming B v hv) :=
  canonicalULSelector_val B v hv

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
rightmost outgoing edge in the project's dart representation. -/
theorem canonicalLRParentEdge_rightmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hv : v ≠ B.sink) :
    (canonicalLRSelector B v hv).val = rightmostOutgoing B v hv :=
  canonicalLRSelector_val B v hv

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
the `j`-th entry of the upper-left contour's forward-dart first-visit order;
this is the source edge `λ_{j+1}`. -/
theorem peanoEdge_eq_firstVisitOrder_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (j : Fin B.map.toCombinatorialMap.numEdges) :
    peanoEdge B j =
      (firstVisitOrder B).get
        ⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩ :=
  rfl

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`), -/
theorem peanoEdge_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Function.Injective (peanoEdge B) := by
  intro i j hij
  have hget : (firstVisitOrder B).get
      ⟨i.val, by rw [firstVisitOrder_length]; exact i.isLt⟩ =
    (firstVisitOrder B).get
      ⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩ := by
    simpa only [peanoEdge_eq_firstVisitOrder_get] using hij
  have hidx := (firstVisitOrder_nodup B).get_inj_iff.mp hget
  apply Fin.ext
  exact congrArg (fun q : Fin (firstVisitOrder B).length => q.val) hidx

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
index in the Peano first-visit order. -/
theorem peanoEdge_surjective_forward
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : B.map.tail d) : ∃ j, peanoEdge B j = d := by
  have hmem : d ∈ firstVisitOrder B :=
    (mem_firstVisitOrder_iff B d).2 hd
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  have hbound : i.val < B.map.toCombinatorialMap.numEdges := by
    rw [← firstVisitOrder_length]
    exact i.isLt
  refine ⟨⟨i.val, hbound⟩, ?_⟩
  rw [peanoEdge_eq_firstVisitOrder_get]
  exact hi

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
bijection from its indices onto the geometric edge quotient, preserving edge
identity (including parallel edges). -/
theorem peanoEdge_bijective_edges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Function.Bijective (fun j : Fin B.map.toCombinatorialMap.numEdges =>
      (Quotient.mk (Equiv.Perm.SameCycle.setoid
        B.map.toCombinatorialMap.edgeInv) (peanoEdge B j) :
          CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap)) := by
  constructor
  · intro i j hij
    have horbit : B.map.toCombinatorialMap.edgeInv.SameCycle
        (peanoEdge B i) (peanoEdge B j) := Quotient.exact hij
    rcases (CombinatorialMap.edgeInv_sameCycle_iff
        B.map.toCombinatorialMap (peanoEdge B i) (peanoEdge B j)).mp horbit with
      h | h
    · exact peanoEdge_injective B h.symm
    · have hnot : ¬ B.map.tail
          (B.map.toCombinatorialMap.edgeInv (peanoEdge B i)) :=
        (B.map.tail_iff (peanoEdge B i) (B.noMissingDarts _)).mp
          (peanoEdge_forward B i)
      exact False.elim (hnot (h ▸ peanoEdge_forward B j))
  · intro q
    induction q using Quotient.inductionOn with
    | h d =>
        by_cases htail : B.map.tail d
        · obtain ⟨j, hj⟩ := peanoEdge_surjective_forward B htail
          refine ⟨j, ?_⟩
          change Quotient.mk _ (peanoEdge B j) = Quotient.mk _ d
          rw [hj]
        · have hinvTail : B.map.tail
              (B.map.toCombinatorialMap.edgeInv d) := by
            apply (B.map.tail_iff (B.map.toCombinatorialMap.edgeInv d)
              (B.noMissingDarts _)).2
            simpa only [B.map.toCombinatorialMap.edgeInv_invol] using htail
          obtain ⟨j, hj⟩ := peanoEdge_surjective_forward B hinvTail
          refine ⟨j, ?_⟩
          change Quotient.mk _ (peanoEdge B j) = Quotient.mk _ d
          rw [hj]
          apply Quotient.sound
          exact (Equiv.Perm.SameCycle.refl
            B.map.toCombinatorialMap.edgeInv d).apply_left

/-- Helper toward Definition 3.7 (`defn:KMSW-inv`),
heights from `canonicalULHeight_unique` and `canonicalLRHeight_unique`, and
the contour-order identification `peanoEdge_eq_firstVisitOrder_get`, the
inverse walk has the source's coordinate formula. -/
theorem bipolarInverseWalk_source_form
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (hUL : MapVertex B.map → ℕ)
    (hUL_zero : hUL B.source = 0)
    (hUL_step : ∀ v, v ≠ B.source →
      hUL v = hUL (ulParent B (canonicalULSelector B) v) + 1)
    (hLR : MapVertex B.map → ℕ)
    (hLR_zero : hLR B.sink = 0)
    (hLR_step : ∀ v, v ≠ B.sink →
      hLR v = hLR (lrParent B (canonicalLRSelector B) v) + 1)
    (j : Fin B.map.toCombinatorialMap.numEdges) :
    bipolarInverseWalk B j =
      ((hUL (dartTailVertex B.map
          ((firstVisitOrder B).get
            ⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩)) : ℤ),
       (hLR (dartHeadVertex B.map
          ((firstVisitOrder B).get
            ⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩)) : ℤ) -
        ((r - 1 : ℕ) : ℤ)) := by
  rw [bipolarInverseWalk,
    ← canonicalULHeight_unique B hUL hUL_zero hUL_step,
    ← canonicalLRHeight_unique B hLR hLR_zero hLR_step]
  rfl

end DirectedDistances.PlanarMap
