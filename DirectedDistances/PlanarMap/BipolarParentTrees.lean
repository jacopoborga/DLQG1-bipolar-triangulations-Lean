/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralBipolarBoundary

/-! # Parent selectors and heights for the inverse trees

Helper toward `thm-kmsw` (inverse trees); not the paper result. The source
constructs the two parent trees in `defn:KMSW-inv` -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. For every
non-source vertex, an incoming selector chooses a present dart whose head is -/
@[expose] def IncomingSelector (B : BipolarTriangulationWithBoundaryBase D ℓ r) :=
  ∀ v : MapVertex B.map, v ≠ B.source →
    {d : D // ¬ B.map.missing d ∧ B.map.tail d ∧ dartHeadVertex B.map d = v}

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Unique
source implies that every non-source vertex has an incoming present dart -/
theorem exists_incomingSelector
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nonempty (IncomingSelector B) := by
  classical
  refine ⟨fun v hv => ?_⟩
  have hpred : ∃ u, B.map.directedStep u v := by
    by_contra h
    have hsource := B.source_unique v h
    exact hv hsource
  have hd : ∃ d, ¬ B.map.missing d ∧ B.map.tail d ∧
      dartHeadVertex B.map d = v := by
    obtain ⟨u, d, hmissing, htail, _htailVertex, hheadVertex⟩ := hpred
    exact ⟨d, hmissing, htail, hheadVertex⟩
  exact ⟨Classical.choose hd, Classical.choose_spec hd⟩

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
positive directed reachability relation is well founded on the finite vertex -/
theorem directedReach_wellFounded
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    WellFounded (Relation.TransGen B.map.directedStep) := by
  let R := Relation.TransGen B.map.directedStep
  let htrans : IsTrans (MapVertex B.map) R :=
    ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩
  let hirrefl : Std.Irrefl R := ⟨B.acyclic⟩
  let hstrict : IsStrictOrder (MapVertex B.map) R :=
    @IsStrictOrder.mk (MapVertex B.map) R hirrefl htrans
  exact Set.wellFoundedOn_univ.mp
    (@Set.Finite.wellFoundedOn (MapVertex B.map) R hstrict Set.univ Set.finite_univ)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. At a
non-source vertex, the parent is the initial vertex of its selected incoming -/
@[expose] noncomputable def ulParent
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) (v : MapVertex B.map) : MapVertex B.map := by
  classical
  exact if h : v = B.source then B.source else dartTailVertex B.map (sel v h).val

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
selected incoming dart is an edge from its parent to the given vertex -/
theorem ulParent_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) {v : MapVertex B.map} (hv : v ≠ B.source) :
    B.map.directedStep (ulParent B sel v) v := by
  classical
  simp [ulParent, hv]
  exact ⟨(sel v hv).val, (sel v hv).property.1, (sel v hv).property.2.1,
    rfl, (sel v hv).property.2.2⟩

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
well-founded recursion step adds one when the current vertex is not the source -/
@[expose] noncomputable def ulHeightStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) (v : MapVertex B.map)
    (ih : ∀ w, Relation.TransGen B.map.directedStep w v → ℕ) : ℕ := by
  classical
  exact if h : v = B.source then 0 else
    ih (ulParent B sel v) (Relation.TransGen.single (ulParent_step B sel h)) + 1

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Height
counts the parent steps to the source; recursion terminates by acyclicity and -/
@[expose] noncomputable def ulHeight
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) : MapVertex B.map → ℕ := by
  let R := Relation.TransGen B.map.directedStep
  letI : WellFounded R := directedReach_wellFounded B
  exact WellFounded.fix' R (ulHeightStep B sel)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The -/
theorem ulHeight_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) : ulHeight B sel B.source = 0 := by
  let R := Relation.TransGen B.map.directedStep
  have hfix := @WellFounded.fix'_eq (MapVertex B.map) R
    (directedReach_wellFounded B) (fun _ => ℕ) (ulHeightStep B sel)
  have h := hfix B.source
  simpa [ulHeight, ulHeightStep] using h

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Every
non-source height is one more than its parent's height -/
theorem ulHeight_parent
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) {v : MapVertex B.map} (hv : v ≠ B.source) :
    ulHeight B sel v = ulHeight B sel (ulParent B sel v) + 1 := by
  let R := Relation.TransGen B.map.directedStep
  have hfix := @WellFounded.fix'_eq (MapVertex B.map) R
    (directedReach_wellFounded B) (fun _ => ℕ) (ulHeightStep B sel)
  have h := hfix v
  simpa [ulHeight, ulHeightStep, hv] using h

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. For every
non-sink vertex, an outgoing selector chooses a present dart with that vertex -/
@[expose] def OutgoingSelector (B : BipolarTriangulationWithBoundaryBase D ℓ r) :=
  ∀ v : MapVertex B.map, v ≠ B.sink →
    {d : D // ¬ B.map.missing d ∧ B.map.tail d ∧ dartTailVertex B.map d = v}

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Unique
sink implies that every non-sink vertex has an outgoing present dart -/
theorem exists_outgoingSelector
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nonempty (OutgoingSelector B) := by
  classical
  refine ⟨fun v hv => ?_⟩
  have hnext : ∃ w, B.map.directedStep v w := by
    by_contra h
    have hsink := B.sink_unique v h
    exact hv hsink
  have hd : ∃ d, ¬ B.map.missing d ∧ B.map.tail d ∧
      dartTailVertex B.map d = v := by
    obtain ⟨w, d, hmissing, htail, htailVertex, _hheadVertex⟩ := hnext
    exact ⟨d, hmissing, htail, htailVertex⟩
  exact ⟨Classical.choose hd, Classical.choose_spec hd⟩

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. At a
non-sink vertex, the parent is the terminal vertex of its selected outgoing -/
@[expose] noncomputable def lrParent
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) (v : MapVertex B.map) : MapVertex B.map := by
  classical
  exact if h : v = B.sink then B.sink else dartHeadVertex B.map (sel v h).val

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
selected outgoing dart points from a non-sink vertex to its parent -/
theorem lrParent_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) {v : MapVertex B.map} (hv : v ≠ B.sink) :
    B.map.directedStep v (lrParent B sel v) := by
  classical
  simp [lrParent, hv]
  exact ⟨(sel v hv).val, (sel v hv).property.1, (sel v hv).property.2.1,
    (sel v hv).property.2.2, rfl⟩

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Reverse
positive reachability is well founded on the finite vertex set of an acyclic -/
theorem reverseDirectedReach_wellFounded
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    WellFounded (Relation.TransGen (fun a b => B.map.directedStep b a)) := by
  let R := Relation.TransGen (fun a b => B.map.directedStep b a)
  let htrans : IsTrans (MapVertex B.map) R :=
    ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩
  let hirrefl : Std.Irrefl R := ⟨fun a h => B.acyclic a (Relation.transGen_swap.mp h)⟩
  let hstrict : IsStrictOrder (MapVertex B.map) R :=
    @IsStrictOrder.mk (MapVertex B.map) R hirrefl htrans
  exact Set.wellFoundedOn_univ.mp
    (@Set.Finite.wellFoundedOn (MapVertex B.map) R hstrict Set.univ Set.finite_univ)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
well-founded recursion step adds one when the current vertex is not the sink -/
@[expose] noncomputable def lrHeightStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) (v : MapVertex B.map)
    (ih : ∀ w, Relation.TransGen (fun a b => B.map.directedStep b a) w v → ℕ) : ℕ := by
  classical
  exact if h : v = B.sink then 0 else
    ih (lrParent B sel v)
      (Relation.TransGen.single (show
        (fun a b => B.map.directedStep b a) (lrParent B sel v) v from
          lrParent_step B sel h)) + 1

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Height
counts the parent steps to the sink; recursion terminates by acyclicity and -/
@[expose] noncomputable def lrHeight
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) : MapVertex B.map → ℕ := by
  let R := Relation.TransGen (fun a b => B.map.directedStep b a)
  letI : WellFounded R := reverseDirectedReach_wellFounded B
  exact WellFounded.fix' R (lrHeightStep B sel)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The sink -/
theorem lrHeight_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) : lrHeight B sel B.sink = 0 := by
  let R := Relation.TransGen (fun a b => B.map.directedStep b a)
  have hfix := @WellFounded.fix'_eq (MapVertex B.map) R
    (reverseDirectedReach_wellFounded B) (fun _ => ℕ) (lrHeightStep B sel)
  have h := hfix B.sink
  simpa [lrHeight, lrHeightStep] using h

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Every
non-sink height is one more than its parent's height -/
theorem lrHeight_parent
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) {v : MapVertex B.map} (hv : v ≠ B.sink) :
    lrHeight B sel v = lrHeight B sel (lrParent B sel v) + 1 := by
  let R := Relation.TransGen (fun a b => B.map.directedStep b a)
  have hfix := @WellFounded.fix'_eq (MapVertex B.map) R
    (reverseDirectedReach_wellFounded B) (fun _ => ℕ) (lrHeightStep B sel)
  have h := hfix v
  simpa [lrHeight, lrHeightStep, hv] using h

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Every
vertex reaches the source by iterating the upper-left parent map -/
theorem ulParent_reaches_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) (v : MapVertex B.map) :
    Relation.ReflTransGen
      (fun a b : MapVertex B.map => a ≠ B.source ∧ ulParent B sel a = b)
      v B.source := by
  let H := ulHeight B sel
  induction hH : H v using Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hv : v = B.source
      · subst v
        exact Relation.ReflTransGen.refl
      · have hparent : H (ulParent B sel v) + 1 = n := by
          have hp := ulHeight_parent B sel hv
          change H v = H (ulParent B sel v) + 1 at hp
          omega
        have hlt : H (ulParent B sel v) < n := by omega
        have hrec := ih (H (ulParent B sel v)) hlt (ulParent B sel v) rfl
        exact Relation.ReflTransGen.head ⟨hv, rfl⟩ hrec

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Every
vertex reaches the sink by iterating the lower-right parent map -/
theorem lrParent_reaches_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) (v : MapVertex B.map) :
    Relation.ReflTransGen
      (fun a b : MapVertex B.map => a ≠ B.sink ∧ lrParent B sel a = b)
      v B.sink := by
  let H := lrHeight B sel
  induction hH : H v using Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hv : v = B.sink
      · subst v
        exact Relation.ReflTransGen.refl
      · have hparent : H (lrParent B sel v) + 1 = n := by
          have hp := lrHeight_parent B sel hv
          change H v = H (lrParent B sel v) + 1 at hp
          omega
        have hlt : H (lrParent B sel v) < n := by omega
        have hrec := ih (H (lrParent B sel v)) hlt (lrParent B sel v) rfl
        exact Relation.ReflTransGen.head ⟨hv, rfl⟩ hrec

private theorem card_vertex_ne (V : Type*) [Fintype V] [DecidableEq V]
    (root : V) : Fintype.card {v : V // v ≠ root} = Fintype.card V - 1 := by
  classical
  let e : {v : V // v ≠ root} ≃ {v : V // v ∈ ({root}ᶜ : Set V)} := {
    toFun := fun v => ⟨v.1, (Set.mem_compl_iff _ _).2 (by
      simpa only [Set.mem_singleton_iff] using v.2)⟩
    invFun := fun v => ⟨v.1, by
      have hv : v.1 ∉ ({root} : Set V) := (Set.mem_compl_iff _ _).1 v.2
      simpa only [Set.mem_singleton_iff] using hv⟩
    left_inv := by intro v; rfl
    right_inv := by intro v; rfl
  }
  calc
    Fintype.card {v : V // v ≠ root} =
        Fintype.card {v : V // v ∈ ({root}ᶜ : Set V)} := Fintype.card_congr e
    _ = Fintype.card V - Fintype.card ({root} : Set V) := Fintype.card_compl_set _
    _ = Fintype.card V - 1 := by simp

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
upper-left selector assigns an edge orbit to each non-source vertex -/
@[expose] noncomputable def ulSelectedEdge
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) (v : {v : MapVertex B.map // v ≠ B.source}) :
    CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.edgeInv)
    (sel v.1 v.2).val

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Selected -/
theorem ulSelectedEdge_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) : Function.Injective (ulSelectedEdge B sel) := by
  classical
  intro a b hab
  let d := (sel a.1 a.2).val
  let e := (sel b.1 b.2).val
  have horbit : B.map.toCombinatorialMap.edgeInv.SameCycle d e := Quotient.exact hab
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap d e).mp
      horbit with heq | heq
  · apply Subtype.ext
    calc
      a.1 = dartHeadVertex B.map d := (sel a.1 a.2).property.2.2.symm
      _ = dartHeadVertex B.map e := by rw [heq]
      _ = b.1 := (sel b.1 b.2).property.2.2
  · have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv d) :=
      (B.map.tail_iff d (sel a.1 a.2).property.1).mp (sel a.1 a.2).property.2.1
    exfalso
    apply hnot
    rw [← heq]
    exact (sel b.1 b.2).property.2.1

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
finite set of upper-left selected edge orbits -/
@[expose] noncomputable def ulSelectedEdges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) :
    Finset (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) := by
  classical
  exact Finset.univ.image (ulSelectedEdge B sel)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
upper-left tree selects exactly `numVertices - 1` distinct edges -/
theorem ulSelectedEdges_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : IncomingSelector B) :
    (ulSelectedEdges B sel).card = B.map.toCombinatorialMap.numVertices - 1 := by
  classical
  calc
    (ulSelectedEdges B sel).card =
        Fintype.card {v : MapVertex B.map // v ≠ B.source} := by
          unfold ulSelectedEdges
          exact Finset.card_image_of_injective Finset.univ (ulSelectedEdge_injective B sel)
    _ = Fintype.card (MapVertex B.map) - 1 := card_vertex_ne _ B.source
    _ = B.map.toCombinatorialMap.numVertices - 1 := by
      simp [CombinatorialMap.numVertices]

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
lower-right selector assigns an edge orbit to each non-sink vertex -/
@[expose] noncomputable def lrSelectedEdge
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) (v : {v : MapVertex B.map // v ≠ B.sink}) :
    CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.edgeInv)
    (sel v.1 v.2).val

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Selected -/
theorem lrSelectedEdge_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) : Function.Injective (lrSelectedEdge B sel) := by
  classical
  intro a b hab
  let d := (sel a.1 a.2).val
  let e := (sel b.1 b.2).val
  have horbit : B.map.toCombinatorialMap.edgeInv.SameCycle d e := Quotient.exact hab
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap d e).mp
      horbit with heq | heq
  · apply Subtype.ext
    calc
      a.1 = dartTailVertex B.map d := (sel a.1 a.2).property.2.2.symm
      _ = dartTailVertex B.map e := by rw [heq]
      _ = b.1 := (sel b.1 b.2).property.2.2
  · have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv d) :=
      (B.map.tail_iff d (sel a.1 a.2).property.1).mp (sel a.1 a.2).property.2.1
    exfalso
    apply hnot
    rw [← heq]
    exact (sel b.1 b.2).property.2.1

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
finite set of lower-right selected edge orbits -/
@[expose] noncomputable def lrSelectedEdges
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) :
    Finset (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) := by
  classical
  exact Finset.univ.image (lrSelectedEdge B sel)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
lower-right tree selects exactly `numVertices - 1` distinct edges -/
theorem lrSelectedEdges_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : OutgoingSelector B) :
    (lrSelectedEdges B sel).card = B.map.toCombinatorialMap.numVertices - 1 := by
  classical
  calc
    (lrSelectedEdges B sel).card =
        Fintype.card {v : MapVertex B.map // v ≠ B.sink} := by
          unfold lrSelectedEdges
          exact Finset.card_image_of_injective Finset.univ (lrSelectedEdge_injective B sel)
    _ = Fintype.card (MapVertex B.map) - 1 := card_vertex_ne _ B.sink
    _ = B.map.toCombinatorialMap.numVertices - 1 := by
      simp [CombinatorialMap.numVertices]

end DirectedDistances.PlanarMap
