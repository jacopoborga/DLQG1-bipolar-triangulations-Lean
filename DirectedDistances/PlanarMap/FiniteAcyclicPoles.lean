/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap
public import Mathlib.Logic.Relation

import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded

/-! # Sources and sinks in finite acyclic orientations -/

public section
namespace DirectedDistances.PlanarMap

/-- A finite nonempty acyclic relation has a source and a sink. Here a source
has no incoming `R`-step and a sink has no outgoing `R`-step. Helper toward -/
theorem exists_source_and_sink {V : Type*} [Finite V] [Nonempty V]
    (R : V → V → Prop)
    (h : ∀ v, ¬ Relation.TransGen R v v) :
    (∃ v, ¬ ∃ u, R u v) ∧ (∃ v, ¬ ∃ w, R v w) := by
  classical
  letI : Std.Irrefl (Relation.TransGen R) := ⟨h⟩
  have hRwf : WellFounded (Relation.TransGen R) :=
    Finite.wellFounded_of_trans_of_irrefl _
  let Rrev : V → V → Prop := Function.swap (Relation.TransGen R)
  letI : IsTrans V Rrev := ⟨fun _ _ _ hab hbc =>
    Relation.TransGen.trans hbc hab⟩
  letI : Std.Irrefl Rrev := ⟨fun v hv => h v hv⟩
  have hRrevwf : WellFounded Rrev := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨s, -, hs⟩ := hRwf.has_min Set.univ Set.univ_nonempty
  obtain ⟨t, -, ht⟩ := hRrevwf.has_min Set.univ Set.univ_nonempty
  constructor
  · refine ⟨s, ?_⟩
    rintro ⟨u, hu⟩
    exact hs u (Set.mem_univ u) (Relation.TransGen.single hu)
  · refine ⟨t, ?_⟩
    rintro ⟨w, hw⟩
    exact ht w (Set.mem_univ w) (Relation.TransGen.single hw)

/-- The literal relation-level bipolar condition from Definition 1.1: the
relation is acyclic and has at most one source and at most one sink. Helper -/
@[expose] def IsBipolarRel {V : Type*} (R : V → V → Prop) : Prop :=
  (∀ v, ¬ Relation.TransGen R v v) ∧
    Subsingleton {v // ¬ ∃ u, R u v} ∧
    Subsingleton {v // ¬ ∃ w, R v w}

/-- A finite nonempty bipolar relation has a unique source and a unique sink. -/
theorem existsUnique_source_and_sink {V : Type*} [Finite V] [Nonempty V]
    (R : V → V → Prop) (hR : IsBipolarRel R) :
    (∃! v, ¬ ∃ u, R u v) ∧ (∃! v, ¬ ∃ w, R v w) := by
  rcases exists_source_and_sink R hR.1 with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  letI : Subsingleton {v // ¬ ∃ u, R u v} := hR.2.1
  letI : Subsingleton {v // ¬ ∃ w, R v w} := hR.2.2
  constructor
  · refine ⟨s, hs, ?_⟩
    intro v hv
    have heq : (⟨v, hv⟩ : {v // ¬ ∃ u, R u v}) = ⟨s, hs⟩ :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val heq
  · refine ⟨t, ht, ?_⟩
    intro v hv
    have heq : (⟨v, hv⟩ : {v // ¬ ∃ w, R v w}) = ⟨t, ht⟩ :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val heq
  
/-- A finite directed map with missing edges and an acyclic orientation has a
source and a sink among its rotation-cycle vertices. The carrier is nonempty
because it contains its distinguished outer dart. Helper toward Definition -/
theorem DirectedMapWithMissing.exists_source_and_sink {D : Type*}
    [Fintype D] [DecidableEq D] (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) :
    (∃ v : CombinatorialMap.VertexQuotient M.toCombinatorialMap,
      ¬ ∃ u, M.directedStep u v) ∧
    (∃ v : CombinatorialMap.VertexQuotient M.toCombinatorialMap,
      ¬ ∃ w, M.directedStep v w) := by
  classical
  letI : Nonempty (CombinatorialMap.VertexQuotient M.toCombinatorialMap) :=
    ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid M.rot) M.outer⟩
  exact DirectedDistances.PlanarMap.exists_source_and_sink
    (M.directedStep) hM

end DirectedDistances.PlanarMap
