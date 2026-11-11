/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.MeasurableSpace.Instances








public section
namespace DirectedDistances.RandomWalk
open MeasureTheory



@[expose] def finiteTimeIndex {Ω : Type*} (T : Ω → WithTop ℕ)
    (ω : {ω // T ω < ⊤}) : ℕ :=
  (T ω.val).untop (ne_of_lt ω.property)

/-- The extracted natural index has exactly the supplied finite value. -/
theorem coe_finiteTimeIndex {Ω : Type*} (T : Ω → WithTop ℕ)
    (ω : {ω // T ω < ⊤}) : (finiteTimeIndex T ω : WithTop ℕ) = T ω.val := by
  exact WithTop.coe_untop _ _

/-- Exact finite-time fibers, retaining the supplied extended time. -/
theorem finiteTimeIndex_eq_iff {Ω : Type*} (T : Ω → WithTop ℕ)
    (ω : {ω // T ω < ⊤}) (n : ℕ) :
    finiteTimeIndex T ω = n ↔ T ω.val = (n : WithTop ℕ) := by
  constructor
  · intro h
    rw [← coe_finiteTimeIndex T ω, h]
  · intro h
    exact WithTop.coe_injective ((coe_finiteTimeIndex T ω).trans h)

/-- The finite event is exactly the union of the actual finite fibers. -/
theorem finiteTime_event_eq_iUnion {Ω : Type*} (T : Ω → WithTop ℕ) :
    {ω | T ω < ⊤} = ⋃ n : ℕ, {ω | T ω = (n : WithTop ℕ)} := by
  ext ω
  constructor
  · intro h
    exact Set.mem_iUnion.mpr ⟨finiteTimeIndex T ⟨ω, h⟩,
      (coe_finiteTimeIndex T ⟨ω, h⟩).symm⟩
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    change T ω < ⊤
    rw [hn]
    exact WithTop.coe_lt_top n

/-- Finite-index extraction is measurable on the genuine finite event. -/
theorem measurable_finiteTimeIndex {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → WithTop ℕ) (hT : Measurable T) : Measurable (finiteTimeIndex T) := by
  let e : {t : WithTop ℕ // t < ⊤} → ℕ := fun t => t.val.untop (ne_of_lt t.property)
  exact (measurable_of_countable e).comp
    ((hT.comp measurable_subtype_coe).subtype_mk (h := fun ω => ω.property))

/-- Full finite vector history, retaining the time as a dependent tag. -/
@[expose] def stoppedVectorHistory {Ω : Type*} (r : Ω → ℕ)
    (X : Ω → ℕ → ℤ × ℤ) (ω : Ω) : Σ n : ℕ, Fin (n + 1) → ℤ × ℤ :=
  ⟨r ω, fun j => X ω j.val⟩

/-- Entire vector future shifted by the actual vector endpoint. -/
@[expose] def stoppedVectorFuture {Ω : Type*} (r : Ω → ℕ)
    (X : Ω → ℕ → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ :=
  fun k => X ω (r ω + k) - X ω (r ω)

/-- On a specified natural-time slice the dependent history is the literal
full prefix, including the final vector endpoint. -/
theorem stoppedVectorHistory_eq_of_time {Ω : Type*} (r : Ω → ℕ)
    (X : Ω → ℕ → ℤ × ℤ) (ω : Ω) (n : ℕ) (h : r ω = n) :
    stoppedVectorHistory r X ω =
      (⟨n, fun j : Fin (n + 1) => X ω j.val⟩ :
        Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) := by
  subst n
  rfl

/-- On a specified natural-time slice the whole future uses the actual
vector endpoint at that time. -/
theorem stoppedVectorFuture_eq_of_time {Ω : Type*} (r : Ω → ℕ)
    (X : Ω → ℕ → ℤ × ℤ) (ω : Ω) (n : ℕ) (h : r ω = n) :
    stoppedVectorFuture r X ω = (fun k => X ω (n + k) - X ω n) := by
  subst n
  rfl

private theorem measurable_sigma_mk_history (n : ℕ) :
    Measurable (Sigma.mk (β := fun n : ℕ => Fin (n + 1) → ℤ × ℤ) n : (Fin (n + 1) → ℤ × ℤ) →
      Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) :=
  Measurable.of_le_map (iInf_le _ n)

/-- The dependent entire-prefix history is measurable for every measurable
natural time and every measurable vector path. -/
theorem measurable_stoppedVectorHistory {Ω : Type*} [MeasurableSpace Ω]
    (r : Ω → ℕ) (X : Ω → ℕ → ℤ × ℤ)
    (hr : Measurable r) (hX : Measurable X) : Measurable (stoppedVectorHistory r X) := by
  intro s hs
  have hset : stoppedVectorHistory r X ⁻¹' s =
      ⋃ n : ℕ, {ω | r ω = n} ∩
        (fun ω => fun j : Fin (n + 1) => X ω j.val) ⁻¹' (Sigma.mk (β := fun n : ℕ => Fin (n + 1) → ℤ × ℤ) n ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨r ω, rfl, h⟩
    · rintro ⟨n, hn, h⟩
      subst n
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun n => (hr (measurableSet_singleton n)).inter
    ((Measurable.of_eval fun j : Fin (n + 1) => (measurable_pi_apply j.val).comp hX)
      ((measurable_sigma_mk_history n) hs))

/-- Both coordinates of the entire shifted future are measurable. -/
theorem measurable_stoppedVectorFuture {Ω : Type*} [MeasurableSpace Ω]
    (r : Ω → ℕ) (X : Ω → ℕ → ℤ × ℤ)
    (hr : Measurable r) (hX : Measurable X) : Measurable (stoppedVectorFuture r X) := by
  have heval : Measurable (fun q : (ℕ → ℤ × ℤ) × ℕ => q.1 q.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  apply Measurable.of_eval
  intro k
  exact (heval.comp (hX.prodMk (hr.add_const k))).sub
    (heval.comp (hX.prodMk hr))

/-- The actual whole dependent history on the finite-time subtype is measurable. -/
theorem measurable_finiteTime_vectorHistory {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → WithTop ℕ) (X : Ω → ℕ → ℤ × ℤ)
    (hT : Measurable T) (hX : Measurable X) :
    Measurable (stoppedVectorHistory (finiteTimeIndex T)
      (fun ω : {ω // T ω < ⊤} => X ω.val)) :=
  measurable_stoppedVectorHistory _ _ (measurable_finiteTimeIndex T hT)
    (hX.comp measurable_subtype_coe)

/-- The actual whole shifted vector future on the finite-time subtype is measurable. -/
theorem measurable_finiteTime_vectorFuture {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → WithTop ℕ) (X : Ω → ℕ → ℤ × ℤ)
    (hT : Measurable T) (hX : Measurable X) :
    Measurable (stoppedVectorFuture (finiteTimeIndex T)
      (fun ω : {ω // T ω < ⊤} => X ω.val)) :=
  measurable_stoppedVectorFuture _ _ (measurable_finiteTimeIndex T hT)
    (hX.comp measurable_subtype_coe)

/-- Every measurable test of a tagged history, on its fixed-time component,
is measurable in exactly the whole finite-prefix sigma algebra. -/
theorem measurableSet_history_test_prefix_comap
    (H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) (hH : MeasurableSet H) (n : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) inferInstance]
      {p | (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
        Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H} := by
  apply MeasurableSpace.measurableSet_comap.mpr
  exact ⟨Sigma.mk (β := fun n : ℕ => Fin (n + 1) → ℤ × ℤ) n ⁻¹' H, measurable_sigma_mk_history n hH, rfl⟩

end DirectedDistances.RandomWalk
