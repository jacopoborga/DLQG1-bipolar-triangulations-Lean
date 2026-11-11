module

public import DirectedDistances.KMSW.KMSWLeftProcedureUniform
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Function

public section
namespace DirectedDistances.PlanarMap

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] def finiteDirectedMapSetoid :
    Setoid (Σ k : ℕ, DirectedMapWithMissing (Fin k)) where
  r M N := Nonempty (DirectedMapWithMissingIso M.2 N.2)
  iseqv := by
    constructor
    · intro M
      exact ⟨DirectedMapWithMissingIso.refl M.2⟩
    · intro M N h
      exact h.elim fun I => ⟨I.symm⟩
    · intro M N P h₁ h₂
      exact h₁.elim fun I => h₂.elim fun J => ⟨I.trans J⟩

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] def FiniteDirectedMapClass : Type := Quotient finiteDirectedMapSetoid

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] def DirectedMapWithMissing.transportIso {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (M : DirectedMapWithMissing D) (e : D ≃ E) :
    DirectedMapWithMissingIso M (M.transport e) where
  toEquiv := e
  rot_comm := by
    intro d
    simp only [DirectedMapWithMissing.transport, CombinatorialMap.transport,
      transportPerm_apply, Equiv.symm_apply_apply]
  edgeInv_comm := by
    intro d
    simp only [DirectedMapWithMissing.transport, CombinatorialMap.transport,
      transportPerm_apply, Equiv.symm_apply_apply]
  missing_iff := by
    intro d
    simp only [DirectedMapWithMissing.transport, Equiv.symm_apply_apply]
  tail_iff := by
    intro d
    simp only [DirectedMapWithMissing.transport, Equiv.symm_apply_apply]
  outer_iff := by
    intro d
    have hf : (M.transport e).toCombinatorialMap.faceSucc =
        transportPerm e M.toCombinatorialMap.faceSucc := by
      ext x
      simp [DirectedMapWithMissing.transport, CombinatorialMap.transport,
        CombinatorialMap.faceSucc, transportPerm, Equiv.Perm.mul_apply]
    change Equiv.Perm.SameCycle (M.transport e).toCombinatorialMap.faceSucc
      (e M.outer) (e d) ↔ Equiv.Perm.SameCycle M.toCombinatorialMap.faceSucc M.outer d
    rw [hf]
    exact sameCycle_transport_iff e M.toCombinatorialMap.faceSucc M.outer d

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] noncomputable def DirectedMapWithMissing.toClass {D : Type*}
    [Fintype D] [DecidableEq D] (M : DirectedMapWithMissing D) :
    FiniteDirectedMapClass :=
  Quotient.mk finiteDirectedMapSetoid
    ⟨Fintype.card D, M.transport (Fintype.equivFin D)⟩

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
theorem DirectedMapWithMissing.toClass_eq_toClass_iff {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (M : DirectedMapWithMissing D) (N : DirectedMapWithMissing E) :
    M.toClass = N.toClass ↔ Nonempty (DirectedMapWithMissingIso M N) := by
  constructor
  · intro h
    obtain ⟨I⟩ := Quotient.exact h
    exact ⟨(M.transportIso (Fintype.equivFin D)).trans
      (I.trans (N.transportIso (Fintype.equivFin E)).symm)⟩
  · rintro ⟨I⟩
    exact Quotient.sound ⟨(M.transportIso (Fintype.equivFin D)).symm.trans
      (I.trans (N.transportIso (Fintype.equivFin E)))⟩

end DirectedDistances.PlanarMap

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] noncomputable def kmswLeftProcedureClass (ℓ n : ℕ)
    (c : KMSWLeftWalkClass ℓ n) : FiniteDirectedMapClass :=
  (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n).toClass

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] noncomputable def decoratedClass {ℓ n : ℕ}
    (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}) :
    FiniteDirectedMapClass := q.val.out.partialMap.toClass

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
theorem decoratedClass_injective (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    Function.Injective (decoratedClass (ℓ := ℓ) (n := n)) := by
  intro q q' h
  have hI := (DirectedMapWithMissing.toClass_eq_toClass_iff
    q.val.out.partialMap q'.val.out.partialMap).mp h
  apply Subtype.ext
  have hmk : KMSWMapIsoClass.mk q.val.out = KMSWMapIsoClass.mk q'.val.out := by
    by_cases h : ℓ = 1
    · subst ℓ
      exact (KMSWMapRep.mk_eq_mk_iff_partialMapIso_one _ _).mpr hI
    · exact (KMSWMapRep.mk_eq_mk_iff_partialMapIso (by omega) _ _).mpr hI
  exact (Quotient.out_eq q.val).symm.trans (hmk.trans (Quotient.out_eq q'.val))

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] noncomputable def decoratedClassEquivRange (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} ≃
      Set.range (decoratedClass (ℓ := ℓ) (n := n)) :=
  Equiv.ofBijective (fun q => ⟨decoratedClass q, ⟨q, rfl⟩⟩) (by
    constructor
    · intro q q' h
      exact decoratedClass_injective ℓ n hℓ (congrArg Subtype.val h)
    · rintro ⟨x, q, rfl⟩
      exact ⟨q, rfl⟩)

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
theorem kmswLeftProcedureClass_injective_range (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (hn : 1 ≤ n) :
    Function.Injective (kmswLeftProcedureClass ℓ n) ∧
      Set.range (kmswLeftProcedureClass ℓ n) =
        Set.range (decoratedClass (ℓ := ℓ) (n := n)) := by
  obtain ⟨F, hF, _⟩ := lem_kmsw_left_procedureReading_uniform ℓ n hℓ hn
  have hcoinc (c : KMSWLeftWalkClass ℓ n) :
      kmswLeftProcedureClass ℓ n c = decoratedClass (F c) :=
    ((DirectedMapWithMissing.toClass_eq_toClass_iff _ _).mpr (hF c)).symm
  constructor
  · intro c c' h
    apply F.injective
    apply decoratedClass_injective ℓ n hℓ
    exact (hcoinc c).symm.trans (h.trans (hcoinc c'))
  · apply Set.ext
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨F c, (hcoinc c).symm⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨c, rfl⟩ := F.surjective q
      exact ⟨c, hcoinc c⟩

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
theorem kmswLeftProcedureClass_bijOn (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    Set.BijOn (kmswLeftProcedureClass ℓ n) Set.univ
      (Set.range (decoratedClass (ℓ := ℓ) (n := n))) := by
  obtain ⟨hinj, hrange⟩ := kmswLeftProcedureClass_injective_range ℓ n hℓ hn
  refine ⟨?_, ?_, ?_⟩
  · intro c _
    rw [← hrange]
    exact ⟨c, rfl⟩
  · intro c _ c' _ h
    exact hinj h
  · intro x hx
    rw [← hrange] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, Set.mem_univ c, rfl⟩

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
@[expose] noncomputable def kmswLeftProcedureCorestrict (ℓ n : ℕ)
    (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) (c : KMSWLeftWalkClass ℓ n) :
    {x : FiniteDirectedMapClass //
      ∃ q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}, decoratedClass q = x} :=
  ⟨kmswLeftProcedureClass ℓ n c,
    (kmswLeftProcedureClass_bijOn ℓ n hℓ hn).mapsTo (Set.mem_univ c)⟩

/-- literal-function form of the procedure-reading bijection; legal-step convention, S7-count, -/
theorem kmswLeftProcedureCorestrict_bijective (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (hn : 1 ≤ n) :
    Function.Bijective (kmswLeftProcedureCorestrict ℓ n hℓ hn) := by
  obtain ⟨hinj, hrange⟩ := kmswLeftProcedureClass_injective_range ℓ n hℓ hn
  constructor
  · intro c c' h
    exact hinj (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈ Set.range (kmswLeftProcedureClass ℓ n) := by
      rw [hrange]
      exact x.property
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, Subtype.ext hc⟩

end DirectedDistances.KMSW
