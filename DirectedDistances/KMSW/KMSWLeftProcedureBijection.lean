module

public import DirectedDistances.KMSW.KMSWLeftWalkCut
public import DirectedDistances.KMSW.KMSWProcedureReading
public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier
public import DirectedDistances.PlanarMap.KMSWMapChanneled

/-! # Preparation for the conditional left-endpoint procedure equivalence

not adopted); CONDITIONAL on named inputs; not the paper result.

The prefix characterization in both directions and the boundary-reversal
equivalence are explicit named inputs. The assembly first prepends the forced
prefix, applies the KMSW procedure, and then applies the inverse of the supplied
boundary-reversal equivalence. It proves none of these named inputs.

The intended positive-parameter assembly assumes `hn : 1 ≤ n`, excluding
`n = 0`. The separate zero-step single-edge map `m₀` correspondence is not
formalized here, and no S7-singleton correction is adopted. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Exactly the subtype predicate in `kmswLeftWalkCut`.
not adopted); CONDITIONAL on named inputs; not the paper result. -/
abbrev kmswLeftForcedPrefix {ℓ N : ℕ}
    (c : KMSWWalkClass 1 ℓ N) : Prop :=
  ∀ i : Fin (N - 1), (i : ℕ) < ℓ - 1 → c.val i = 2

/-- The code-cut factor at total size `N = n + ℓ`, transported along
`Nat.add_sub_cancel n ℓ`. This factor does not assert channeling.
not adopted); CONDITIONAL on named inputs; not the paper result. -/
@[expose] def kmswLeftWalkCutAdd (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    {c : KMSWWalkClass 1 ℓ (n + ℓ) // kmswLeftForcedPrefix c} ≃
      KMSWLeftWalkClass ℓ n :=
  (kmswLeftWalkCut ℓ (n + ℓ) hℓ (by omega)).trans
    (Equiv.cast (congrArg (KMSWLeftWalkClass ℓ) (Nat.add_sub_cancel n ℓ)))

/-- Prefix codes of the inverse cut-and-length transport are all `2`.
CONDITIONAL on named inputs; not the paper result. -/
@[simp] theorem kmswLeftWalkCutAdd_symm_val_of_lt (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (w : KMSWLeftWalkClass ℓ n) (i : Fin (n + ℓ - 1)) (hi : i.val < ℓ - 1) :
    ((kmswLeftWalkCutAdd ℓ n hℓ).symm w).val.val i = 2 :=
  ((kmswLeftWalkCutAdd ℓ n hℓ).symm w).property i hi

/-- After the forced prefix, the inverse cut-and-length transport has the original codes.
CONDITIONAL on named inputs; not the paper result. -/
@[simp] theorem kmswLeftWalkCutAdd_symm_val_shift (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (w : KMSWLeftWalkClass ℓ n) (i : Fin n) :
    ((kmswLeftWalkCutAdd ℓ n hℓ).symm w).val.val ⟨ℓ - 1 + i.val, by omega⟩ =
      w.val i := by
  have cast_val {a b : ℕ} (h : a = b) (v : KMSWLeftWalkClass ℓ a) (j : Fin b) :
      ((Equiv.cast (congrArg (KMSWLeftWalkClass ℓ) h)) v).val j =
        v.val ⟨j.val, by omega⟩ := by
    subst b
    rfl
  have h := congrArg (fun v : KMSWLeftWalkClass ℓ n => v.val i)
    ((kmswLeftWalkCutAdd ℓ n hℓ).apply_symm_apply w)
  change ((Equiv.cast (congrArg (KMSWLeftWalkClass ℓ) (Nat.add_sub_cancel n ℓ)))
    (kmswLeftWalkCut ℓ (n + ℓ) hℓ (by omega)
      ((kmswLeftWalkCutAdd ℓ n hℓ).symm w))).val i = w.val i at h
  rw [cast_val (Nat.add_sub_cancel n ℓ)] at h
  exact h

/-- Restrict the procedure equivalence using the two named prefix/channeling inputs.
CONDITIONAL on named inputs; not the paper result. -/
@[expose] noncomputable def kmswPrefixChanneledEquivOf {ℓ N : ℕ} (hN : 1 ≤ N)
    (hA : ∀ c : KMSWWalkClass 1 ℓ N,
      kmswLeftForcedPrefix c → (kmswToMapIsoClass hN c).IsChanneled)
    (hB : ∀ c : KMSWWalkClass 1 ℓ N,
      (kmswToMapIsoClass hN c).IsChanneled → kmswLeftForcedPrefix c) :
    {c : KMSWWalkClass 1 ℓ N // kmswLeftForcedPrefix c} ≃
      {q : KMSWMapIsoClass 1 ℓ N // q.IsChanneled} :=
  Equiv.subtypeEquiv (kmswProcedureEquiv 1 ℓ N hN)
    (fun c => ⟨hA c, hB c⟩)

/-- Forward formula for the restricted procedure equivalence.
CONDITIONAL on named inputs; not the paper result. -/
@[simp] theorem kmswPrefixChanneledEquivOf_apply {ℓ N : ℕ} (hN : 1 ≤ N)
    (hA : ∀ c : KMSWWalkClass 1 ℓ N,
      kmswLeftForcedPrefix c → (kmswToMapIsoClass hN c).IsChanneled)
    (hB : ∀ c : KMSWWalkClass 1 ℓ N,
      (kmswToMapIsoClass hN c).IsChanneled → kmswLeftForcedPrefix c)
    (c : {c : KMSWWalkClass 1 ℓ N // kmswLeftForcedPrefix c}) :
    kmswPrefixChanneledEquivOf hN hA hB c =
      ⟨kmswToMapIsoClass hN c.val, hA c.val c.property⟩ := rfl

/-- Assemble prefix insertion, the restricted procedure, and inverse boundary reversal.
CONDITIONAL on named inputs; not the paper result. -/
@[expose] noncomputable def kmswLeftProcedureEquivOf (ℓ n : ℕ)
    (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n)
    (hA : ∀ c : KMSWWalkClass 1 ℓ (n + ℓ),
      kmswLeftForcedPrefix c → (kmswToMapIsoClass (by omega) c).IsChanneled)
    (hB : ∀ c : KMSWWalkClass 1 ℓ (n + ℓ),
      (kmswToMapIsoClass (by omega) c).IsChanneled → kmswLeftForcedPrefix c)
    (rev : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} ≃
      {q : KMSWMapIsoClass 1 ℓ (n + ℓ) // q.IsChanneled}) :
    KMSWLeftWalkClass ℓ n ≃
      {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
  (kmswLeftWalkCutAdd ℓ n hℓ).symm.trans
    ((kmswPrefixChanneledEquivOf (by omega) hA hB).trans rev.symm)

/-- Forward formula: prepend the forced prefix, run the procedure, and undo `rev`.
CONDITIONAL on named inputs; not the paper result. -/
@[simp] theorem kmswLeftProcedureEquivOf_apply (ℓ n : ℕ)
    (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n)
    (hA : ∀ c : KMSWWalkClass 1 ℓ (n + ℓ),
      kmswLeftForcedPrefix c → (kmswToMapIsoClass (by omega) c).IsChanneled)
    (hB : ∀ c : KMSWWalkClass 1 ℓ (n + ℓ),
      (kmswToMapIsoClass (by omega) c).IsChanneled → kmswLeftForcedPrefix c)
    (rev : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} ≃
      {q : KMSWMapIsoClass 1 ℓ (n + ℓ) // q.IsChanneled})
    (w : KMSWLeftWalkClass ℓ n) :
    kmswLeftProcedureEquivOf ℓ n hℓ hn hA hB rev w =
      rev.symm ⟨kmswToMapIsoClass (by omega) ((kmswLeftWalkCutAdd ℓ n hℓ).symm w).val,
        hA _ ((kmswLeftWalkCutAdd ℓ n hℓ).symm w).property⟩ := rfl

/-- Bijectivity of the conditional assembly.
CONDITIONAL on named inputs; not the paper result. -/
theorem lem_kmsw_left_procedureReading_of (ℓ n : ℕ)
    (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n)
    (hA : ∀ c : KMSWWalkClass 1 ℓ (n + ℓ),
      kmswLeftForcedPrefix c → (kmswToMapIsoClass (by omega) c).IsChanneled)
    (hB : ∀ c : KMSWWalkClass 1 ℓ (n + ℓ),
      (kmswToMapIsoClass (by omega) c).IsChanneled → kmswLeftForcedPrefix c)
    (rev : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} ≃
      {q : KMSWMapIsoClass 1 ℓ (n + ℓ) // q.IsChanneled}) :
    Function.Bijective (fun w => kmswLeftProcedureEquivOf ℓ n hℓ hn hA hB rev w) :=
  (kmswLeftProcedureEquivOf ℓ n hℓ hn hA hB rev).bijective

end DirectedDistances.KMSW
