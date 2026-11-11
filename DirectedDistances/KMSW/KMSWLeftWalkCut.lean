module

public import DirectedDistances.KMSW.FiniteWalkClass

/-! # Cutting a prescribed initial down-step segment

characterization is asserted here. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

/-- PROCEDURE READING: Definition 3.3 increments (−1,0), (0,1), (1,−1) -/
@[expose] def KMSWLeftWalkAdmissible (ℓ n : ℕ) (c : Fin n → Fin 3) : Prop :=
  ((ℓ : ℤ) - 1, 0) + integrateCodes (finiteCodeExtend (n := n + 1) c) n = (0, 0) ∧
    ∀ k ∈ Finset.range (n + 1),
      0 ≤ (((ℓ : ℤ) - 1, 0) +
        integrateCodes (finiteCodeExtend (n := n + 1) c) k).1 ∧
      0 ≤ (((ℓ : ℤ) - 1, 0) +
        integrateCodes (finiteCodeExtend (n := n + 1) c) k).2

/-- Decidable endpoint and quadrant conditions for the procedure-reading -/
instance instDecidableKMSWLeftWalkAdmissible (ℓ n : ℕ) :
    DecidablePred (KMSWLeftWalkAdmissible ℓ n) := by
  intro c
  unfold KMSWLeftWalkAdmissible
  infer_instance

/-- PROCEDURE READING: Definition 3.3 increments (−1,0), (0,1), (1,−1) -/
@[expose] def KMSWLeftWalkClass (ℓ n : ℕ) :=
  {c : Fin n → Fin 3 // KMSWLeftWalkAdmissible ℓ n c}

/-- Finite enumeration of the procedure-reading walk carrier of -/
instance instFintypeKMSWLeftWalkClass (ℓ n : ℕ) :
    Fintype (KMSWLeftWalkClass ℓ n) := by
  change Fintype {c : Fin n → Fin 3 // KMSWLeftWalkAdmissible ℓ n c}
  infer_instance

/-- Suffix word for the helper toward `lem-kmsw-left` -/
@[expose] def kmswLeftDropCodes {r N : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : Fin (N - 1) → Fin 3) : Fin (N - r) → Fin 3 :=
  fun i => c ⟨r - 1 + i.val, by omega⟩

/-- Prefix insertion for the helper toward `lem-kmsw-left` -/
@[expose] def kmswLeftPrependCodes {r N : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : Fin (N - r) → Fin 3) : Fin (N - 1) → Fin 3 :=
  fun i => if h : i.val < r - 1 then 2 else c ⟨i.val - (r - 1), by omega⟩

/-- Cutting after prefix insertion recovers the word, for the helper toward -/
theorem kmswLeftDrop_prepend {r N : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : Fin (N - r) → Fin 3) :
    kmswLeftDropCodes (r := r) (N := N) hr hrN
      (kmswLeftPrependCodes (r := r) (N := N) hr hrN c) = c := by
  funext i
  simp only [kmswLeftDropCodes, kmswLeftPrependCodes]
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  simp

/-- Prefix insertion after cutting recovers a word with the prescribed prefix, -/
theorem kmswLeftPrepend_drop {r N : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : Fin (N - 1) → Fin 3)
    (hp : ∀ i : Fin (N - 1), i.val < r - 1 → c i = 2) :
    kmswLeftPrependCodes (r := r) (N := N) hr hrN
      (kmswLeftDropCodes (r := r) (N := N) hr hrN c) = c := by
  funext i
  simp only [kmswLeftPrependCodes]
  split_ifs with hi
  · exact (hp i hi).symm
  · simp only [kmswLeftDropCodes]
    congr 1
    apply Fin.ext
    dsimp
    omega

private theorem integrated_succ (c : ℕ → Fin 3) (k : ℕ) :
    integrateCodes c (k + 1) = integrateCodes c k + lazyTwoDimensionalStep (c k) :=
  Finset.sum_range_succ _ _

private theorem integrated_prefix {r N : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : Fin (N - 1) → Fin 3)
    (hp : ∀ i : Fin (N - 1), i.val < r - 1 → c i = 2)
    (k : ℕ) (hk : k ≤ r - 1) :
    integrateCodes (finiteCodeExtend c) k = ((k : ℤ), -(k : ℤ)) := by
  induction k with
  | zero =>
    simp only [integrateCodes, Finset.range_zero, Finset.sum_empty]
    rfl
  | succ k ih =>
    rw [integrated_succ, ih (by omega)]
    have hkN : k < N - 1 := by omega
    have hcode : finiteCodeExtend c k = 2 := by
      simp only [finiteCodeExtend, dite_eq_left hkN]
      exact hp ⟨k, hkN⟩ (show k < r - 1 by omega)
    rw [hcode, lazyTwoDimensionalStep_two]
    apply Prod.ext
    · simp only [Prod.fst_add, Nat.cast_add, Nat.cast_one]
    · simp only [Prod.snd_add, Nat.cast_add, Nat.cast_one]
      omega

private theorem integrated_suffix {r N : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : Fin (N - 1) → Fin 3)
    (hp : ∀ i : Fin (N - 1), i.val < r - 1 → c i = 2)
    (k : ℕ) (hk : k ≤ N - r) :
    integrateCodes (finiteCodeExtend c) (r - 1 + k) =
      (((r : ℤ) - 1), -(r : ℤ) + 1) +
        integrateCodes (finiteCodeExtend (n := N - r + 1)
          (kmswLeftDropCodes (r := r) (N := N) hr hrN c)) k := by
  induction k with
  | zero =>
    rw [Nat.add_zero, integrated_prefix hr hrN c hp (r - 1) le_rfl]
    simp only [integrateCodes, Finset.range_zero, Finset.sum_empty, add_zero]
    have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hcast]
    congr 1; omega
  | succ k ih =>
    rw [show r - 1 + (k + 1) = (r - 1 + k) + 1 by omega,
      integrated_succ, integrated_succ, ih (by omega)]
    have hkN : r - 1 + k < N - 1 := by omega
    have hks : k < N - r + 1 - 1 := by omega
    have hcode : finiteCodeExtend c (r - 1 + k) =
        finiteCodeExtend (n := N - r + 1)
          (kmswLeftDropCodes (r := r) (N := N) hr hrN c) k := by
      simp only [finiteCodeExtend, dite_eq_left hkN, dite_eq_left hks, kmswLeftDropCodes]
    rw [hcode, add_assoc]

/-- Admissibility transfer for the helper toward `lem-kmsw-left`
not the paper result. -/
theorem kmswLeftAdmissible_iff_drop {r N : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : Fin (N - 1) → Fin 3)
    (hp : ∀ i : Fin (N - 1), i.val < r - 1 → c i = 2) :
    KMSWWalkAdmissible 1 r N c ↔
      KMSWLeftWalkAdmissible r (N - r)
        (kmswLeftDropCodes (r := r) (N := N) hr hrN c) := by
  have hlen : r - 1 + (N - r) = N - 1 := by omega
  have hs := integrated_suffix hr hrN c hp
  constructor
  · rintro ⟨hend, hcone⟩
    constructor
    · have he := hs (N - r) le_rfl
      rw [hlen, hend] at he
      apply Prod.ext
      · have := congrArg Prod.fst he
        simp only [Prod.fst_add] at this ⊢
        omega
      · have := congrArg Prod.snd he
        simp only [Prod.snd_add] at this ⊢
        omega
    · intro k hk
      have hk' : k ≤ N - r := by
        have := Finset.mem_range.mp hk
        omega
      have hc := hcone (r - 1 + k) (Finset.mem_range.mpr (by omega))
      rw [hs k hk'] at hc
      simp only [Prod.fst_add, Prod.snd_add] at hc ⊢
      constructor <;> omega
  · rintro ⟨hend, hcone⟩
    constructor
    · have he := hs (N - r) le_rfl
      rw [hlen] at he
      have he1 := congrArg Prod.fst hend
      have he2 := congrArg Prod.snd hend
      apply Prod.ext
      · have := congrArg Prod.fst he
        simp only [Prod.fst_add] at this he1 ⊢
        omega
      · have := congrArg Prod.snd he
        simp only [Prod.snd_add] at this he2 ⊢
        omega
    · intro k hk
      have hk' : k ≤ N - 1 := by
        have := Finset.mem_range.mp hk
        omega
      by_cases hkp : k ≤ r - 1
      · rw [integrated_prefix hr hrN c hp k hkp]
        constructor <;> omega
      · have hks : k - (r - 1) ≤ N - r := by omega
        have hc := hcone (k - (r - 1)) (Finset.mem_range.mpr (by omega))
        have he := hs (k - (r - 1)) hks
        rw [show r - 1 + (k - (r - 1)) = k by omega] at he
        rw [he]
        simp only [Prod.fst_add, Prod.snd_add] at hc ⊢
        constructor <;> omega

/-- prefix of `r - 1` copies of code `2`; the inverse prepends that prefix. -/
@[expose] def kmswLeftWalkCut (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) :
    {c : KMSWWalkClass 1 r N //
      ∀ i : Fin (N - 1), (i : ℕ) < r - 1 → c.val i = 2} ≃
        KMSWLeftWalkClass r (N - r) where
  toFun c := ⟨kmswLeftDropCodes (r := r) (N := N) hr hrN c.val.val,
    (kmswLeftAdmissible_iff_drop hr hrN c.val.val c.property).mp c.val.property⟩
  invFun c := by
    have hp : ∀ i : Fin (N - 1), i.val < r - 1 →
        kmswLeftPrependCodes (r := r) (N := N) hr hrN c.val i = 2 := by
      intro i hi
      simp only [kmswLeftPrependCodes, dite_eq_left hi]
    refine ⟨⟨kmswLeftPrependCodes (r := r) (N := N) hr hrN c.val, ?_⟩, hp⟩
    apply (kmswLeftAdmissible_iff_drop hr hrN _ hp).mpr
    rw [kmswLeftDrop_prepend]
    exact c.property
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact kmswLeftPrepend_drop hr hrN c.val.val c.property
  right_inv c := by
    apply Subtype.ext
    exact kmswLeftDrop_prepend hr hrN c.val

/-- Forward code values for the helper toward `lem-kmsw-left`
not the paper result. -/
@[simp] theorem kmswLeftWalkCut_apply_val (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : {c : KMSWWalkClass 1 r N //
      ∀ i : Fin (N - 1), (i : ℕ) < r - 1 → c.val i = 2}) (i : Fin (N - r)) :
    (kmswLeftWalkCut r N hr hrN c).val i =
      c.val.val ⟨r - 1 + i.val, by omega⟩ := rfl

/-- Inverse prefix values for the helper toward `lem-kmsw-left`
not the paper result. -/
@[simp] theorem kmswLeftWalkCut_symm_val_of_lt (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : KMSWLeftWalkClass r (N - r)) (i : Fin (N - 1)) (hi : i.val < r - 1) :
    ((kmswLeftWalkCut r N hr hrN).symm c).val.val i = 2 := by
  change kmswLeftPrependCodes (r := r) (N := N) hr hrN c.val i = 2
  simp only [kmswLeftPrependCodes, dite_eq_left hi]

/-- Inverse suffix values for the helper toward `lem-kmsw-left`
not the paper result. -/
@[simp] theorem kmswLeftWalkCut_symm_val_of_le (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (c : KMSWLeftWalkClass r (N - r)) (i : Fin (N - 1)) (hi : r - 1 ≤ i.val) :
    ((kmswLeftWalkCut r N hr hrN).symm c).val.val i =
      c.val ⟨i.val - (r - 1), by omega⟩ := by
  change kmswLeftPrependCodes (r := r) (N := N) hr hrN c.val i = _
  simp only [kmswLeftPrependCodes, dite_eq_right (by omega : ¬i.val < r - 1)]

end DirectedDistances.KMSW
