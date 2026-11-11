module

public import DirectedDistances.PlanarMap.CombinatorialMap

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.PlanarMap

open Equiv

variable {α : Type*} [DecidableEq α]

/-- The least positive time at which the orbit of `x` under `σ` returns to `S`.
Helper toward `prop-disk-bs-conv` (Proposition 5.16, -/
@[expose] noncomputable def cyclicFirstReturnTime (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) (x : S) : ℕ :=
  Nat.find (hper x)

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
is positive, returns to `S`, and has no earlier positive return. -/
theorem cyclicFirstReturnTime_spec (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) (x : S) :
    0 < cyclicFirstReturnTime σ S hper x ∧
      (σ ^ cyclicFirstReturnTime σ S hper x) x.1 ∈ S ∧
      ∀ j : ℕ, 0 < j → j < cyclicFirstReturnTime σ S hper x →
        (σ ^ j) x.1 ∉ S := by
  unfold cyclicFirstReturnTime
  have hs := Nat.find_spec (hper x)
  refine ⟨hs.1, hs.2, ?_⟩
  intro j hj hjk hjS
  exact Nat.find_min (hper x) hjk ⟨hj, hjS⟩

/-- Advance to the next point of a finite subset along the cycles of `σ`.
Helper toward `prop-disk-bs-conv` (Proposition 5.16, -/
@[expose] noncomputable def cyclicFirstReturn (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) : Equiv.Perm S := by
  classical
  let f : S → S := fun x =>
    ⟨(σ ^ cyclicFirstReturnTime σ S hper x) x.1,
      (cyclicFirstReturnTime_spec σ S hper x).2.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    let k := cyclicFirstReturnTime σ S hper x
    let l := cyclicFirstReturnTime σ S hper y
    have hk := cyclicFirstReturnTime_spec σ S hper x
    have hl := cyclicFirstReturnTime_spec σ S hper y
    change (σ ^ k) x.1 = (σ ^ l) y.1 at hv
    by_cases hkl : k < l
    · have hsum : k + (l - k) = l := Nat.add_sub_of_le hkl.le
      have heq : x.1 = (σ ^ (l - k)) y.1 := by
        apply (σ ^ k).injective
        calc
          (σ ^ k) x.1 = (σ ^ l) y.1 := hv
          _ = (σ ^ (k + (l - k))) y.1 := by rw [hsum]
          _ = (σ ^ k) ((σ ^ (l - k)) y.1) := by simp [pow_add]
      have hpos : 0 < l - k := Nat.sub_pos_of_lt hkl
      have hlt : l - k < l := by omega
      have hret : (σ ^ (l - k)) y.1 ∈ S := heq ▸ x.2
      exact (hl.2.2 (l - k) hpos hlt hret).elim
    · by_cases hlk : l < k
      · have hsum : l + (k - l) = k := Nat.add_sub_of_le hlk.le
        have heq : y.1 = (σ ^ (k - l)) x.1 := by
          apply (σ ^ l).injective
          calc
            (σ ^ l) y.1 = (σ ^ k) x.1 := hv.symm
            _ = (σ ^ (l + (k - l))) x.1 := by rw [hsum]
            _ = (σ ^ l) ((σ ^ (k - l)) x.1) := by simp [pow_add]
        have hpos : 0 < k - l := Nat.sub_pos_of_lt hlk
        have hlt : k - l < k := by omega
        have hret : (σ ^ (k - l)) x.1 ∈ S := heq ▸ y.2
        exact (hk.2.2 (k - l) hpos hlt hret).elim
      · have hkl' : k = l := by omega
        have hv' : (σ ^ k) x.1 = (σ ^ k) y.1 := by
          simpa [k, l, hkl'] using hv
        apply Subtype.ext
        exact (σ ^ k).injective hv'
  letI : Fintype S := Fintype.ofFinite S
  exact Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
`cyclicFirstReturn` is the least positive iterate of `σ` returning to `S`. -/
theorem firstReturn_spec (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) (x : S) :
    (cyclicFirstReturn σ S hper x).1 =
        (σ ^ cyclicFirstReturnTime σ S hper x) x.1 ∧
      0 < cyclicFirstReturnTime σ S hper x ∧
      (σ ^ cyclicFirstReturnTime σ S hper x) x.1 ∈ S ∧
      ∀ j : ℕ, 0 < j → j < cyclicFirstReturnTime σ S hper x →
        (σ ^ j) x.1 ∉ S := by
  exact ⟨rfl, cyclicFirstReturnTime_spec σ S hper x⟩

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
return lie in the same ambient rotation cycle. -/
theorem firstReturn_sameCycle (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) (x : S) :
    σ.SameCycle x.1 (cyclicFirstReturn σ S hper x).1 := by
  refine ⟨(cyclicFirstReturnTime σ S hper x : ℕ), ?_⟩
  exact (firstReturn_spec σ S hper x).1.symm

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
invariant under `σ`, first return agrees with the restricted successor. -/
theorem firstReturn_eq_next_of_mem (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hσS : ∀ x : α, x ∈ S → σ x ∈ S) (x : S) :
    (cyclicFirstReturn σ S hper x).1 = σ x.1 := by
  have hret : σ x.1 ∈ S := hσS x.1 x.2
  have hk := (cyclicFirstReturnTime_spec σ S hper x).1
  by_contra hne
  have htime : cyclicFirstReturnTime σ S hper x ≠ 1 := by
    intro heq
    apply hne
    simpa [heq] using (firstReturn_spec σ S hper x).1
  have htwo : 1 < cyclicFirstReturnTime σ S hper x := by omega
  exact (cyclicFirstReturnTime_spec σ S hper x).2.2 1 Nat.one_pos htwo hret

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
restricted successor follows a forward iterate of `σ`. -/
theorem firstReturn_iterate_repr (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) (x : S) :
    ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
      ((cyclicFirstReturn σ S hper ^ n) x).1 = (σ ^ k) x.1 := by
  let R := cyclicFirstReturn σ S hper
  intro n
  induction n with
  | zero => exact ⟨0, Nat.zero_le _, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk, hval⟩ := ih
    let z : S := (R ^ n) x
    let l := cyclicFirstReturnTime σ S hper z
    have hl := cyclicFirstReturnTime_spec σ S hper z
    refine ⟨l + k, ?_, ?_⟩
    · have hpos : 0 < l := hl.1
      omega
    · change ((R ^ (n + 1)) x).1 = _
      rw [pow_succ']
      change (R z).1 = _
      rw [(firstReturn_spec σ S hper z).1, hval]
      rw [pow_add]
      rfl

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
return to `S` occurs after some positive number of restricted steps. -/
theorem firstReturn_reaches_iterate (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) (x : S)
    (q : ℕ) (hqS : (σ ^ q) x.1 ∈ S) :
    ∃ n : ℕ, ((cyclicFirstReturn σ S hper ^ n) x).1 = (σ ^ q) x.1 := by
  induction q using Nat.strong_induction_on generalizing x with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst q
      exact ⟨0, rfl⟩
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      let k := cyclicFirstReturnTime σ S hper x
      have hkpos := (cyclicFirstReturnTime_spec σ S hper x).1
      have hk_le : k ≤ q := Nat.find_min' (hper x) ⟨hqpos, hqS⟩
      by_cases hkq : k = q
      · refine ⟨1, ?_⟩
        have hval := (firstReturn_spec σ S hper x).1
        simp only [pow_one]
        simpa [k, hkq] using hval
      · have hklt : k < q := Nat.lt_of_le_of_ne hk_le hkq
        let r := q - k
        have hrpos : 0 < r := Nat.sub_pos_of_lt hklt
        have hrlt : r < q := by dsimp [r]; omega
        have hsum : r + k = q := by dsimp [r]; omega
        let y : S := cyclicFirstReturn σ S hper x
        have hyval : y.1 = (σ ^ k) x.1 := (firstReturn_spec σ S hper x).1
        have hrem : (σ ^ r) y.1 = (σ ^ q) x.1 := by
          rw [hyval]
          calc
            (σ ^ r) ((σ ^ k) x.1) = (σ ^ (r + k)) x.1 := by
              rw [pow_add]
              rfl
            _ = (σ ^ q) x.1 := by rw [hsum]
        have hremS : (σ ^ r) y.1 ∈ S := hrem ▸ hqS
        obtain ⟨n, hn⟩ := ih r hrlt y hremS
        refine ⟨n + 1, ?_⟩
        calc
          ((cyclicFirstReturn σ S hper ^ (n + 1)) x).1 =
              ((cyclicFirstReturn σ S hper ^ n) y).1 := by
                simp [y, pow_succ, Equiv.Perm.mul_apply]
          _ = (σ ^ r) y.1 := by
            exact hn
          _ = (σ ^ q) x.1 := hrem

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
first-return path at successive returns to `S`. -/
theorem firstReturn_reaches_first (σ : Equiv.Perm α) (S T : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hTS : ∀ x, x ∈ T → x ∈ S) (x : S) (q : ℕ) (hqpos : 0 < q)
    (hqT : (σ ^ q) x.1 ∈ T)
    (hqmin : ∀ j : ℕ, 0 < j → j < q → (σ ^ j) x.1 ∉ T) :
    ∃ n : ℕ, 0 < n ∧
      ((cyclicFirstReturn σ S hper ^ n) x).1 = (σ ^ q) x.1 ∧
      ∀ m : ℕ, 0 < m → m < n →
        ((cyclicFirstReturn σ S hper ^ m) x).1 ∉ T := by
  have aux : ∀ q : ℕ, 0 < q → ∀ x : S, (σ ^ q) x.1 ∈ T →
      (∀ j : ℕ, 0 < j → j < q → (σ ^ j) x.1 ∉ T) →
        ∃ n : ℕ, 0 < n ∧
          ((cyclicFirstReturn σ S hper ^ n) x).1 = (σ ^ q) x.1 ∧
          ∀ m : ℕ, 0 < m → m < n →
            ((cyclicFirstReturn σ S hper ^ m) x).1 ∉ T := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hqpos x hqT hqmin
      let k := cyclicFirstReturnTime σ S hper x
      have hkpos := (cyclicFirstReturnTime_spec σ S hper x).1
      have hqS : (σ ^ q) x.1 ∈ S := hTS _ hqT
      have hk_le : k ≤ q := Nat.find_min' (hper x) ⟨hqpos, hqS⟩
      by_cases hkq : k = q
      · refine ⟨1, Nat.one_pos, ?_, ?_⟩
        · simpa [k, hkq] using (firstReturn_spec σ S hper x).1
        · intro m hm hmn
          omega
      · have hklt : k < q := Nat.lt_of_le_of_ne hk_le hkq
        let r := q - k
        have hrpos : 0 < r := Nat.sub_pos_of_lt hklt
        have hrlt : r < q := by dsimp [r]; omega
        have hsum : r + k = q := by dsimp [r]; omega
        let y : S := cyclicFirstReturn σ S hper x
        have hyval : y.1 = (σ ^ k) x.1 := (firstReturn_spec σ S hper x).1
        have hy_notT : y.1 ∉ T := by
          rw [hyval]
          exact hqmin k hkpos hklt
        have hrem : (σ ^ r) y.1 = (σ ^ q) x.1 := by
          rw [hyval]
          calc
            (σ ^ r) ((σ ^ k) x.1) = (σ ^ (r + k)) x.1 := by
              rw [pow_add]
              rfl
            _ = (σ ^ q) x.1 := by rw [hsum]
        have hremT : (σ ^ r) y.1 ∈ T := hrem ▸ hqT
        have hremmin : ∀ j : ℕ, 0 < j → j < r → (σ ^ j) y.1 ∉ T := by
          intro j hj hjr hjT
          have hshift : (σ ^ j) y.1 = (σ ^ (j + k)) x.1 := by
            rw [hyval, pow_add]
            rfl
          have hjq : j + k < q := by dsimp [r] at hjr; omega
          exact hqmin (j + k) (by omega) hjq (hshift ▸ hjT)
        obtain ⟨n, hnpos, hneq, hno⟩ := ih r hrlt hrpos y hremT hremmin
        refine ⟨n + 1, by omega, ?_, ?_⟩
        · calc
            ((cyclicFirstReturn σ S hper ^ (n + 1)) x).1 =
                ((cyclicFirstReturn σ S hper ^ n) y).1 := by
                  simp [y, pow_succ, Equiv.Perm.mul_apply]
            _ = (σ ^ r) y.1 := hneq
            _ = (σ ^ q) x.1 := hrem
        · intro m hm hmn
          by_cases hmone : m = 1
          · subst m
            simpa [pow_one, y] using hy_notT
          · have hjpos : 0 < m - 1 := by omega
            have hjlt : m - 1 < n := by omega
            have hmval : m = (m - 1) + 1 := by omega
            have heq : ((cyclicFirstReturn σ S hper ^ m) x).1 =
                ((cyclicFirstReturn σ S hper ^ (m - 1)) y).1 := by
              rw [hmval, pow_succ, Equiv.Perm.mul_apply]
              rfl
            intro hmT
            exact hno (m - 1) hjpos hjlt (heq ▸ hmT)
  exact aux q hqpos x hqT hqmin

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16, -/
@[expose] noncomputable def firstReturnSubset (S T : Finset α) : Finset S := by
  classical
  exact Finset.univ.filter fun x : S => x.1 ∈ T

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
has a positive return to every finite subset. -/
theorem finitePermutationReturn
    {β : Type*} [DecidableEq β] (τ : Equiv.Perm β) [Finite β] (U : Finset β) :
    ∀ x : U, ∃ k : ℕ, 0 < k ∧ (τ ^ k) x.1 ∈ U := by
  intro x
  exact ⟨orderOf τ, orderOf_pos τ, by rw [pow_orderOf_eq_one]; exact x.2⟩

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
positive ambient return times from `S`. -/
theorem firstReturn_has_period_on_subset (σ : Equiv.Perm α) (S T : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hTS : ∀ x, x ∈ T → x ∈ S) :
    ∀ x : T, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ T := by
  classical
  let R := cyclicFirstReturn σ S hper
  intro x
  let xS : S := ⟨x.1, hTS x.1 x.2⟩
  obtain ⟨k, hk, hrepr⟩ := firstReturn_iterate_repr σ S hper xS (orderOf R)
  have hpow : (R ^ orderOf R) xS = xS := by simp [pow_orderOf_eq_one]
  have hreturn : (σ ^ k) xS.1 = xS.1 := by
    calc
      (σ ^ k) xS.1 = ((R ^ orderOf R) xS).1 := hrepr.symm
      _ = xS.1 := congrArg Subtype.val hpow
  refine ⟨k, lt_of_lt_of_le (orderOf_pos R) hk, ?_⟩
  rw [hreturn]
  exact x.2

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
`S` and then to `T ⊆ S` agrees pointwise with restricting directly to `T`. -/
theorem firstReturn_nested (σ : Equiv.Perm α) (S T : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hTS : ∀ x, x ∈ T → x ∈ S) (x : T) :
    let R := cyclicFirstReturn σ S hper
    let U := firstReturnSubset S T
    let hperT := firstReturn_has_period_on_subset σ S T hper hTS
    ((cyclicFirstReturn R U (finitePermutationReturn R U)
      ⟨⟨x.1, hTS x.1 x.2⟩, by simp [U, firstReturnSubset]⟩).1).1 =
      (cyclicFirstReturn σ T hperT x).1 := by
  classical
  let R := cyclicFirstReturn σ S hper
  let U := firstReturnSubset S T
  let xS : S := ⟨x.1, hTS x.1 x.2⟩
  have hxU : xS ∈ U := by simp [U, firstReturnSubset, xS, x.2]
  let xU : U := ⟨xS, hxU⟩
  let hperU := finitePermutationReturn R U
  let hperT := firstReturn_has_period_on_subset σ S T hper hTS
  let q := cyclicFirstReturnTime σ T hperT x
  have hdirect := firstReturn_spec σ T hperT x
  obtain ⟨n, hnpos, hreach, hno⟩ :=
    firstReturn_reaches_first σ S T hper hTS xS q hdirect.2.1
      hdirect.2.2.1 hdirect.2.2.2
  have hreachT : ((R ^ n) xS).1 ∈ T := by
    rw [hreach]
    exact hdirect.2.2.1
  have hreachU : (R ^ n) xS ∈ U := by
    simpa [U, firstReturnSubset] using hreachT
  have htime_le : cyclicFirstReturnTime R U hperU xU ≤ n :=
    Nat.find_min' (hperU xU) ⟨hnpos, hreachU⟩
  have htime_eq : cyclicFirstReturnTime R U hperU xU = n := by
    apply le_antisymm htime_le
    by_contra hlt
    have hlt' : cyclicFirstReturnTime R U hperU xU < n := by omega
    have hspec := cyclicFirstReturnTime_spec R U hperU xU
    have htime_pos := hspec.1
    have htime_memU : (R ^ cyclicFirstReturnTime R U hperU xU) xS ∈ U := hspec.2.1
    have htime_mem : ((R ^ cyclicFirstReturnTime R U hperU xU) xS).1 ∈ T := by
      simpa [U, firstReturnSubset] using htime_memU
    exact hno _ htime_pos hlt' htime_mem
  have hnested := (firstReturn_spec R U hperU xU).1
  rw [htime_eq] at hnested
  calc
    ((cyclicFirstReturn R U hperU xU).1).1 = ((R ^ n) xS).1 :=
      congrArg Subtype.val hnested
    _ = (σ ^ q) xS.1 := hreach
    _ = (cyclicFirstReturn σ T hperT x).1 := hdirect.1.symm

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
identity is independent of the chosen positive-return proofs. -/
theorem firstReturn_nested' (σ : Equiv.Perm α) (S T : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hTS : ∀ x, x ∈ T → x ∈ S) :
    let R := cyclicFirstReturn σ S hper
    let U := firstReturnSubset S T
    ∀ (hperU : ∀ x : U, ∃ k : ℕ, 0 < k ∧ (R ^ k) x.1 ∈ U)
      (hperT : ∀ x : T, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ T) (x : T),
      let xS : S := ⟨x.1, hTS x.1 x.2⟩
      let xU : U := ⟨xS, by simp [U, firstReturnSubset, xS, x.2]⟩
      ((cyclicFirstReturn R U hperU xU).1).1 = (cyclicFirstReturn σ T hperT x).1 := by
  classical
  intro R U hperU hperT x
  let xS : S := ⟨x.1, hTS x.1 x.2⟩
  have hxU : xS ∈ U := by simp [U, firstReturnSubset, xS, x.2]
  let xU : U := ⟨xS, hxU⟩
  have hperU_eq : hperU = finitePermutationReturn R U := Subsingleton.elim _ _
  have hperT_eq : hperT = firstReturn_has_period_on_subset σ S T hper hTS :=
    Subsingleton.elim _ _
  cases hperU_eq
  cases hperT_eq
  have h := firstReturn_nested σ S T hper hTS x
  change ((cyclicFirstReturn R U (finitePermutationReturn R U) xU).1).1 =
    (cyclicFirstReturn σ T (firstReturn_has_period_on_subset σ S T hper hTS) x).1 at h
  exact h

omit [DecidableEq α] in
/-- not a paper result. -/
private theorem sameCycle_nat_pow_of_period (σ : Equiv.Perm α) (x y : α)
    (p : ℕ) (hp : 0 < p) (hperiod : (σ ^ p) x = x)
    (hxy : σ.SameCycle x y) : ∃ q : ℕ, (σ ^ q) x = y := by
  rcases hxy with ⟨i, hi⟩
  let r : ℤ := i % (p : ℤ)
  have hpz : ∀ z : ℤ, (σ ^ ((p : ℤ) * z)) x = x := by
    intro z
    have hfix : Function.IsFixedPt (σ ^ p) x := hperiod
    calc
      (σ ^ ((p : ℤ) * z)) x = ((σ ^ (p : ℤ)) ^ z) x := by rw [zpow_mul]
      _ = ((σ ^ p) ^ z) x := by simp
      _ = x := (hfix.perm_zpow z).eq
  have hdecomp : r + (p : ℤ) * (i / (p : ℤ)) = i := by
    dsimp [r]
    exact Int.emod_add_mul_ediv i (p : ℤ)
  have hreduce : (σ ^ i) x = (σ ^ r) x := by
    rw [← hdecomp, zpow_add, Equiv.Perm.mul_apply, hpz]
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have hnatEq : (σ ^ r.toNat) x = (σ ^ r) x := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hrnonneg]
  refine ⟨r.toNat, ?_⟩
  calc
    (σ ^ r.toNat) x = (σ ^ r) x := hnatEq
    _ = (σ ^ i) x := hreduce.symm
    _ = y := hi

/-- Helper toward `prop-disk-bs-conv` (Proposition 5.16,
restricted successor are the ambient `σ`-cycles intersected with `S`. -/
theorem firstReturn_sameCycle_iff (σ : Equiv.Perm α) (S : Finset α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S) (x y : S) :
    (cyclicFirstReturn σ S hper).SameCycle x y ↔ σ.SameCycle x.1 y.1 := by
  constructor
  · intro hxy
    let R := cyclicFirstReturn σ S hper
    have hstep : ∀ z : S, σ.SameCycle z.1 (R z).1 :=
      firstReturn_sameCycle σ S hper
    have hback : ∀ z : S, σ.SameCycle z.1 (R.symm z).1 := by
      intro z
      simpa using (hstep (R.symm z)).symm
    have hpos : ∀ n : ℕ, σ.SameCycle x.1 ((R ^ n) x).1 := by
      intro n
      induction n with
      | zero => exact Equiv.Perm.SameCycle.rfl
      | succ n ih =>
        rw [pow_succ']
        exact ih.trans (hstep ((R ^ n) x))
    have hneg : ∀ n : ℕ, σ.SameCycle x.1 ((R.symm ^ n) x).1 := by
      intro n
      induction n with
      | zero => exact Equiv.Perm.SameCycle.rfl
      | succ n ih =>
        rw [pow_succ']
        exact ih.trans (hback ((R.symm ^ n) x))
    rcases hxy with ⟨i, hi⟩
    cases i with
    | ofNat n =>
      have hn := hpos n
      have hn' : σ.SameCycle x.1 ((R ^ (Int.ofNat n)) x).1 := by simpa using hn
      rw [hi] at hn'
      exact hn'
    | negSucc n =>
      have hn := hneg (n + 1)
      have hpow : (R ^ Int.negSucc n) x = (R.symm ^ (n + 1)) x := by
        rw [zpow_negSucc]
        rfl
      have hn' : σ.SameCycle x.1 ((R ^ Int.negSucc n) x).1 := by
        rw [hpow]
        exact hn
      rw [hi] at hn'
      exact hn'
  · intro hxy
    obtain ⟨p, hp, hperiod⟩ :=
      firstReturn_has_period_on_subset σ S {x.1} hper (by
        intro z hz
        simp only [Finset.mem_singleton] at hz
        rw [hz]
        exact x.2) ⟨x.1, by simp⟩
    have hperiod' : (σ ^ p) x.1 = x.1 := by simpa using hperiod
    obtain ⟨q, hq⟩ := sameCycle_nat_pow_of_period σ x.1 y.1 p hp hperiod' hxy
    have hqS : (σ ^ q) x.1 ∈ S := hq ▸ y.2
    obtain ⟨n, hn⟩ := firstReturn_reaches_iterate σ S hper x q hqS
    refine ⟨(n : ℤ), ?_⟩
    apply Subtype.ext
    calc
      ((cyclicFirstReturn σ S hper ^ n) x).1 = (σ ^ q) x.1 := hn
      _ = y.1 := hq

end DirectedDistances.PlanarMap
