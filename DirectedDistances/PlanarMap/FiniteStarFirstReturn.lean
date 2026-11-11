module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap

import DirectedDistances.PlanarMap.SlopeAngularOrder

/-! Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.

# First returns in finite planar stars

The source uses the cut-completed map at -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem permIterateEqPow {α : Type*} (σ : Equiv.Perm α) (k : ℕ) :
    ((σ : α → α)^[k]) = ((σ ^ k : Equiv.Perm α) : α → α) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    rw [Function.iterate_succ_apply, ih]
    simp only [pow_succ, Equiv.Perm.mul_apply]

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem permIterateInvSub {α : Type*} (σ : Equiv.Perm α) {j k : ℕ}
    (hjk : j ≤ k) (x : α) :
    ((σ⁻¹ : Equiv.Perm α) : α → α)^[j] ((σ : α → α)^[k] x) =
      (σ : α → α)^[k - j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjk' : j ≤ k := Nat.le_trans (Nat.le_succ j) hjk
    rw [Function.iterate_succ_apply', ih hjk']
    have hdecomp : k - j = (k - (j + 1)) + 1 := by omega
    rw [hdecomp, Function.iterate_succ_apply']
    simp

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] noncomputable def subsetFirstReturnTime {α : Type*}
    (σ : Equiv.Perm α) (S : Set α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S) (x : S) : ℕ :=
  by
    classical
    exact Nat.find (hper x)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem subsetFirstReturnTime_spec {α : Type*} (σ : Equiv.Perm α)
    (S : Set α) (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S) (x : S) :
    0 < subsetFirstReturnTime σ S hper x ∧
      (σ : α → α)^[subsetFirstReturnTime σ S hper x] x.1 ∈ S ∧
      ∀ j : ℕ, 0 < j → j < subsetFirstReturnTime σ S hper x →
        (σ : α → α)^[j] x.1 ∉ S := by
  classical
  unfold subsetFirstReturnTime
  have hs := Nat.find_spec (hper x)
  refine ⟨hs.1, hs.2, ?_⟩
  intro j hj hjk hjS
  exact Nat.find_min (hper x) hjk ⟨hj, hjS⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] noncomputable def subsetFirstReturn {α : Type*}
    (σ : Equiv.Perm α) (S : Set α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S) (x : S) : S :=
  ⟨(σ : α → α)^[subsetFirstReturnTime σ S hper x] x.1,
    (subsetFirstReturnTime_spec σ S hper x).2.1⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem subsetFirstReturn_inv_apply {α : Type*} (σ : Equiv.Perm α)
    (S : Set α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S)
    (hperInv : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      ((σ⁻¹ : Equiv.Perm α) : α → α)^[k] x.1 ∈ S) (x : S) :
    subsetFirstReturn (σ⁻¹) S hperInv (subsetFirstReturn σ S hper x) = x := by
  classical
  let k := subsetFirstReturnTime σ S hper x
  have hk := subsetFirstReturnTime_spec σ S hper x
  let y := subsetFirstReturn σ S hper x
  have hy : (σ : α → α)^[k] x.1 = y.1 := rfl
  have htime : subsetFirstReturnTime (σ⁻¹) S hperInv y = k := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (hperInv y) ⟨hk.1, by
        rw [← hy]
        have h := permIterateInvSub σ (Nat.le_refl k) x.1
        rw [h]
        simp only [Nat.sub_self, Function.iterate_zero_apply]
        exact x.2
      ⟩
    · by_contra hnot
      let j := subsetFirstReturnTime (σ⁻¹) S hperInv y
      have hj := subsetFirstReturnTime_spec (σ⁻¹) S hperInv y
      have hjk : j < k := by dsimp [j]; omega
      have hforward : (σ : α → α)^[k - j] x.1 ∈ S := by
        have hmem := hj.2.1
        rw [← hy] at hmem
        rw [permIterateInvSub σ (Nat.le_of_lt hjk) x.1] at hmem
        exact hmem
      have hpos : 0 < k - j := by omega
      have hlt : k - j < k := by omega
      exact hk.2.2 (k - j) hpos hlt hforward
  apply Subtype.ext
  change ((σ⁻¹ : Equiv.Perm α) : α → α)^[
      subsetFirstReturnTime (σ⁻¹) S hperInv y] y.1 = x.1
  rw [htime]
  change ((σ⁻¹ : Equiv.Perm α) : α → α)^[k]
      ((σ : α → α)^[k] x.1) = x.1
  have h := permIterateInvSub σ (Nat.le_refl k) x.1
  simpa using h

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] noncomputable def subsetFirstReturnPerm {α : Type*}
    (σ : Equiv.Perm α) (S : Set α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S)
    (hperInv : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      ((σ⁻¹ : Equiv.Perm α) : α → α)^[k] x.1 ∈ S) : Equiv.Perm S := by
  classical
  let f : S → S := subsetFirstReturn σ S hper
  let g : S → S := subsetFirstReturn (σ⁻¹) S hperInv
  have hgf : ∀ x, g (f x) = x := subsetFirstReturn_inv_apply σ S hper hperInv
  have hfg : ∀ x, f (g x) = x :=
    subsetFirstReturn_inv_apply (σ⁻¹) S hperInv hper
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg g hxy
    rw [hgf x, hgf y] at h
    exact h
  have hsurj : Function.Surjective f := by
    intro y
    exact ⟨g y, hfg y⟩
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem subsetFirstReturnPerm_apply {α : Type*} (σ : Equiv.Perm α)
    (S : Set α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S)
    (hperInv : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      ((σ⁻¹ : Equiv.Perm α) : α → α)^[k] x.1 ∈ S) (x : S) :
    (subsetFirstReturnPerm σ S hper hperInv x).1 =
      (σ : α → α)^[subsetFirstReturnTime σ S hper x] x.1 := rfl

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem subsetFirstReturn_sameCycle {α : Type*} (σ : Equiv.Perm α)
    (S : Set α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S) (x : S) :
    Equiv.Perm.SameCycle σ x.1 (subsetFirstReturn σ S hper x).1 := by
  refine ⟨subsetFirstReturnTime σ S hper x, ?_⟩
  change (σ ^ subsetFirstReturnTime σ S hper x) x.1 =
    ((σ : α → α)^[subsetFirstReturnTime σ S hper x]) x.1
  exact (congrFun (permIterateEqPow σ _) x.1).symm

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem subsetFirstReturn_eq_next {α : Type*} (σ : Equiv.Perm α)
    (S : Set α)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧
      (σ : α → α)^[k] x.1 ∈ S) (x : S)
    (hnext : σ x.1 ∈ S) :
    (subsetFirstReturn σ S hper x).1 = σ x.1 := by
  classical
  have htime : subsetFirstReturnTime σ S hper x = 1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (hper x) ⟨Nat.one_pos, by simpa using hnext⟩
    · exact Nat.succ_le_of_lt (subsetFirstReturnTime_spec σ S hper x).1
  simp [subsetFirstReturn, htime]

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private noncomputable def drawingStarRotation {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) :
    Equiv.Perm {e : D // vert e = vert d} := by
  classical
  let f : {e : D // vert e = vert d} → {e : D // vert e = vert d} :=
    fun e => ⟨rot e.1, by simpa [e.2] using P.vert_rotation e.1⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact rot.injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨rot.symm y.1, ?_⟩, ?_⟩
    · have h := P.vert_rotation (rot.symm y.1)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans y.2
    · dsimp [f]
      apply Subtype.ext
      exact Equiv.apply_symm_apply rot y.1
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private theorem drawingStarRotation_pow_val {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (k : ℕ)
    (x : {e : D // vert e = vert d}) :
    ((drawingStarRotation P d ^ k) x).1 = (rot ^ k) x.1 := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    calc
      ((drawingStarRotation P d ^ (k + 1)) x).1 =
          ((drawingStarRotation P d ^ k) ((drawingStarRotation P d) x)).1 := by
            rw [pow_succ, Equiv.Perm.mul_apply]
      _ = (rot ^ k) ((drawingStarRotation P d x).1) := ih _
      _ = (rot ^ k) (rot x.1) := rfl
      _ = (rot ^ (k + 1)) x.1 := by rw [pow_succ, Equiv.Perm.mul_apply]

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private theorem drawingVertPow {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) :
    ∀ k : ℕ, ∀ d : D, vert ((rot ^ k) d) = vert d := by
  intro k
  induction k with
  | zero => intro d; rfl
  | succ k ih =>
    intro d
    rw [pow_succ, Equiv.Perm.mul_apply]
    exact (ih (rot d)).trans (P.vert_rotation d)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private theorem finitePermPeriod {α : Type*} [Finite α]
    (σ : Equiv.Perm α) (x : α) :
    ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
  exact ⟨orderOf σ, orderOf_pos σ, by simp [pow_orderOf_eq_one]⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private theorem drawingRotationExists {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) :
    ∃ k : ℕ, 0 < k ∧ (rot : D → D)^[k] d = d := by
  classical
  let τ := drawingStarRotation P d
  let x : {e : D // vert e = vert d} := ⟨d, rfl⟩
  have hfinite : Finite {e : D // vert e = vert d} :=
    (P.rotation_agreement d).1.to_subtype
  obtain ⟨k, hk, hperiod⟩ := @finitePermPeriod _ hfinite τ x
  refine ⟨k, hk, ?_⟩
  have hv := congrArg Subtype.val hperiod
  have hv' : (rot ^ k) d = d := by
    calc
      (rot ^ k) d = ((τ ^ k) x).1 :=
        (drawingStarRotation_pow_val P d k x).symm
      _ = d := hv
  rw [permIterateEqPow rot k]
  exact hv'

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private noncomputable def drawingRotationPeriod {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) : ℕ := by
  classical
  exact Nat.find (drawingRotationExists P d)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private theorem drawingRotationPeriod_spec {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) :
    0 < drawingRotationPeriod P d ∧
      (rot : D → D)^[drawingRotationPeriod P d] d = d ∧
      ∀ j : ℕ, 0 < j → j < drawingRotationPeriod P d →
        (rot : D → D)^[j] d ≠ d := by
  classical
  let q : ℕ → Prop := fun j => 0 < j ∧ (rot : D → D)^[j] d = d
  have hq : ∃ j, q j := by
    exact drawingRotationExists P d
  change 0 < Nat.find hq ∧
    (rot : D → D)^[Nat.find hq] d = d ∧
      ∀ j : ℕ, 0 < j → j < Nat.find hq →
        (rot : D → D)^[j] d ≠ d
  have hs := Nat.find_spec hq
  refine ⟨hs.1, hs.2, ?_⟩
  intro j hj hjlt hret
  exact Nat.find_min hq hjlt ⟨hj, hret⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
private theorem drawingAngleCutIterate {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d f : D)
    (hvert : vert f = vert d) (hne : f ≠ d) :
    ∃ n : ℕ, 0 < n ∧ n ≤ drawingRotationPeriod P d ∧
      (rot : D → D)^[n] d = f ∧
      ∀ j : ℕ, 0 < j → j < n →
        ccwTurn (P.arc d).initialDirection
            (P.arc ((rot : D → D)^[j] d)).initialDirection <
          ccwTurn (P.arc d).initialDirection (P.arc f).initialDirection := by
  classical
  let dir : D → ℂ := fun x => (P.arc x).initialDirection
  let turn := ccwTurn (dir d) (dir f)
  let q : ℕ → Prop := fun j => 0 < j ∧ turn ≤ ccwTurn (dir d) (dir ((rot : D → D)^[j] d))
  have hturnne : turn ≠ 2 * Real.pi := by
    intro hfull
    have harg := (ccwTurn_eq_two_pi_iff (dir d) (dir f)).mp hfull
    exact hne (P.initial_arg_injective f d hvert harg.symm)
  have hturnlt : turn < 2 * Real.pi :=
    lt_of_le_of_ne (ccwTurn_le_two_pi (dir d) (dir f)) hturnne
  have hperiod := drawingRotationPeriod_spec P d
  have hq : ∃ j, q j := by
    refine ⟨drawingRotationPeriod P d, hperiod.1, ?_⟩
    rw [hperiod.2.1]
    rw [(ccwTurn_eq_two_pi_iff (dir d) (dir d)).2 rfl]
    exact le_of_lt hturnlt
  let n := Nat.find hq
  have hn := Nat.find_spec hq
  have hnmin : ∀ j : ℕ, 0 < j → j < n → ¬ q j := by
    intro j hj hjn hqj
    exact Nat.find_min hq hjn ⟨hj, hqj.2⟩
  have hnle : n ≤ drawingRotationPeriod P d := by
    exact Nat.find_min' hq ⟨hperiod.1, by
      rw [hperiod.2.1]
      rw [(ccwTurn_eq_two_pi_iff (dir d) (dir d)).2 rfl]
      exact le_of_lt hturnlt⟩
  have hiterate : (rot : D → D)^[n] d = f := by
    by_cases hnone : n = 1
    · have hfind1 : Nat.find hq = 1 := by simpa [n] using hnone
      have hrot := P.rotation_agreement d
      rcases hrot with ⟨_, hd, hr, hcase⟩
      have hfstar : f ∈ {x | vert x = vert d} := hvert
      rcases hcase with hsingle | ⟨hneq, hmin⟩
      · have : f = d := by simpa [hsingle.2] using hfstar
        exact (hne this).elim
      · have hle := hmin f hfstar hne
        have hturnle : turn ≤ ccwTurn (dir d) (dir (rot d)) := by
          simpa [n, hfind1] using hn.2
        have heq : turn = ccwTurn (dir d) (dir (rot d)) := by
          apply le_antisymm
          · exact hturnle
          · exact hle
        have harg := ccwTurn_left_injective heq.symm
        have hvfr : vert f = vert (rot d) :=
          hvert.trans (P.vert_rotation d).symm
        have hresult : rot d = f :=
          (P.initial_arg_injective f (rot d) hvfr harg.symm).symm
        simpa [n, hfind1] using hresult
    · have hnlarge : 1 < n := by omega
      let j := n - 1
      have hjpos : 0 < j := by dsimp [j]; omega
      have hjlt : j < n := by dsimp [j]; omega
      have hbelow :
          ccwTurn (dir d) (dir ((rot : D → D)^[j] d)) < turn := by
        have hnot := hnmin j hjpos hjlt
        dsimp [q, turn] at hnot
        exact lt_of_not_ge (fun h => hnot ⟨hjpos, h⟩)
      have hnext : (rot : D → D)^[n] d = rot ((rot : D → D)^[j] d) := by
        have hnj : n = j + 1 := by dsimp [j]; omega
        rw [hnj, Function.iterate_succ_apply']
      have hnvert : vert ((rot : D → D)^[n] d) = vert d := by
        rw [permIterateEqPow]
        exact drawingVertPow P n d
      by_cases heq : turn = ccwTurn (dir d) (dir ((rot : D → D)^[n] d))
      · have harg := ccwTurn_left_injective heq.symm
        exact (P.initial_arg_injective f ((rot : D → D)^[n] d)
          (hvert.trans hnvert.symm) harg.symm).symm
      · have habove : turn <
            ccwTurn (dir d) (dir ((rot : D → D)^[n] d)) :=
          lt_of_le_of_ne hn.2 heq
        have hbetween : CcwBetween
          (dir ((rot : D → D)^[j] d)) (dir f)
          (dir ((rot : D → D)^[n] d)) := by
          change ccwTurn (dir ((rot : D → D)^[j] d)) (dir f) <
            ccwTurn (dir ((rot : D → D)^[j] d))
              (dir ((rot : D → D)^[n] d))
          have hcompf := ccwTurn_comp_add hbelow
          have hcompn := ccwTurn_comp_add (lt_trans hbelow habove)
          linarith
        have hprevvert : vert ((rot : D → D)^[j] d) = vert d := by
          rw [permIterateEqPow]
          exact drawingVertPow P j d
        have hfprev : vert f = vert ((rot : D → D)^[j] d) :=
          hvert.trans hprevvert.symm
        have hfstar : f ∈ {x | vert x = vert ((rot : D → D)^[j] d)} := hfprev
        have hfd : f ≠ (rot : D → D)^[j] d := by
          intro heq'
          have hturneq := congrArg (fun x => ccwTurn (dir d) (dir x)) heq'
          dsimp [turn] at hbelow
          exact (ne_of_lt hbelow) hturneq.symm
        have hstepneq :
            rot ((rot : D → D)^[j] d) ≠ (rot : D → D)^[j] d := by
          intro heq'
          have hturneq :
              ccwTurn (dir d) (dir ((rot : D → D)^[n] d)) =
                ccwTurn (dir d) (dir ((rot : D → D)^[j] d)) := by
            rw [hnext, heq']
          exact (ne_of_lt (lt_trans hbelow habove)) hturneq.symm
        have hrot := P.rotation_agreement ((rot : D → D)^[j] d)
        rcases hrot with ⟨_, _, _, hcase⟩
        rcases hcase with hsingle | ⟨_, hmin⟩
        · exact (hstepneq hsingle.1).elim
        · have hle := hmin f hfstar hfd
          have hbetween' : CcwBetween
            (dir ((rot : D → D)^[j] d)) (dir f)
            (dir (rot ((rot : D → D)^[j] d))) := by
            simpa [hnext] using hbetween
          change ccwTurn (dir ((rot : D → D)^[j] d)) (dir f) <
            ccwTurn (dir ((rot : D → D)^[j] d))
              (dir (rot ((rot : D → D)^[j] d))) at hbetween'
          exact False.elim ((not_lt_of_ge hle) hbetween')
  refine ⟨n, hn.1, hnle, hiterate, ?_⟩
  intro j hj hjn
  have hnot := hnmin j hj hjn
  dsimp [q, turn] at hnot
  exact lt_of_not_ge (fun h => hnot ⟨hj, h⟩)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem drawingRotation_period {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) :
    ∃ k : ℕ, 0 < k ∧ (rot : D → D)^[k] d = d := by
  exact drawingRotationExists P d

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem drawingPositiveReturn {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D) (x : {d : D // d ∈ S}) :
    ∃ k : ℕ, 0 < k ∧ (rot : D → D)^[k] x.1 ∈ S := by
  obtain ⟨k, hk, hperiod⟩ := drawingRotation_period P x.1
  refine ⟨k, hk, ?_⟩
  rw [hperiod]
  exact x.2

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem drawingPositiveReturnInv {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D) (x : {d : D // d ∈ S}) :
    ∃ k : ℕ, 0 < k ∧ ((rot⁻¹ : Equiv.Perm D) : D → D)^[k] x.1 ∈ S := by
  obtain ⟨k, hk, hperiod⟩ := drawingRotation_period P x.1
  have h := permIterateInvSub rot (Nat.le_refl k) x.1
  rw [hperiod] at h
  refine ⟨k, hk, ?_⟩
  have h' : ((rot⁻¹ : Equiv.Perm D) : D → D)^[k] x.1 = x.1 := by
    simpa using h
  rw [h']
  exact x.2

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] noncomputable def drawingFirstReturnPerm {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D) :
    Equiv.Perm {d : D // d ∈ S} :=
  subsetFirstReturnPerm rot S (drawingPositiveReturn P S)
    (drawingPositiveReturnInv P S)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem drawingFirstReturn_sameCycle {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : {d : D // d ∈ S}) :
    Equiv.Perm.SameCycle rot d.1 ((drawingFirstReturnPerm P S d).1) := by
  exact subsetFirstReturn_sameCycle rot S (drawingPositiveReturn P S) d

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem drawingFirstReturn_sameVertex {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : {d : D // d ∈ S}) :
    vert ((drawingFirstReturnPerm P S d).1) = vert d.1 := by
  let hper := drawingPositiveReturn P S
  let hperInv := drawingPositiveReturnInv P S
  let k := subsetFirstReturnTime rot S hper d
  change vert ((subsetFirstReturnPerm rot S hper hperInv d).1) = vert d.1
  rw [subsetFirstReturnPerm_apply]
  rw [permIterateEqPow]
  exact drawingVertPow P k d.1

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem drawingFirstReturn_eq_next {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : {d : D // d ∈ S}) (hnext : rot d.1 ∈ S) :
    (drawingFirstReturnPerm P S d).1 = rot d.1 := by
  exact subsetFirstReturn_eq_next rot S (drawingPositiveReturn P S) d hnext

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def drawingFirstReturnCcwObligation {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : {d : D // d ∈ S}) : Prop :=
  CcwSuccessor {e | e ∈ S ∧ vert e = vert d.1}
    (fun e => (P.arc e).initialDirection) d.1
    (drawingFirstReturnPerm P S d).1

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem drawingFirstReturnCcwObligation_holds {D V : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : {d : D // d ∈ S}) : drawingFirstReturnCcwObligation P S d := by
  classical
  let dir : D → ℂ := fun e => (P.arc e).initialDirection
  let star : Set D := {e | e ∈ S ∧ vert e = vert d.1}
  let hper := drawingPositiveReturn P S
  let k := subsetFirstReturnTime rot S hper d
  let r : D := (drawingFirstReturnPerm P S d).1
  let p := drawingRotationPeriod P d.1
  have hspec := subsetFirstReturnTime_spec rot S hper d
  have hret : (rot : D → D)^[k] d.1 = r := by
    simpa [k, r, drawingFirstReturnPerm] using
      (subsetFirstReturnPerm_apply rot S hper
        (drawingPositiveReturnInv P S) d).symm
  have hretS : r ∈ S := (drawingFirstReturnPerm P S d).2
  have hretV : vert r = vert d.1 := drawingFirstReturn_sameVertex P S d
  have hfin : star.Finite := by
    apply Set.Finite.subset (P.rotation_agreement d.1).1
    intro e he
    exact he.2
  have hd : d.1 ∈ star := ⟨d.2, rfl⟩
  have hr : r ∈ star := ⟨hretS, hretV⟩
  change CcwSuccessor star dir d.1 r
  have hperiod := drawingRotationPeriod_spec P d.1
  by_cases hreturn : r = d.1
  · have hperiodK : (rot : D → D)^[k] d.1 = d.1 := hret.trans hreturn
    have hpk : p ≤ k := by
      by_contra hnot
      exact hperiod.2.2 k hspec.1 (Nat.lt_of_not_ge hnot) hperiodK
    have hkp : k ≤ p := by
      dsimp [k, subsetFirstReturnTime]
      apply Nat.find_min'
      refine ⟨hperiod.1, ?_⟩
      rw [hperiod.2.1]
      exact d.2
    have hkeq : k = p := Nat.le_antisymm hkp hpk
    have hstar : star = {d.1} := by
      ext e
      constructor
      · intro he
        rcases he with ⟨heS, heV⟩
        by_cases heq : e = d.1
        · simp [heq]
        · obtain ⟨n, hn, hnp, hne, _⟩ :=
            drawingAngleCutIterate P d.1 e heV heq
          have hnneq : n ≠ p := by
            intro hnpeq
            have hiterp : (rot : D → D)^[p] d.1 = e := by
              simpa [hnpeq] using hne
            exact heq (hiterp.symm.trans hperiod.2.1)
          have hnltp : n < p := lt_of_le_of_ne hnp hnneq
          have hnltk : n < k := by omega
          have hnS : (rot : D → D)^[n] d.1 ∈ S := by rw [hne]; exact heS
          exact False.elim (hspec.2.2 n hn hnltk hnS)
      · intro he
        have heq : e = d.1 := by simpa using he
        subst e
        exact ⟨d.2, rfl⟩
    refine ⟨hfin, hd, hr, Or.inl ⟨hreturn, hstar⟩⟩
  · have hneReturn : r ≠ d.1 := hreturn
    obtain ⟨ne, hnePos, hneLe, hneVal, hneFirst⟩ :=
      drawingAngleCutIterate P d.1 r hretV hneReturn
    have hneEqK : ne = k := by
      apply Nat.le_antisymm
      · by_contra hnot
        have hlt : k < ne := Nat.lt_of_not_ge hnot
        have hangle := hneFirst k hspec.1 hlt
        rw [hret] at hangle
        exact (lt_irrefl _) hangle
      · by_contra hnot
        have hlt : ne < k := Nat.lt_of_not_ge hnot
        have hneS : (rot : D → D)^[ne] d.1 ∈ S := by
          rw [hneVal]
          exact hretS
        exact hspec.2.2 ne hnePos hlt hneS
    apply (ccwSuccessor_iff_no_between star dir d.1 r hfin hd).2
    refine Or.inr ⟨hneReturn, hr, ?_⟩
    intro e he hed her hbetween
    rcases he with ⟨heS, heV⟩
    change ccwTurn (dir d.1) (dir e) < ccwTurn (dir d.1) (dir r) at hbetween
    obtain ⟨n, hnPos, hnLe, hnVal, hnFirst⟩ :=
      drawingAngleCutIterate P d.1 e heV hed
    have hnltne : n < ne := by
      by_contra hnot
      have hnele : ne ≤ n := Nat.le_of_not_gt hnot
      by_cases heq : ne = n
      · have hneVal' : (rot : D → D)^[n] d.1 = r := by
          simpa [heq] using hneVal
        have hfeq : e = r := hnVal.symm.trans hneVal'
        exact her hfeq
      · have hlt : ne < n := by omega
        have hangle := hnFirst ne hnePos hlt
        rw [hneVal] at hangle
        linarith
    have hnltk : n < k := by omega
    have hnS : (rot : D → D)^[n] d.1 ∈ S := by rw [hnVal]; exact heS
    exact hspec.2.2 n hnPos hnltk hnS

end DirectedDistances.PlanarMap
