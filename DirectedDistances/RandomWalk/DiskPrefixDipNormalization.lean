module

public import DirectedDistances.RandomWalk.BridgeEndpointWindow

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/

/-! # Disk prefix dip normalization

Deterministic and cone-bridge helpers toward Proposition 5.16
slice 1). This file records the disk prefix-dip event in first-hit form; it is not the
paper result. -/

public section
namespace DirectedDistances.RandomWalk

private theorem codeWalk_fst_step_abs_le_one (ω : ℕ → Fin 3) (t : ℕ) :
    |(codeWalk ω (t + 1)).1 - (codeWalk ω t).1| ≤ 1 := by
  have h := congrArg Prod.fst (codeWalk_succ_sub ω t)
  rw [Prod.fst_sub] at h
  rw [h]
  exact lazyTwoDimensionalStep_fst_abs_le_one (ω (t + 1))

private theorem codeFstFirstHit_eq_nat_of_hit (a : ℤ) (ω : ℕ → Fin 3)
    (t : ℕ) (ht : (codeWalk ω t).1 = a) :
    ∃ t' : ℕ, codeFstFirstHit a ω = t' ∧ t' ≤ t ∧
      (codeWalk ω t').1 = a := by
  classical
  let hhit : ∃ s, (codeWalk ω s).1 = a := ⟨t, ht⟩
  refine ⟨Nat.find hhit, ?_, Nat.find_min' hhit ht, Nat.find_spec hhit⟩
  simp [codeFstFirstHit, hhit]

private theorem codeFstFirstHit_eq_nat_endpoint (a : ℤ) (ω : ℕ → Fin 3)
    (T : ℕ) (hT : codeFstFirstHit a ω = T) :
    (codeWalk ω T).1 = a := by
  classical
  have hhit : ∃ t, (codeWalk ω t).1 = a := by
    by_contra hhit
    have htop : codeFstFirstHit a ω = ⊤ := by
      simp [codeFstFirstHit, hhit]
    rw [htop] at hT
    exact (ENat.top_ne_natCast T) hT
  obtain ⟨t, ht⟩ := hhit
  obtain ⟨t', ht', _, hval⟩ := codeFstFirstHit_eq_nat_of_hit a ω t ht
  have heq : t' = T := by exact_mod_cast ht'.symm.trans hT
  rw [heq] at hval
  exact hval

private theorem codeWalk_fst_hits_level_before
    (ω : ℕ → Fin 3) (d j : ℕ) (hd : 0 < d)
    (hj : (codeWalk ω j).1 ≤ -(d : ℤ)) :
    ∃ t ≤ j, (codeWalk ω t).1 = -(d : ℤ) := by
  classical
  let P : ℕ → Prop := fun i => (codeWalk ω i).1 ≤ -(d : ℤ)
  have hP : ∃ i, P i := ⟨j, hj⟩
  let t := Nat.find hP
  have htP : P t := Nat.find_spec hP
  have htj : t ≤ j := Nat.find_min' hP hj
  have htpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    have hzero := codeWalk_zero ω
    change (codeWalk ω t).1 ≤ -(d : ℤ) at htP
    rw [ht0, hzero] at htP
    omega
  let s := t - 1
  have ht : t = s + 1 := by dsimp [s]; omega
  have hsnot : ¬ P s := by
    apply Nat.find_min hP
    dsimp [s]
    omega
  have hs : -(d : ℤ) < (codeWalk ω s).1 := by
    dsimp [P] at hsnot
    omega
  have hstep := codeWalk_fst_step_abs_le_one ω s
  rw [abs_le] at hstep
  refine ⟨t, htj, ?_⟩
  have htP' : (codeWalk ω (s + 1)).1 ≤ -(d : ℤ) := by simpa [ht] using htP
  have hlow : -(d : ℤ) ≤ (codeWalk ω (s + 1)).1 := by omega
  rw [ht]
  exact le_antisymm htP' hlow



theorem diskPrefixDip_iff_firstHit
    (ω : ℕ → Fin 3) (K K0 N T : ℕ) (hK0 : K0 < K)
    (hT : codeFstFirstHit (-(K : ℤ)) ω = T) :
    (∃ j : ℕ, j + N < T ∧
      (codeWalk ω j).1 ≤ (codeWalk ω T).1 + (K0 : ℤ)) ↔
    ∃ t' : ℕ, codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω = t' ∧
      t' + N < T := by
  have hTval := codeFstFirstHit_eq_nat_endpoint (-(K : ℤ)) ω T hT
  have htarget (t : ℕ)
      (ht : (codeWalk ω t).1 = -((K - K0 : ℕ) : ℤ)) :
      ∃ t' : ℕ, codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω = t' ∧
        t' ≤ t ∧ (codeWalk ω t').1 = -((K - K0 : ℕ) : ℤ) :=
    codeFstFirstHit_eq_nat_of_hit _ ω t ht
  constructor
  · rintro ⟨j, hjT, hj⟩
    have hlevel : (codeWalk ω j).1 ≤ -((K - K0 : ℕ) : ℤ) := by
      rw [hTval] at hj
      have hsub : (K - K0 : ℕ) = K - K0 := rfl
      omega
    have hcross := codeWalk_fst_hits_level_before ω (K - K0) j (by omega) hlevel
    obtain ⟨t, htj, htt⟩ := hcross
    obtain ⟨t', htime, hle, _⟩ := htarget t htt
    exact ⟨t', htime, by omega⟩
  · rintro ⟨t', htime, htN⟩
    have htval := codeFstFirstHit_eq_nat_endpoint (-((K - K0 : ℕ) : ℤ)) ω t' htime
    refine ⟨t', by omega, ?_⟩
    rw [hTval, htval]
    omega



theorem coneEvent_codeFstFirstHit_finite_le
    (ell n K : ℕ) (ω : ℕ → Fin 3)
    (hω : ω ∈ coneEvent (ell : ℤ) 0 n)
    (hK : 1 ≤ K) (hKell : K ≤ ell) :
    ∃ T : ℕ, codeFstFirstHit (-(K : ℤ)) ω = T ∧ T ≤ n := by
  obtain ⟨T, hT, _, hTn, _⟩ :=
    coneEvent_fstFirstHit (ell : ℤ) n K hK (by exact_mod_cast hKell) ω hω
  exact ⟨T, hT, hTn⟩



theorem diskPrefixDip_of_level_le
    (ω : ℕ → Fin 3) (K K0 N T : ℕ)
    (hK : K ≤ K0) (hN : N < T)
    (hT : codeFstFirstHit (-(K : ℤ)) ω = T) :
    ∃ j : ℕ, j + N < T ∧
      (codeWalk ω j).1 ≤ (codeWalk ω T).1 + (K0 : ℤ) := by
  refine ⟨0, by simpa using hN, ?_⟩
  rw [codeWalk_zero, codeFstFirstHit_eq_nat_endpoint (-(K : ℤ)) ω T hT]
  omega

end DirectedDistances.RandomWalk
