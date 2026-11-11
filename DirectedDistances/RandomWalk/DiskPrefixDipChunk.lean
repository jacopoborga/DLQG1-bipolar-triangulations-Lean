module

public import DirectedDistances.RandomWalk.CappedLevelChunks

/-! # Disk prefix dips and complete level chunks

Helper toward Proposition 5.16 (`prop-disk-bs-conv`,
out the disk prefix dip; not the paper result. -/

public section
namespace DirectedDistances.RandomWalk

private theorem codeWalk_fst_step_abs_le_one (ω : ℕ → Fin 3) (n : ℕ) :
    |(codeWalk ω (n + 1)).1 - (codeWalk ω n).1| ≤ 1 := by
  have h := congrArg Prod.fst (codeWalk_succ_sub ω n)
  rw [Prod.fst_sub] at h
  rw [h]
  generalize ω (n + 1) = c
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

private theorem codeWalk_fst_hits_level_before (ω : ℕ → Fin 3) (d j : ℕ)
    (hd : 0 < d) (hj : (codeWalk ω j).1 ≤ -(d : ℤ)) :
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
    have htP0 : (codeWalk ω 0).1 ≤ -(d : ℤ) := by
      simpa [P, ht0] using htP
    rw [codeWalk_zero ω] at htP0
    omega
  let r := t - 1
  have htr : t = r + 1 := by dsimp [r]; omega
  have hrnot : ¬ P r := by
    apply Nat.find_min hP
    dsimp [r]
    omega
  have hr : -(d : ℤ) < (codeWalk ω r).1 := by
    dsimp [P] at hrnot
    omega
  have hstep := codeWalk_fst_step_abs_le_one ω r
  rw [abs_le] at hstep
  refine ⟨t, htj, ?_⟩
  have htP' : (codeWalk ω (r + 1)).1 ≤ -(d : ℤ) := by
    simpa [htr] using htP
  rw [htr]
  omega

private theorem codeFstFirstHit_zero (ω : ℕ → Fin 3) :
    codeFstFirstHit 0 ω = 0 := by
  classical
  have h : ∃ n, (codeWalk ω n).1 = 0 := ⟨0, by simp [codeWalk_zero]⟩
  have hfind : Nat.find h = 0 := by
    apply (Nat.find_eq_iff h).2
    constructor
    · simp [codeWalk_zero]
    · intro n hn
      omega
  simp [codeFstFirstHit, h, hfind]

private theorem codeFstFirstHit_toNat_hit {a : ℤ} (ω : ℕ → Fin 3)
    (hfin : codeFstFirstHit a ω < ⊤) :
    (codeWalk ω (codeFstFirstHit a ω).toNat).1 = a := by
  classical
  have hhit : ∃ n, (codeWalk ω n).1 = a := by
    by_contra hn
    have htop : codeFstFirstHit a ω = ⊤ := by
      simp [codeFstFirstHit, hn]
    rw [htop] at hfin
    simp at hfin
  let t := Nat.find hhit
  have htime : codeFstFirstHit a ω = (t : ℕ∞) := by
    simp [codeFstFirstHit, hhit, t]
  have htoNat : (codeFstFirstHit a ω).toNat = t := by
    rw [htime]
    rfl
  rw [htoNat]
  exact Nat.find_spec hhit

private theorem codeFstFirstHit_toNat_le_of_hit {a : ℤ} (ω : ℕ → Fin 3)
    (n : ℕ) (hhit : (codeWalk ω n).1 = a) :
    (codeFstFirstHit a ω).toNat ≤ n := by
  classical
  let h : ∃ k, (codeWalk ω k).1 = a := ⟨n, hhit⟩
  have htime : codeFstFirstHit a ω = (Nat.find h : ℕ∞) := by
    simp [codeFstFirstHit, h]
  rw [htime]
  simpa using (Nat.find_min' h hhit)

private theorem codeWalk_fst_hits_level_of_deeper_hit (d e : ℕ)
    (ω : ℕ → Fin 3) (hde : d ≤ e) (he : codeFstFirstHit (-(e : ℤ)) ω < ⊤) :
    codeFstFirstHit (-(d : ℤ)) ω < ⊤ ∧
      (codeFstFirstHit (-(d : ℤ)) ω).toNat ≤
        (codeFstFirstHit (-(e : ℤ)) ω).toNat := by
  by_cases hd : d = 0
  · subst d
    simp only [Nat.cast_zero, Int.neg_zero]
    rw [codeFstFirstHit_zero]
    constructor
    · exact ENat.natCast_lt_top 0
    · simp
  · have hdpos : 0 < d := by omega
    have heHit := codeFstFirstHit_toNat_hit ω he
    have hcross := codeWalk_fst_hits_level_before ω d
      (codeFstFirstHit (-(e : ℤ)) ω).toNat hdpos (by rw [heHit]; omega)
    obtain ⟨k, hk, hdk⟩ := hcross
    have hdfin : codeFstFirstHit (-(d : ℤ)) ω < ⊤ := by
      have hex : ∃ n, (codeWalk ω n).1 = -(d : ℤ) := ⟨k, hdk⟩
      have heq : codeFstFirstHit (-(d : ℤ)) ω = (Nat.find hex : ℕ∞) := by
        simp [codeFstFirstHit, hex]
      rw [heq]
      exact ENat.natCast_lt_top _
    constructor
    · exact hdfin
    · exact (codeFstFirstHit_toNat_le_of_hit ω k hdk).trans hk

private theorem completedChunk_local_time (m C s : ℕ) (ω : ℕ → Fin 3)
    (hcomplete : (cappedLevelChunk m C s ω).2 = true) :
    ∃ L ≤ C,
      (codeWalk
        (codeShift (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat ω) L).1 =
          -(m : ℤ) := by
  let p := codeShift (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat ω
  have hcap : codeFstFirstHit (-(m : ℤ)) p ≤ C := by
    change (if codeFstFirstHit (-(m : ℤ)) p ≤ C then true else false) = true at hcomplete
    by_contra hnot
    simp [hnot] at hcomplete
  have hfin : codeFstFirstHit (-(m : ℤ)) p < ⊤ :=
    lt_of_le_of_lt hcap (ENat.natCast_lt_top C)
  refine ⟨(codeFstFirstHit (-(m : ℤ)) p).toNat, ?_, ?_⟩
  · cases ht : codeFstFirstHit (-(m : ℤ)) p with
    | top => simp [ht] at hfin
    | coe t =>
      have hle : (t : ℕ∞) ≤ C := by simpa [ht] using hcap
      exact_mod_cast hle
  · exact codeFstFirstHit_toNat_hit p hfin

private theorem codeFstFirstHit_base_finite_of_endpoint
    (m K s : ℕ) (ω : ℕ → Fin 3) (hsm : s * m ≤ K)
    (hK : codeFstFirstHit (-(K : ℤ)) ω < ⊤) :
    codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω < ⊤ :=
  (codeWalk_fst_hits_level_of_deeper_hit (s * m) K ω hsm hK).1

private theorem completeChunk_time_span
    (m K K0 C s o : ℕ) (ω : ℕ → Fin 3)
    (_hmK0 : K0 < m) (ho : K0 ≤ o) (hom : o < m)
    (hKrepr : K = s * m + o + 1)
    (hcomplete : (cappedLevelChunk m C s ω).2 = true)
    (hKfin : codeFstFirstHit (-(K : ℤ)) ω < ⊤) :
    (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat ≤
        (codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω).toNat ∧
      (codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω).toNat ≤
        (codeFstFirstHit (-(K : ℤ)) ω).toNat ∧
      (codeFstFirstHit (-(K : ℤ)) ω).toNat -
        (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat ≤ C := by
  let B := (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat
  let U := (codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω).toNat
  let T := (codeFstFirstHit (-(K : ℤ)) ω).toNat
  have hsmK : s * m ≤ K := by rw [hKrepr]; omega
  have hbasefin := codeFstFirstHit_base_finite_of_endpoint m K s ω hsmK hKfin
  have hbaseval : (codeWalk ω B).1 = -((s * m : ℕ) : ℤ) :=
    codeFstFirstHit_toNat_hit ω hbasefin
  obtain ⟨L, hLC, hlocal⟩ := completedChunk_local_time m C s ω hcomplete
  have hlocal' : (codeWalk (codeShift B ω) L).1 = -(m : ℤ) := by
    simpa [B] using hlocal
  have hshiftval :
      (codeWalk (codeShift B ω) L).1 =
        (codeWalk ω (B + L)).1 - (codeWalk ω B).1 := by
    have h := congrArg Prod.fst (codeWalk_codeShift B ω L)
    rw [Prod.fst_sub] at h
    exact h
  have hend : (codeWalk ω (B + L)).1 = -(((s + 1) * m : ℕ) : ℤ) := by
    rw [hlocal', hbaseval] at hshiftval
    have hmul : (s + 1) * m = s * m + m := by
      rw [Nat.add_mul]
      simp
    have hglobal : (codeWalk ω (B + L)).1 = -((s * m + m : ℕ) : ℤ) := by
      omega
    rw [hmul]
    exact hglobal
  have hKleEnd : K ≤ (s + 1) * m := by
    rw [hKrepr]
    omega
  have hcrossT := codeWalk_fst_hits_level_before ω K (B + L)
    (by omega) (by rw [hend]; omega)
  obtain ⟨r, hr, hrhit⟩ := hcrossT
  have hTle : T ≤ B + L :=
    (codeFstFirstHit_toNat_le_of_hit ω r hrhit).trans hr
  have htargetleK : K - K0 ≤ K := by omega
  have htargetgebase : s * m ≤ K - K0 := by
    rw [hKrepr]
    omega
  have hUfin : codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω < ⊤ :=
    (codeWalk_fst_hits_level_of_deeper_hit (K - K0) K ω htargetleK hKfin).1
  have hBU : B ≤ U := by
    exact (codeWalk_fst_hits_level_of_deeper_hit (s * m) (K - K0) ω
      htargetgebase hUfin).2
  have hUT : U ≤ T :=
    (codeWalk_fst_hits_level_of_deeper_hit (K - K0) K ω htargetleK hKfin).2
  refine ⟨hBU, hUT, ?_⟩
  have hTC : T ≤ B + C := by
    exact hTle.trans (Nat.add_le_add_left hLC B)
  dsimp [B, T] at hTC ⊢
  omega

/-- Helper toward Proposition 5.16 (`prop-disk-bs-conv`,
out the disk prefix dip; not the paper result. With the first hit of `-K`
finite, the selected chunk contains the first hits of `-(K-K0)` and `-K`. -/
theorem completeLevelChunk_firstHits_within_cap
    (m K K0 C s o : ℕ) (ω : ℕ → Fin 3)
    (hmK0 : K0 < m) (ho : K0 ≤ o) (hom : o < m)
    (hKrepr : K = s * m + o + 1)
    (hcomplete : (cappedLevelChunk m C s ω).2 = true)
    (hKfin : codeFstFirstHit (-(K : ℤ)) ω < ⊤) :
    (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat ≤
        (codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω).toNat ∧
      (codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω).toNat ≤
        (codeFstFirstHit (-(K : ℤ)) ω).toNat ∧
      (codeFstFirstHit (-(K : ℤ)) ω).toNat -
        (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat ≤ C := by
  exact completeChunk_time_span m K K0 C s o ω hmK0 ho hom hKrepr
    hcomplete hKfin

/-- Helper toward Proposition 5.16 (`prop-disk-bs-conv`,
out the disk prefix dip; not the paper result. This gives its first-hit-free
form when the window length is at least the `m^100` cap. -/
theorem completeLevelChunk_no_prefix_dip
    (m K K0 s o N T : ℕ) (ω : ℕ → Fin 3)
    (hmK0 : K0 < m) (ho : K0 ≤ o) (hom : o < m)
    (hKrepr : K = s * m + o + 1) (hN : m ^ 100 ≤ N)
    (hcomplete : (cappedLevelChunk m (m ^ 100) s ω).2 = true)
    (hT : codeFstFirstHit (-(K : ℤ)) ω = (T : ℕ∞)) :
    ¬ ∃ j : ℕ, j + N < T ∧
      (codeWalk ω j).1 ≤ (codeWalk ω T).1 + (K0 : ℤ) := by
  intro hdip
  have hKfin : codeFstFirstHit (-(K : ℤ)) ω < ⊤ := by
    rw [hT]
    exact ENat.natCast_lt_top _
  have hspan := completeChunk_time_span m K K0 (m ^ 100) s o ω hmK0 ho hom
    hKrepr hcomplete hKfin
  have hTtoNat : (codeFstFirstHit (-(K : ℤ)) ω).toNat = T := by
    have h := congrArg ENat.toNat hT
    simpa using h
  rw [hTtoNat] at hspan
  have hTval : (codeWalk ω T).1 = -(K : ℤ) := by
    have := codeFstFirstHit_toNat_hit ω hKfin
    rw [hTtoNat] at this
    exact this
  rcases hdip with ⟨j, hjT, hj⟩
  rw [hTval] at hj
  have hd : 0 < K - K0 := by rw [hKrepr]; omega
  have hj' : (codeWalk ω j).1 ≤ -((K - K0 : ℕ) : ℤ) := by omega
  obtain ⟨u, hu, huhit⟩ :=
    codeWalk_fst_hits_level_before ω (K - K0) j hd hj'
  have hUleu : (codeFstFirstHit (-((K - K0 : ℕ) : ℤ)) ω).toNat ≤ u :=
    codeFstFirstHit_toNat_le_of_hit ω u huhit
  have hBU := hspan.1
  have hUT := hspan.2.1
  have hgap := hspan.2.2
  omega

/-- Helper toward Proposition 5.16 (`prop-disk-bs-conv`,
out the disk prefix dip; not the paper result. For `K ≥ 1`, `K0 < K`, and
`N ≥ m^100`, a dip implies a bad offset or an incomplete selected chunk. -/
theorem prefix_dip_subset_badLevelChunk
    (m K K0 s o N : ℕ) (ω : ℕ → Fin 3)
    (hmK0 : K0 < m) (_hK : 1 ≤ K) (_hK0K : K0 < K)
    (hom : o < m) (hKrepr : K = s * m + o + 1)
    (hN : m ^ 100 ≤ N) :
    (∃ T : ℕ, codeFstFirstHit (-(K : ℤ)) ω = (T : ℕ∞) ∧
      ∃ j : ℕ, j + N < T ∧
        (codeWalk ω j).1 ≤ (codeWalk ω T).1 + (K0 : ℤ)) →
    o < K0 ∨ (cappedLevelChunk m (m ^ 100) s ω).2 = false := by
  intro hdip
  by_cases hoK0 : o < K0
  · exact Or.inl hoK0
  · right
    have ho : K0 ≤ o := le_of_not_gt hoK0
    cases hbit : (cappedLevelChunk m (m ^ 100) s ω).2 with
    | false => rfl
    | true =>
      obtain ⟨T, hT, j, hjT, hj⟩ := hdip
      have hnot := completeLevelChunk_no_prefix_dip m K K0 s o N T ω hmK0
        ho hom hKrepr hN hbit hT
      exact False.elim (hnot ⟨j, hjT, hj⟩)

end DirectedDistances.RandomWalk
