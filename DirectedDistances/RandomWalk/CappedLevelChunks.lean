module

public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.RandomWalk.FutureCodesAtHits
public import DirectedDistances.RandomWalk.IIDCodeRelabel
public import DirectedDistances.Probability.FrontierIndependence
public import DirectedDistances.Probability.ShiftIndependenceInduction

/-! # Capped level chunks

Finite code records cut off at first-coordinate level hits, for the iid chunk
decomposition in Lemma `lem-disk-walk-conv` -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory

/-- The first-coordinate level-`m` segment, truncated at `C` codes and padded
with zero codes, together with the bit recording whether the level was hit by
the cap. This is the finite observable for the iid capped level chunks in
`lem-disk-walk-conv` (`eqn-cramer-increment`, -/
@[expose] noncomputable def chunk (m C : ℕ) (ω : ℕ → Fin 3) :
    (Fin C → Fin 3) × Bool :=
  (fun i => if i.val < (codeFstFirstHit (-(m : ℤ)) ω).toNat
    then ω (i.val + 1) else 0,
    if codeFstFirstHit (-(m : ℤ)) ω ≤ C then true else false)

private theorem measurable_codeFstFirstHit (a : ℤ) :
    Measurable (codeFstFirstHit a) := by
  rw [ENat.measurable_iff]
  intro k
  exact codePast_le k _ (measurableSet_codePast_codeFstFirstHit_eq a k)

/-- Every capped chunk is a measurable finite-valued observable. Helper for
`lem-disk-walk-conv` (`eqn-cramer-increment`, -/
theorem measurable_chunk (m C : ℕ) : Measurable (chunk m C) := by
  classical
  let τ := codeFstFirstHit (-(m : ℤ))
  have hτ : Measurable τ := measurable_codeFstFirstHit _
  have hτN : Measurable (fun ω => (τ ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp hτ
  have hcodes : Measurable (fun ω : ℕ → Fin 3 =>
      fun i : Fin C => if i.val < (τ ω).toNat then ω (i.val + 1) else 0) := by
    refine measurable_pi_iff.mpr fun i => ?_
    have he : MeasurableSet {ω : ℕ → Fin 3 | i.val < (τ ω).toNat} :=
      measurableSet_lt measurable_const hτN
    exact Measurable.ite he (measurable_pi_apply (i.val + 1)) measurable_const
  have hbit : Measurable (fun ω : ℕ → Fin 3 => if τ ω ≤ C then true else false) := by
    have heq : {ω : ℕ → Fin 3 | τ ω ≤ C} =
        ⋃ k : Fin (C + 1), {ω | τ ω = k.val} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        cases ht : τ ω with
        | top => simp [ht] at h
        | coe n =>
          have hn : n ≤ C := by
            have := h
            rw [ht] at this
            exact ENat.natCast_le_natCast.mp this
          exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, by simpa using ht⟩
      · rintro ⟨k, hk⟩
        rw [hk]
        exact ENat.natCast_le_natCast.mpr (by omega)
    have he : MeasurableSet {ω : ℕ → Fin 3 | τ ω ≤ C} := by
      rw [heq]
      exact MeasurableSet.iUnion fun k => by
        have hs : MeasurableSet (τ ⁻¹' ({(k.val : ℕ∞)} : Set ℕ∞)) :=
          hτ (measurableSet_singleton (k.val : ℕ∞))
        simpa only [Set.preimage, Set.mem_singleton_iff] using hs
    exact Measurable.ite he measurable_const measurable_const
  change Measurable (fun ω => (fun i : Fin C =>
    if i.val < (τ ω).toNat then ω (i.val + 1) else 0,
    if τ ω ≤ C then true else false))
  exact hcodes.prodMk hbit

private theorem codeWalk_fst_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).1 - 1 ≤ (codeWalk ω (n + 1)).1 := by
  have h := congrArg Prod.fst (codeWalk_succ_sub ω n)
  rw [Prod.fst_sub] at h
  have hsAll : ∀ c : Fin 3, -1 ≤ (lazyTwoDimensionalStep c).1 := by
    intro c
    fin_cases c <;> decide
  have hs := hsAll (ω (n + 1))
  omega

private theorem codeWalk_fst_gt_before_hit (ω : ℕ → Fin 3) {a : ℕ}
    (ha : 0 < a) (h : ∃ n, (codeWalk ω n).1 = -(a : ℤ)) :
    ∀ n < Nat.find h, -(a : ℤ) < (codeWalk ω n).1 := by
  intro n hn
  induction n with
  | zero => simp [codeWalk_zero]; omega
  | succ n ih =>
    have hn' : n < Nat.find h := by omega
    have hprev := ih hn'
    have hstep := codeWalk_fst_succ_ge ω n
    have hnot : (codeWalk ω (n + 1)).1 ≠ -(a : ℤ) :=
      Nat.find_min h (by omega)
    omega

/-- First-passage additivity for first-coordinate levels. If the initial level
`-a` is hit, the first hit of `-(a+b)` is the hit of `-a` followed by the
first `-b` hit in the shifted path. Helper for the iid capped level chunks in
`lem-disk-walk-conv` (`eqn-cramer-increment`, -/
theorem codeFstFirstHit_add (a b : ℕ) (ha : 0 < a) (ω : ℕ → Fin 3)
    (hfirst : codeFstFirstHit (-(a : ℤ)) ω < ⊤) :
    codeFstFirstHit (-((a + b : ℕ) : ℤ)) ω =
      codeFstFirstHit (-(a : ℤ)) ω +
        codeFstFirstHit (-(b : ℤ))
          (codeShift (codeFstFirstHit (-(a : ℤ)) ω).toNat ω) := by
  classical
  let h₁ : ∃ n, (codeWalk ω n).1 = -(a : ℤ) := by
    by_contra hn
    have htop : codeFstFirstHit (-(a : ℤ)) ω = ⊤ := by
      simp [codeFstFirstHit, hn]
    exact (ne_of_lt hfirst) htop
  let t : ℕ := Nat.find h₁
  have htval : (codeWalk ω t).1 = -(a : ℤ) := Nat.find_spec h₁
  have htfirst : codeFstFirstHit (-(a : ℤ)) ω = (t : ℕ∞) := by
    simp [codeFstFirstHit, h₁, t]
  have htnat : (codeFstFirstHit (-(a : ℤ)) ω).toNat = t := by
    rw [htfirst]
    rfl
  have hshift (m : ℕ) :
      (codeWalk (codeShift t ω) m).1 = (codeWalk ω (t + m)).1 + a := by
    rw [codeWalk_codeShift, Prod.fst_sub, htval]
    simp

  have hhit (m : ℕ) :
      (codeWalk (codeShift t ω) m).1 = -(b : ℤ) ↔
        (codeWalk ω (t + m)).1 = -((a + b : ℕ) : ℤ) := by
    rw [hshift]
    simp only [Nat.cast_add]
    omega
  have htime_le (n : ℕ) (hn : (codeWalk ω n).1 = -((a + b : ℕ) : ℤ)) :
      t ≤ n := by
    by_contra htn
    have hbefore := codeWalk_fst_gt_before_hit ω ha h₁ n (by omega)
    omega
  by_cases hK : ∃ n, (codeWalk ω n).1 = -((a + b : ℕ) : ℤ)
  · have hQ : ∃ m, (codeWalk (codeShift t ω) m).1 = -(b : ℤ) := by
      obtain ⟨n, hn⟩ := hK
      have htn := htime_le n hn
      refine ⟨n - t, ?_⟩
      have heq : t + (n - t) = n := by omega
      have hn' : (codeWalk ω (t + (n - t))).1 = -((a + b : ℕ) : ℤ) := by
        simpa [heq] using hn
      exact (hhit (n - t)).2 hn'
    have hfind : Nat.find hK = t + Nat.find hQ := by
      apply (Nat.find_eq_iff hK).2
      constructor
      · exact (hhit (Nat.find hQ)).1 (Nat.find_spec hQ)
      · intro n hnlt hnval
        have htn := htime_le n hnval
        let m := n - t
        have heq : t + m = n := by dsimp [m]; omega
        have hqval : (codeWalk (codeShift t ω) m).1 = -(b : ℤ) := by
          apply (hhit m).2
          simpa [heq] using hnval
        have hqle := Nat.find_min' hQ hqval
        dsimp [m] at hqle
        omega
    have hleft : codeFstFirstHit (-((a + b : ℕ) : ℤ)) ω =
        (Nat.find hK : ℕ∞) := by
      simp only [codeFstFirstHit, dif_pos hK]
    have hright : codeFstFirstHit (-(b : ℤ)) (codeShift t ω) =
        (Nat.find hQ : ℕ∞) := by
      simp only [codeFstFirstHit, dif_pos hQ]
    rw [htfirst]
    change codeFstFirstHit (-((a + b : ℕ) : ℤ)) ω = (t : ℕ∞) +
      codeFstFirstHit (-(b : ℤ)) (codeShift t ω)
    rw [hleft, hright, hfind]
    simp [Nat.cast_add]
  · have hQ : ¬ ∃ m, (codeWalk (codeShift t ω) m).1 = -(b : ℤ) := by
      intro hq
      obtain ⟨m, hm⟩ := hq
      exact hK ⟨t + m, (hhit m).1 hm⟩
    have hleft : codeFstFirstHit (-((a + b : ℕ) : ℤ)) ω = ⊤ := by
      simp only [codeFstFirstHit, dif_neg hK]
    have hright : codeFstFirstHit (-(b : ℤ)) (codeShift t ω) = ⊤ := by
      simp only [codeFstFirstHit, dif_neg hQ]
    rw [htfirst]
    change codeFstFirstHit (-((a + b : ℕ) : ℤ)) ω = (t : ℕ∞) +
      codeFstFirstHit (-(b : ℤ)) (codeShift t ω)
    rw [hleft, hright]
    simp

/-- First-passage additivity at arbitrary nonzero first-coordinate levels,
almost surely for iid codes. -/
theorem ae_codeFstFirstHit_add (a b : ℕ) (ha : 0 < a) :
    ∀ᵐ ω ∂iidCodeMeasure,
      codeFstFirstHit (-((a + b : ℕ) : ℤ)) ω =
        codeFstFirstHit (-(a : ℤ)) ω +
          codeFstFirstHit (-(b : ℤ))
            (codeShift (codeFstFirstHit (-(a : ℤ)) ω).toNat ω) := by
  filter_upwards [ae_codeFstFirstHit_lt_top_int (-(a : ℤ))] with ω hω
  exact codeFstFirstHit_add a b ha ω hω

@[simp] private theorem codeFstFirstHit_zero (ω : ℕ → Fin 3) :
    codeFstFirstHit 0 ω = 0 := by
  classical
  unfold codeFstFirstHit
  let h : ∃ n, (codeWalk ω n).1 = 0 := ⟨0, by simp [codeWalk_zero]⟩
  rw [dif_pos h]
  have hf : Nat.find h = 0 := by
    apply (Nat.find_eq_iff h).2
    constructor
    · simp [codeWalk_zero]
    · intro n hn
      omega
  simp [hf]

private theorem codeFstFirstHit_codeShift_zero (a : ℤ) (ω : ℕ → Fin 3) :
    codeFstFirstHit a (codeShift 0 ω) = codeFstFirstHit a ω := by
  have hwalk : codeWalk (codeShift 0 ω) = codeWalk ω := by
    funext n
    rw [codeWalk_codeShift]
    simp [codeWalk_zero]
  unfold codeFstFirstHit
  rw [hwalk]

private theorem codeShift_comp' (a b : ℕ) (ω : ℕ → Fin 3) :
    codeShift a (codeShift b ω) = codeShift (b + a) ω := by
  funext i
  by_cases hi : i = 0
  · simp [codeShift, hi]
  · simp [codeShift, hi, add_assoc]

/-- The first-passage decomposition at consecutive level blocks holds almost
surely under the iid code law. Helper for `lem-disk-walk-conv`
as a paper result. -/
theorem ae_codeFstFirstHit_block_add (m s : ℕ) (hm : 0 < m) (hs : 1 ≤ s) :
    ∀ᵐ ω ∂iidCodeMeasure,
      codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω =
        codeFstFirstHit (-(((s - 1) * m : ℕ) : ℤ)) ω +
          codeFstFirstHit (-(m : ℤ))
            (codeShift (codeFstFirstHit (-(((s - 1) * m : ℕ) : ℤ)) ω).toNat ω) := by
  have hfin := ae_codeFstFirstHit_lt_top_int (-(((s - 1) * m : ℕ) : ℤ))
  filter_upwards [hfin] with ω hω
  by_cases ha : (s - 1) * m = 0
  · have hs1 : s = 1 := by
      rcases Nat.mul_eq_zero.mp ha with hsub | hmzero
      · omega
      · omega
    subst s
    simp [codeFstFirstHit_zero, codeFstFirstHit_codeShift_zero]
  · have hap : 0 < (s - 1) * m := Nat.pos_iff_ne_zero.mpr ha
    have hadd := codeFstFirstHit_add ((s - 1) * m) m hap ω hω
    have hsigma : s * m = (s - 1) * m + m := by
      calc
        s * m = ((s - 1) + 1) * m := by
          congr 1
          omega
        _ = (s - 1) * m + 1 * m := Nat.add_mul _ _ _
        _ = (s - 1) * m + m := by simp
    simpa [hsigma] using hadd

/-- The observable block started at level `s*m`, with a finite cap. It is the
first-coordinate path segment from `σ_(s*m)` to `σ_((s+1)*m)`, recorded with
the completion bit. Helper for `lem-disk-walk-conv` (`eqn-cramer-increment`, -/
@[expose] noncomputable def cappedLevelChunk (m C s : ℕ)
    (ω : ℕ → Fin 3) : (Fin C → Fin 3) × Bool :=
  chunk m C (codeShift (codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω).toNat ω)

/-- Measurability of each level block. Helper for `lem-disk-walk-conv` -/
theorem measurable_cappedLevelChunk (m C s : ℕ) :
    Measurable (cappedLevelChunk m C s) := by
  apply (measurable_chunk m C).comp
  exact measurable_codeShift_toNat _
    (measurableSet_codePast_codeFstFirstHit_eq (-((s * m : ℕ) : ℤ)))

/-- Every capped block has the same law as the initial chunk. Helper for
`lem-disk-walk-conv` (`eqn-cramer-increment`, -/
theorem map_cappedLevelChunk (m C s : ℕ) :
    iidCodeMeasure.map (cappedLevelChunk m C s) = iidCodeMeasure.map (chunk m C) := by
  exact map_comp_codeShift_toNat _
    (measurableSet_codePast_codeFstFirstHit_eq (-((s * m : ℕ) : ℤ)))
    (ae_codeFstFirstHit_lt_top_int (-((s * m : ℕ) : ℤ))) (measurable_chunk m C)

private theorem ae_cappedLevelChunk_shift (m C s : ℕ) (hm : 0 < m) :
    ∀ᵐ ω ∂iidCodeMeasure,
      cappedLevelChunk m C (s + 1) ω =
        cappedLevelChunk m C s
          (codeShift (codeFstFirstHit (-(m : ℤ)) ω).toNat ω) := by
  have hadd := ae_codeFstFirstHit_add m (s * m) hm
  have hbase := ae_codeFstFirstHit_lt_top_int (-(m : ℤ))
  have hfuture : ∀ᵐ ω ∂iidCodeMeasure,
      codeFstFirstHit (-((s * m : ℕ) : ℤ))
        (codeShift (codeFstFirstHit (-(m : ℤ)) ω).toNat ω) < ⊤ := by
    have hp : ∀ᵐ y ∂iidCodeMeasure.map
        (fun ω => codeShift (codeFstFirstHit (-(m : ℤ)) ω).toNat ω),
        codeFstFirstHit (-((s * m : ℕ) : ℤ)) y < ⊤ := by
      rw [map_codeShift_codeFstFirstHit]
      exact ae_codeFstFirstHit_lt_top_int (-((s * m : ℕ) : ℤ))
    exact ae_of_ae_map (μ := iidCodeMeasure)
      (measurable_codeShift_toNat _
        (measurableSet_codePast_codeFstFirstHit_eq (-(m : ℤ)))).aemeasurable hp
  filter_upwards [hadd, hbase, hfuture] with ω hadd hb hf
  let τ := codeFstFirstHit (-(m : ℤ)) ω
  let υ := codeFstFirstHit (-((s * m : ℕ) : ℤ)) (codeShift τ.toNat ω)
  have hidx : m + s * m = (s + 1) * m := by
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  have hdecomp : codeFstFirstHit (-(((s + 1) * m : ℕ) : ℤ)) ω = τ + υ := by
    dsimp [τ, υ]
    simpa [hidx] using hadd
  cases ht : τ with
  | top => simp [τ, ht] at hb
  | coe t =>
    cases hu : υ with
    | top =>
      have hf' : codeFstFirstHit (-((s * m : ℕ) : ℤ))
          (codeShift t ω) < ⊤ := by simpa [τ, ht] using hf
      have hu' : codeFstFirstHit (-((s * m : ℕ) : ℤ))
          (codeShift t ω) = ⊤ := by simpa [υ, τ, ht] using hu
      rw [hu'] at hf'
      simp at hf'
    | coe u =>
      have htime :
          (codeFstFirstHit (-(((s + 1) * m : ℕ) : ℤ)) ω).toNat = t + u := by
        rw [hdecomp, ht, hu]
        rfl
      change chunk m C
          (codeShift (codeFstFirstHit (-(((s + 1) * m : ℕ) : ℤ)) ω).toNat ω) =
        chunk m C (codeShift υ.toNat (codeShift τ.toNat ω))
      rw [htime, ht, hu]
      exact congrArg (chunk m C) (codeShift_comp' u t ω).symm

private def frontierChunk (C k : ℕ) (p : ℕ → Fin 3) :
    (Fin C → Fin 3) × Bool :=
  (fun i => if i.val < k then p i.val else 0,
    if k ≤ C then true else false)

private theorem measurable_frontierChunk_uncurry (C k : ℕ) :
    Measurable (Function.uncurry
      (fun (p : ℕ → Fin 3) (_ : Unit) => frontierChunk C k p)) := by
  change Measurable (fun z : (ℕ → Fin 3) × Unit => frontierChunk C k z.1)
  have hcodes : Measurable (fun z : (ℕ → Fin 3) × Unit =>
      fun i : Fin C => if i.val < k then z.1 i.val else 0) := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases hi : i.val < k
    · have h : Measurable (fun z : (ℕ → Fin 3) × Unit => z.1 i.val) :=
        (measurable_pi_apply i.val).comp measurable_fst
      simpa only [if_pos hi] using h
    · simp [frontierChunk, hi]
  have hbit : Measurable (fun _ : (ℕ → Fin 3) × Unit =>
      if k ≤ C then true else false) := measurable_const
  exact hcodes.prodMk hbit

private theorem ae_chunk_eq_frontier (m C : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      chunk m C ω = frontierChunk C (codeFstFirstHit (-(m : ℤ)) ω).toNat
        (Probability.codePastVector (codeFstFirstHit (-(m : ℤ))) ω) := by
  filter_upwards [ae_codeFstFirstHit_lt_top_int (-(m : ℤ))] with ω hfin
  cases ht : codeFstFirstHit (-(m : ℤ)) ω with
  | top => simp [ht] at hfin
  | coe k =>
    apply Prod.ext
    · funext i
      by_cases hi : i.val < k
      · simp [chunk, frontierChunk, Probability.codePastVector, ht, hi]
      · simp [chunk, frontierChunk, Probability.codePastVector, ht, hi]
    · by_cases hk : k ≤ C <;> simp [chunk, frontierChunk, ht, hk]

/-- The sequence of capped level blocks for `lem-disk-walk-conv` -/
@[expose] noncomputable def cappedLevelChunks (m C s : ℕ)
    (ω : ℕ → Fin 3) : (Fin C → Fin 3) × Bool := cappedLevelChunk m C s ω

/-- The capped level chunk sequence is independent, with each marginal equal
to the initial chunk law. This is the iid finite-path assertion in
`lem-disk-walk-conv` (`eqn-cramer-increment`, -/
theorem iIndepFun_cappedLevelChunks (m C : ℕ) (hm : 0 < m) :
    iIndepFun (fun s ω => cappedLevelChunks m C s ω) iidCodeMeasure := by
  classical
  let α := (Fin C → Fin 3) × Bool
  let D : ℕ → (ℕ → Fin 3) → α := fun s => cappedLevelChunks m C s
  let τ : (ℕ → Fin 3) → ℕ∞ := codeFstFirstHit (-(m : ℤ))
  let T : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω => codeShift (τ ω).toNat ω
  have hτ : ∀ k : ℕ, MeasurableSet[codePast k] {ω | τ ω = k} :=
    measurableSet_codePast_codeFstFirstHit_eq (-(m : ℤ))
  have hfin : ∀ᵐ ω ∂iidCodeMeasure, τ ω < ⊤ :=
    ae_codeFstFirstHit_lt_top_int (-(m : ℤ))
  have hTm : Measurable T := measurable_codeShift_toNat τ hτ
  have hT : MeasurePreserving T iidCodeMeasure iidCodeMeasure := by
    exact ⟨hTm, map_codeShift_codeFstFirstHit (-(m : ℤ))⟩
  have hD : ∀ s, Measurable (D s) := by
    intro s
    exact measurable_cappedLevelChunk m C s
  have hshift : ∀ s, D (s + 1) =ᵐ[iidCodeMeasure] (D s ∘ T) := by
    intro s
    exact ae_cappedLevelChunk_shift m C s hm
  let H : (ℕ → Fin 3) → ℕ → α := fun ω s => D s ω
  have hH : Measurable H := measurable_pi_iff.mpr fun s => hD s
  let G : (ℕ → Fin 3) → Unit := fun _ => ()
  let F : ℕ → (ℕ → Fin 3) → Unit → α := fun k p _ => frontierChunk C k p
  have hF : ∀ k, Measurable (Function.uncurry (F k)) := by
    intro k
    exact measurable_frontierChunk_uncurry C k
  have hfront : ∀ᵐ ω ∂iidCodeMeasure,
      D 0 ω = F (τ ω).toNat (Probability.codePastVector τ ω) (G (T ω)) := by
    filter_upwards [ae_chunk_eq_frontier m C] with ω hω
    have hstart : D 0 ω = chunk m C ω := by
      simp [D, cappedLevelChunks, cappedLevelChunk, codeFstFirstHit_zero,
        codeFstFirstHit_codeShift_zero, chunk, codeShift]
    simpa [D, F, G, T, τ] using hstart.trans hω
  have hheadFront := DirectedDistances.Probability.indepFun_frontier_of_strongMarkov
    τ hτ hfin measurable_const hH (indepFun_const_left () H) F hF
  have hfrontEq : (D 0) =ᵐ[iidCodeMeasure]
      (fun ω => F (τ ω).toNat (Probability.codePastVector τ ω) (G (T ω))) := by
    filter_upwards [hfront] with ω hω
    exact hω
  have htail : (fun ω s => H (T ω) s) =ᵐ[iidCodeMeasure]
      (fun ω s => D (s + 1) ω) := by
    have hall : ∀ᵐ ω ∂iidCodeMeasure, ∀ s, D (s + 1) ω = D s (T ω) :=
      ae_all_iff.mpr hshift
    filter_upwards [hall] with ω hω
    funext s
    exact (hω s).symm
  have hhead : IndepFun (D 0) (fun ω s => D (s + 1) ω) iidCodeMeasure :=
    hheadFront.congr hfrontEq.symm htail
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let enc : α → ℤ := fun x => (e x).val
  let dec : ℤ → α := fun z =>
    if hz : z.toNat < Fintype.card α then e.symm ⟨z.toNat, hz⟩ else default
  have henc : Measurable enc := measurable_of_countable enc
  have hdec : Measurable dec := measurable_of_countable dec
  have hdecode : ∀ x : α, dec (enc x) = x := by
    intro x
    simp [dec, enc]
  let E : ℕ → (ℕ → Fin 3) → ℤ := fun s ω => enc (D s ω)
  have hE : ∀ s, Measurable (E s) := fun s => henc.comp (hD s)
  have hEshift : ∀ s, E (s + 1) =ᵐ[iidCodeMeasure] (E s ∘ T) := by
    intro s
    filter_upwards [hshift s] with ω hω
    exact congrArg enc hω
  have htailMeas : Measurable (fun z : (ℕ → α) => fun s => enc (z s)) :=
    measurable_pi_iff.mpr fun s => henc.comp (measurable_pi_apply s)
  have hheadE : IndepFun (E 0) (fun ω s => E (s + 1) ω) iidCodeMeasure := by
    have := hhead.comp henc htailMeas
    exact this
  have hEind : iIndepFun E iidCodeMeasure :=
    DirectedDistances.Probability.iIndepFun_of_head_indep_tail_of_shift
      hT hE hEshift hheadE
  have hDind : iIndepFun D iidCodeMeasure := by
    have h := hEind.comp (fun _ => dec) (fun _ => hdec)
    apply h.congr
    intro s
    filter_upwards with ω
    exact hdecode (D s ω)
  change iIndepFun D iidCodeMeasure
  exact hDind

end DirectedDistances.RandomWalk
