module

public import DirectedDistances.Recursive.RightStationaryBusemann
public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.RandomWalk.FutureCodesAtHits

/-! # Right shift structure of the increment process

right-shift structure of the LDP and SDP increment processes. These helpers
are not counted as paper results; F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.RandomWalk MeasureTheory Filter

private theorem codeWalk_snd_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).2 - 1 ≤ (codeWalk ω (n + 1)).2 := by
  have h := congrArg Prod.snd (codeWalk_succ_sub ω n)
  rw [Prod.snd_sub] at h
  let c := ω (n + 1)
  have hs : -1 ≤ (lazyTwoDimensionalStep (ω (n + 1))).2 := by
    change -1 ≤ (lazyTwoDimensionalStep c).2
    unfold lazyTwoDimensionalStep
    split_ifs <;> omega
  omega

private theorem codeWalk_snd_nonneg_before_hit (ω : ℕ → Fin 3)
    (h : ∃ n, (codeWalk ω n).2 = -1) :
    ∀ n < Nat.find h, 0 ≤ (codeWalk ω n).2 := by
  intro n hn
  induction n with
  | zero => simp [codeWalk_zero]
  | succ n ih =>
      have hn' : n < Nat.find h := by omega
      have hprev := ih hn'
      have hstep := codeWalk_snd_succ_ge ω n
      have hnot : (codeWalk ω (n + 1)).2 ≠ -1 :=
        Nat.find_min h (by omega)
      omega

/-- The first hit of level `-k` decomposes at the first hit of `-1` into the
first hit of `-(k - 1)` in the shifted code. Helper toward -/
theorem codeSndFirstHit_right_add (k : ℕ) (hk : 2 ≤ k)
    (ω : ℕ → Fin 3) (hfirst : codeSndFirstHit (-1) ω < ⊤) :
    codeSndFirstHit (-(k : ℤ)) ω =
      codeSndFirstHit (-1) ω +
        codeSndFirstHit (-((k - 1 : ℕ) : ℤ))
          (codeShift (codeSndFirstHit (-1) ω).toNat ω) := by
  classical
  let h₁ : ∃ n, (codeWalk ω n).2 = -1 := by
    by_contra hn
    have htop : codeSndFirstHit (-1) ω = ⊤ := by
      simp [codeSndFirstHit, hn]
    exact (ne_of_lt hfirst) htop
  let t : ℕ := Nat.find h₁
  have htval : (codeWalk ω t).2 = -1 := Nat.find_spec h₁
  have htfirst : codeSndFirstHit (-1) ω = (t : ℕ∞) := by
    simp [codeSndFirstHit, h₁, t]
  have htnat : (codeSndFirstHit (-1) ω).toNat = t := by
    rw [htfirst]
    rfl
  have hshift (m : ℕ) :
      (codeWalk (codeShift t ω) m).2 = (codeWalk ω (t + m)).2 + 1 := by
    rw [codeWalk_codeShift, Prod.snd_sub, htval]
    omega
  have hhit (m : ℕ) :
      (codeWalk (codeShift t ω) m).2 = -((k - 1 : ℕ) : ℤ) ↔
        (codeWalk ω (t + m)).2 = -(k : ℤ) := by
    rw [hshift]
    omega
  have htime_le (n : ℕ) (hn : (codeWalk ω n).2 = -(k : ℤ)) : t ≤ n := by
    by_contra htn
    have hnonneg := codeWalk_snd_nonneg_before_hit ω h₁ n (by omega)
    omega
  by_cases hK : ∃ n, (codeWalk ω n).2 = -(k : ℤ)
  · have hQ : ∃ m, (codeWalk (codeShift t ω) m).2 =
        -((k - 1 : ℕ) : ℤ) := by
      obtain ⟨n, hn⟩ := hK
      have htn := htime_le n hn
      refine ⟨n - t, ?_⟩
      have heq : t + (n - t) = n := by omega
      have hn' : (codeWalk ω (t + (n - t))).2 = -(k : ℤ) := by
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
        have hqval : (codeWalk (codeShift t ω) m).2 =
            -((k - 1 : ℕ) : ℤ) := by
          apply (hhit m).2
          simpa [heq] using hnval
        have hqle := Nat.find_min' hQ hqval
        dsimp [m] at hqle
        omega
    have hleft : codeSndFirstHit (-(k : ℤ)) ω = (Nat.find hK : ℕ∞) := by
      simp [codeSndFirstHit, hK]
    have hright : codeSndFirstHit (-((k - 1 : ℕ) : ℤ))
        (codeShift t ω) = (Nat.find hQ : ℕ∞) := by
      simp [codeSndFirstHit, hQ]
    rw [htfirst]
    change codeSndFirstHit (-(k : ℤ)) ω = (t : ℕ∞) +
      codeSndFirstHit (-((k - 1 : ℕ) : ℤ)) (codeShift t ω)
    rw [hleft, hright, hfind]
    simp [Nat.cast_add]
  · have hQ : ¬ ∃ m, (codeWalk (codeShift t ω) m).2 =
        -((k - 1 : ℕ) : ℤ) := by
      intro hq
      obtain ⟨m, hm⟩ := hq
      exact hK ⟨t + m, (hhit m).1 hm⟩
    have hleft : codeSndFirstHit (-(k : ℤ)) ω = ⊤ := by
      simp [codeSndFirstHit, hK]
    have hright : codeSndFirstHit (-((k - 1 : ℕ) : ℤ))
        (codeShift t ω) = ⊤ := by
      simp [codeSndFirstHit, hQ]
    rw [htfirst]
    change codeSndFirstHit (-(k : ℤ)) ω = (t : ℕ∞) +
      codeSndFirstHit (-((k - 1 : ℕ) : ℤ)) (codeShift t ω)
    rw [hleft, hright]
    simp

/-- The reset shift composition identity, with chronological shifts composed
in the order shown. Helper toward `item-busemann-ind` -/
theorem codeShift_comp (a b : ℕ) (ω : ℕ → Fin 3) :
    codeShift a (codeShift b ω) = codeShift (b + a) ω := by
  funext i
  by_cases hi : i = 0
  · simp [codeShift, hi]
  · simp [codeShift, hi, add_assoc]

/-- A full-measure property transfers to the code sequence at a second
coordinate first hit. Helper toward `item-busemann-ind` -/
theorem ae_comp_rightHit (a : ℤ) {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂iidCodeMeasure,
      p (codeShift (codeSndFirstHit a ω).toNat ω) := by
  apply ae_of_ae_map
    (measurable_codeShift_toNat _ (measurableSet_codePast_codeSndFirstHit_eq a)).aemeasurable
  rw [map_codeShift_codeSndFirstHit]
  exact hp

private theorem right_increment_shift_of_value_shift
    (V : (ℕ → Fin 3) → ℤ → ℤ)
    (inc : ℤ → (ℕ → Fin 3) → ℤ)
    (hinc : ∀ k ω, inc k ω = V ω k - V ω (k - 1))
    (hzero : ∀ ω, V ω 0 = 0)
    (hshift : ∀ k : ℕ, 1 ≤ k → ∀ᵐ ω ∂iidCodeMeasure,
      V (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 1 =
        V ω ((k : ℤ) + 1) - V ω (k : ℤ)) :
    ∀ j : ℕ, 1 ≤ j → ∀ᵐ ω ∂iidCodeMeasure,
      inc ((j : ℤ) + 1) ω =
        inc (j : ℤ) (codeShift (codeSndFirstHit (-1) ω).toNat ω) := by
  intro j hj
  by_cases hj1 : j = 1
  · subst j
    filter_upwards [hshift 1 (by omega)] with ω hs
    let θ := codeShift (codeSndFirstHit (-1) ω).toNat ω
    have hz := hzero θ
    have hs' : V θ 1 = V ω 2 - V ω 1 := by
      simpa using hs
    calc
      inc 2 ω = V ω 2 - V ω 1 := by rw [hinc]; norm_num
      _ = V θ 1 - V θ 0 := by rw [hz, sub_zero, hs'.symm]
      _ = inc 1 θ := by rw [hinc]; norm_num
  · have hj2 : 2 ≤ j := by omega
    have hjm : 1 ≤ j - 1 := by omega
    have hsJ := hshift j (by omega)
    have hsQ := ae_comp_rightHit (-1) (hshift (j - 1) hjm)
    have hfinite1 := ae_codeSndFirstHit_lt_top_int (-1)
    have hfiniteQ := ae_comp_rightHit (-1)
      (ae_codeSndFirstHit_lt_top_int (-((j - 1 : ℕ) : ℤ)))
    filter_upwards [hsJ, hsQ, hfinite1, hfiniteQ] with ω hJ hQ hf1 hfQ
    let τ₁ := codeSndFirstHit (-1) ω
    let θ := codeShift τ₁.toNat ω
    let τQ := codeSndFirstHit (-((j - 1 : ℕ) : ℤ)) θ
    let τJ := codeSndFirstHit (-(j : ℤ)) ω
    have hadd : τJ = τ₁ + τQ := by
      dsimp [τJ, τ₁, τQ, θ]
      exact codeSndFirstHit_right_add j hj2 ω hf1
    have hnatadd : τJ.toNat = τ₁.toNat + τQ.toNat := by
      rw [hadd]
      exact ENat.toNat_add (ne_of_lt hf1) (ne_of_lt hfQ)
    have hcomp : codeShift τQ.toNat (codeShift τ₁.toNat ω) =
        codeShift τJ.toNat ω := by
      calc
        codeShift τQ.toNat (codeShift τ₁.toNat ω) =
            codeShift (τ₁.toNat + τQ.toNat) ω := codeShift_comp _ _ _
        _ = codeShift τJ.toNat ω := by rw [← hnatadd]
    have hQ' : V (codeShift τJ.toNat ω) 1 =
        V θ (((j - 1 : ℕ) : ℤ) + 1) - V θ ((j - 1 : ℕ) : ℤ) := by
      change V (codeShift τQ.toNat θ) 1 = _ at hQ
      rw [hcomp] at hQ
      exact hQ
    calc
      inc ((j : ℤ) + 1) ω = V ω ((j : ℤ) + 1) - V ω (j : ℤ) := by
        rw [hinc]
        rw [show ((j : ℤ) + 1) - 1 = (j : ℤ) by omega]
      _ = V (codeShift τJ.toNat ω) 1 := hJ.symm
      _ = inc (j : ℤ) θ := by
        rw [hinc]
        have hc₁ : ((j - 1 : ℕ) : ℤ) + 1 = (j : ℤ) := by omega
        have hc₀ : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        simpa only [hc₁, hc₀, Int.sub_add_cancel] using hQ'

/-- The LDP increment at `j + 1` is the increment at `j` after the first
right shift. Helper toward `item-busemann-ind` -/
theorem busemannLDPMeasurableVersion_right_increment_shift :
    ∀ j : ℕ, 1 ≤ j → ∀ᵐ ω ∂iidCodeMeasure,
      ldpIncrement busemannLDPMeasurableVersion ((j : ℤ) + 1) ω =
        ldpIncrement busemannLDPMeasurableVersion (j : ℤ)
          (codeShift (codeSndFirstHit (-1) ω).toNat ω) :=
  right_increment_shift_of_value_shift busemannLDPMeasurableVersion
    (ldpIncrement busemannLDPMeasurableVersion) (by intro k ω; rfl)
    busemannLDPMeasurableVersion_zero
    busemannLDPMeasurableVersion_right_shift_identity

/-- The SDP increment at `j + 1` is the increment at `j` after the first
right shift. Helper toward `item-busemann-ind` -/
theorem busemannSDPMeasurableVersion_right_increment_shift :
    ∀ j : ℕ, 1 ≤ j → ∀ᵐ ω ∂iidCodeMeasure,
      SDPMasterFromLaw.increment busemannSDPMeasurableVersion ((j : ℤ) + 1) ω =
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion (j : ℤ)
          (codeShift (codeSndFirstHit (-1) ω).toNat ω) :=
  right_increment_shift_of_value_shift busemannSDPMeasurableVersion
    (SDPMasterFromLaw.increment busemannSDPMeasurableVersion) (by intro k ω; rfl)
    busemannSDPMeasurableVersion_zero
    busemannSDPMeasurableVersion_right_shift_identity

end DirectedDistances.Recursive
