module

public import DirectedDistances.Probability.ShiftIndependenceInduction
public import Mathlib.Probability.Independence.InfinitePi

/-! # Independence from two independent sides

Generic probability helpers for the item-Busemann-ind reduction -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- If the nonpositive and positive parts of a two-sided family are each
mutually independent, and the two entire sides are independent, then the
whole family is mutually independent. Generic probability helper for the
a paper theorem. -/
theorem iIndepFun_int_of_two_sides {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℤ → Ω → ℤ}
    (hD : ∀ k, Measurable (D k))
    (hR : iIndepFun (fun n : ℕ => D ((n : ℤ) + 1)) μ)
    (hL : iIndepFun (fun n : ℕ => D (-(n : ℤ))) μ)
    (hLR : IndepFun (fun ω (n : ℕ) => D (-(n : ℤ)) ω)
      (fun ω (n : ℕ) => D ((n : ℤ) + 1) ω) μ) :
    iIndepFun D μ := by
  let X : Bool → ℕ → Ω → ℤ := fun b n =>
    if b then D ((n : ℤ) + 1) else D (-(n : ℤ))
  have hOuter : iIndepFun (fun b : Bool => fun ω n => X b n ω) μ := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hs
    classical
    by_cases hf : false ∈ S <;> by_cases ht : true ∈ S
    · have hS : S = Finset.univ := by
        ext b
        cases b <;> simp [hf, ht]
      subst S
      have hInter : (⋂ i ∈ Finset.univ, (fun ω n => X i n ω) ⁻¹' sets i) =
          (fun ω (n : ℕ) => D (-(n : ℤ)) ω) ⁻¹' sets false ∩
            (fun ω (n : ℕ) => D ((n : ℤ) + 1) ω) ⁻¹' sets true := by
        ext ω
        simp [X]
      rw [hInter]
      calc
        μ ((fun ω (n : ℕ) => D (-(n : ℤ)) ω) ⁻¹' sets false ∩
            (fun ω (n : ℕ) => D ((n : ℤ) + 1) ω) ⁻¹' sets true) =
            μ ((fun ω (n : ℕ) => D (-(n : ℤ)) ω) ⁻¹' sets false) *
              μ ((fun ω (n : ℕ) => D ((n : ℤ) + 1) ω) ⁻¹' sets true) :=
          hLR.measure_inter_preimage_eq_mul (sets false) (sets true)
            (hs false (by simp)) (hs true (by simp))
        _ = ∏ i ∈ Finset.univ, μ ((fun ω n => X i n ω) ⁻¹' sets i) := by
          simp [X, mul_comm]
    · have hS : S = {false} := by
        ext b
        cases b <;> simp [hf, ht]
      subst S
      simp
    · have hS : S = {true} := by
        ext b
        cases b <;> simp [hf, ht]
      subst S
      simp
    · have hS : S = ∅ := by
        ext b
        cases b <;> simp [hf, ht]
      subst S
      simp
  have hInner : ∀ b : Bool, iIndepFun (X b) μ := by
    intro b
    cases b
    · simpa [X] using hL
    · simpa [X] using hR
  have hAll : iIndepFun (fun p : Bool × ℕ => X p.1 p.2) μ :=
    iIndepFun_uncurry' (P := μ) (X := X) (fun b n => by
      dsimp [X]
      split_ifs with hb
      · exact hD ((n : ℤ) + 1)
      · exact hD (-(n : ℤ))) hOuter hInner
  let g : ℤ → Bool × ℕ
    | Int.ofNat 0 => (false, 0)
    | Int.ofNat (n + 1) => (true, n)
    | Int.negSucc n => (false, n + 1)
  let f : Bool × ℕ → ℤ
    | (false, 0) => 0
    | (false, n + 1) => Int.negSucc n
    | (true, n) => Int.ofNat (n + 1)
  have hfg : Function.LeftInverse f g := by
    intro k
    cases k with
    | ofNat n =>
        cases n with
        | zero => simp [f, g]
        | succ n => simp only [g, f]
    | negSucc n => rfl
  have hg_inj : Function.Injective g := hfg.injective
  have hReindex : iIndepFun (fun k : ℤ => X (g k).1 (g k).2) μ :=
    hAll.precomp hg_inj
  have hEq : (fun k : ℤ => X (g k).1 (g k).2) = D := by
    funext k ω
    cases k with
    | ofNat n =>
        cases n with
        | zero => simp [g, X]
        | succ n =>
            simp only [g]
            simp [X]
    | negSucc n =>
        rfl
  exact hReindex.congr fun k => Filter.EventuallyEq.of_eq (congrFun hEq k)

end DirectedDistances.Probability
