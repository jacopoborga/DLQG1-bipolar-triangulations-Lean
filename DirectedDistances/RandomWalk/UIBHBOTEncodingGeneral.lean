module

public import DirectedDistances.RandomWalk.UIBHBOTEncodingWalk

/-! # Laws for arbitrary iid UIBHBOT excursion encodings

The finite window law is independent of the probability space used to realize the iid stopped
not paper claims. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private def uibhbotGeneralWordIndex (N : ℕ) (i : Fin (2 * N)) : ℤ :=
  if i.val < N then (i.val : ℤ) else -((i.val - N : ℕ) : ℤ) - 1

private theorem uibhbotGeneralWordIndex_injective (N : ℕ) :
    Function.Injective (uibhbotGeneralWordIndex N) := by
  intro i j hij
  by_cases hi : i.val < N <;> by_cases hj : j.val < N
  · simp [uibhbotGeneralWordIndex, hi, hj] at hij
    exact Fin.ext (by omega)
  · simp [uibhbotGeneralWordIndex, hi, hj] at hij
    exfalso
    omega
  · simp [uibhbotGeneralWordIndex, hi, hj] at hij
    exfalso
    omega
  · simp [uibhbotGeneralWordIndex, hi, hj] at hij
    exact Fin.ext (by omega)

/-- The finite concatenated walk window has the same law for every iid realization of stopped -/
theorem uibhbotConcatWindow_law_of_iid {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → List (Fin 3)) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ)
    (hlaw : ∀ k, μ.map (X k) = excursionWordLaw) (N : ℕ) :
    μ.map (fun ω (j : Fin (2 * N + 1)) =>
      uibhbotConcatWalk (fun k => X k ω) ((j : ℤ) - N)) =
        uibhbotExcursionWindowLaw N := by
  classical
  let coords : Fin (2 * N) → Ω → List (Fin 3) := fun i ω =>
    X (uibhbotGeneralWordIndex N i) ω
  have hcoordsMeas : Measurable (fun ω (i : Fin (2 * N)) => coords i ω) :=
    measurable_pi_iff.mpr fun i => hX (uibhbotGeneralWordIndex N i)
  have hcoordsInd : iIndepFun coords μ := by
    change iIndepFun (fun i => X (uibhbotGeneralWordIndex N i)) μ
    exact hind.precomp (g := uibhbotGeneralWordIndex N)
      (uibhbotGeneralWordIndex_injective N)
  have hcoordsLaw : μ.map (fun ω (i : Fin (2 * N)) => coords i ω) =
      excursionWordProductLaw N := by
    have hmap := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (hX (uibhbotGeneralWordIndex N i)).aemeasurable)).mp hcoordsInd
    calc
      μ.map (fun ω (i : Fin (2 * N)) => coords i ω) =
          Measure.pi (fun i : Fin (2 * N) => μ.map (coords i)) := hmap
      _ = excursionWordProductLaw N := by
        rw [excursionWordProductLaw]
        congr 1
        funext i
        exact hlaw (uibhbotGeneralWordIndex N i)
  have hcoordsNonempty : ∀ᵐ ω ∂μ,
      ∀ i : Fin (2 * N), 1 ≤ (coords i ω).length := by
    rw [ae_all_iff]
    intro i
    have hae := ae_one_le_excursionWord_length
    rw [← hlaw (uibhbotGeneralWordIndex N i)] at hae
    exact (ae_map_iff (hX (uibhbotGeneralWordIndex N i)).aemeasurable
      (measurableSet_le measurable_const
        (measurable_of_countable fun v : List (Fin 3) => v.length))).mp hae
  have hnonempty : ∀ᵐ ω ∂μ,
      ∀ k : ℤ, -(N : ℤ) ≤ k → k < (N : ℤ) → 1 ≤ (X k ω).length := by
    filter_upwards [hcoordsNonempty] with ω hω
    intro k hk₁ hk₂
    by_cases hk : 0 ≤ k
    · let i : Fin (2 * N) := ⟨k.toNat, by omega⟩
      have hik : k.toNat < N := by omega
      have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
      have hindex : uibhbotGeneralWordIndex N i = k := by
        simp [uibhbotGeneralWordIndex, i, hik, hcast]
      simpa [coords, hindex] using hω i
    · have hqnonneg : 0 ≤ -k - 1 := by omega
      let q : ℕ := (-k - 1).toNat
      have hq : (q : ℤ) = -k - 1 := Int.toNat_of_nonneg hqnonneg
      let i : Fin (2 * N) := ⟨N + q, by omega⟩
      have hi : ¬ i.val < N := by dsimp [i]; omega
      have hindex : uibhbotGeneralWordIndex N i = k := by
        simp [uibhbotGeneralWordIndex, i, q]
        omega
      simpa [coords, hindex] using hω i
  have hwindow :
      (fun ω (j : Fin (2 * N + 1)) =>
        uibhbotConcatWalk (fun k => X k ω) ((j : ℤ) - N)) =ᵐ[μ]
      (fun ω j => uibhbotWindowFromWords N
        (fun i : Fin (2 * N) => X (uibhbotGeneralWordIndex N i) ω) j) := by
    filter_upwards [hnonempty] with ω hω
    funext j
    have hwords :
        (fun i : Fin (2 * N) =>
          if i.val < N then X (i.val : ℤ) ω
          else X (-((i.val - N : ℕ) : ℤ) - 1) ω) =
        (fun i : Fin (2 * N) => X (uibhbotGeneralWordIndex N i) ω) := by
      funext i
      by_cases hi : i.val < N <;>
        simp [uibhbotGeneralWordIndex, hi]
    rw [← hwords]
    exact uibhbotConcatWalk_eq_uibhbotWindowFromWords N (fun k => X k ω) hω j
  rw [Measure.map_congr hwindow]
  calc
    μ.map (fun ω (j : Fin (2 * N + 1)) =>
        uibhbotWindowFromWords N
          (fun i : Fin (2 * N) => X (uibhbotGeneralWordIndex N i) ω) j) =
        (μ.map (fun ω (i : Fin (2 * N)) => coords i ω)).map
          (uibhbotWindowFromWords N) := by
      rw [Measure.map_map (measurable_uibhbotWindowFromWords N) hcoordsMeas]
      rfl
    _ = uibhbotExcursionWindowLaw N := by
      rw [hcoordsLaw]
      rfl

/-- The canonical infinite product construction is a special case of the realization independent -/
theorem uibhbotEncodingWindowLaw_eq_uibhbotExcursionWindowLaw_of_iid (N : ℕ) :
    uibhbotEncodingWindowLaw N = uibhbotExcursionWindowLaw N := by
  simpa [uibhbotEncodingWindowLaw] using
    (uibhbotConcatWindow_law_of_iid
      (μ := uibhbotWordFamilyLaw)
      (X := fun k x => x k)
      (hX := measurable_uibhbotWordFamilyEval)
      (hind := iIndepFun_uibhbotWordFamilyEval)
      (hlaw := uibhbotWordFamilyLaw_map_eval) N)

end DirectedDistances.RandomWalk
