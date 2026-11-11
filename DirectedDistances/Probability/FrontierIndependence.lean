module

public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.RandomWalk.FutureCodesAtHits

/-! # Independence at the frontier of a stopping time

Generic probability helpers for the item–Busemann independence reduction -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open Function
open DirectedDistances.RandomWalk

/-- The stopped past as a code sequence, with zeroes after the stopping frontier. -/
@[expose] def codePastVector (τ : (ℕ → Fin 3) → ℕ∞) (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => if ((i : ℕ) : ℕ∞) < τ ω then ω (i + 1) else 0

private def extendCodePrefix (k : ℕ) (p : Fin k → Fin 3) : ℕ → Fin 3 :=
  fun i => if h : i < k then p ⟨i, h⟩ else 0

private def codePrefix (k : ℕ) (ω : ℕ → Fin 3) : Fin k → Fin 3 :=
  fun j => ω (j.val + 1)

private theorem codePastVector_eq_prefix (τ : (ℕ → Fin 3) → ℕ∞) (k : ℕ)
    (ω : ℕ → Fin 3) (hω : τ ω = k) :
    codePastVector τ ω = extendCodePrefix k (codePrefix k ω) := by
  funext i
  by_cases hi : i < k
  · simp [codePastVector, hω, extendCodePrefix, codePrefix, hi]
  · simp [codePastVector, hω, extendCodePrefix, hi]

private theorem extendCodePrefix_injective (k : ℕ) :
    Function.Injective (extendCodePrefix k) := by
  intro p q hpq
  funext j
  have := congrFun hpq j.val
  simpa [extendCodePrefix, j.isLt] using this

/-- The code sequence after a measurable a.s. finite stopping time has the iid code law. -/
theorem map_comp_codeShift_stoppingTime (τ : (ℕ → Fin 3) → ℕ∞)
    (hτ : ∀ k : ℕ, MeasurableSet[codePast k] {ω | τ ω = k})
    (hfin : ∀ᵐ ω ∂iidCodeMeasure, τ ω < ⊤)
    {β : Type*} [MeasurableSpace β] {H : (ℕ → Fin 3) → β} (hH : Measurable H) :
    iidCodeMeasure.map (fun ω => H (codeShift (τ ω).toNat ω)) = iidCodeMeasure.map H :=
  map_comp_codeShift_toNat τ hτ hfin hH

/-- A measurable frontier functional of the stopped past and future is independent of any
measurable functional of the future, by the strong Markov property and independence of `G` and -/
theorem indepFun_frontier_of_strongMarkov (τ : (ℕ → Fin 3) → ℕ∞)
    (hτ : ∀ k : ℕ, MeasurableSet[codePast k] {ω | τ ω = k})
    (hfin : ∀ᵐ ω ∂iidCodeMeasure, τ ω < ⊤)
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {G : (ℕ → Fin 3) → α} {H : (ℕ → Fin 3) → β}
    (hG : Measurable G) (hH : Measurable H) (hGH : IndepFun G H iidCodeMeasure)
    (F : ℕ → (ℕ → Fin 3) → α → γ)
    (hF : ∀ k, Measurable (Function.uncurry (F k))) :
    IndepFun (fun ω => F (τ ω).toNat (codePastVector τ ω)
      (G (codeShift (τ ω).toNat ω)))
      (fun ω => H (codeShift (τ ω).toNat ω)) iidCodeMeasure := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S T hS hT
  let X : (ℕ → Fin 3) → γ := fun ω =>
    F (τ ω).toNat (codePastVector τ ω) (G (codeShift (τ ω).toNat ω))
  let Y : (ℕ → Fin 3) → β := fun ω => H (codeShift (τ ω).toNat ω)
  let N : Set (ℕ → Fin 3) := {ω | τ ω < ⊤}
  let U : Set (ℕ → Fin 3) := X ⁻¹' S
  let V : Set (ℕ → Fin 3) := Y ⁻¹' T
  let A : ∀ k : ℕ, (Fin k → Fin 3) → Set (ℕ → Fin 3) := fun k p =>
    {ω | τ ω = k} ∩ {ω | codePrefix k ω = p}
  let P : ∀ k : ℕ, (Fin k → Fin 3) → Set α := fun k p =>
    {a | F k (extendCodePrefix k p) a ∈ S}
  let C : ∀ k : ℕ, (Fin k → Fin 3) → Set (ℕ → Fin 3) := fun k p =>
    {ω | G ω ∈ P k p ∧ H ω ∈ T}
  let D : ∀ k : ℕ, (Fin k → Fin 3) → Set (ℕ → Fin 3) := fun k p =>
    {ω | G ω ∈ P k p}
  let Index := Σ k : ℕ, Fin k → Fin 3
  let J : Index → Set (ℕ → Fin 3) := fun i =>
    A i.1 i.2 ∩ codeShift i.1 ⁻¹' C i.1 i.2
  let O : Index → Set (ℕ → Fin 3) := fun i =>
    A i.1 i.2 ∩ codeShift i.1 ⁻¹' D i.1 i.2
  have hA : ∀ k p, MeasurableSet[codePast k] (A k p) := by
    intro k p
    let pref : (ℕ → Fin 3) → (Fin k → Fin 3) := codePrefix k
    have hp : MeasurableSet[codePast k] (pref ⁻¹' {p}) := by
      exact ⟨{x | x = p}, (Set.toFinite _).measurableSet, rfl⟩
    change MeasurableSet[codePast k] ({ω | τ ω = k} ∩ pref ⁻¹' {p})
    exact (hτ k).inter hp
  have hP : ∀ k p, MeasurableSet (P k p) := by
    intro k p
    exact ((hF k).comp (measurable_const.prodMk measurable_id)) hS
  have hC : ∀ k p, MeasurableSet (C k p) := by
    intro k p
    change MeasurableSet (G ⁻¹' P k p ∩ H ⁻¹' T)
    exact (hG (hP k p)).inter (hH hT)
  have hD : ∀ k p, MeasurableSet (D k p) := by
    intro k p
    change MeasurableSet (G ⁻¹' P k p)
    exact hG (hP k p)
  have hJm : ∀ i, MeasurableSet (J i) := by
    intro i
    exact ((codePast_le i.1) _ (hA i.1 i.2)).inter
      ((measurable_codeShift i.1) (hC i.1 i.2))
  have hOm : ∀ i, MeasurableSet (O i) := by
    intro i
    exact ((codePast_le i.1) _ (hA i.1 i.2)).inter
      ((measurable_codeShift i.1) (hD i.1 i.2))
  have hpieceJ : ∀ i : Index,
      iidCodeMeasure (J i) = iidCodeMeasure (O i) * iidCodeMeasure (H ⁻¹' T) := by
    intro i
    have hSMJ := iidCodeMeasure_inter_codeShift_preimage i.1
      (hA i.1 i.2) (hC i.1 i.2)
    have hSMO := iidCodeMeasure_inter_codeShift_preimage i.1
      (hA i.1 i.2) (hD i.1 i.2)
    have hGH' := hGH.measure_inter_preimage_eq_mul
      (P i.1 i.2) T (hP i.1 i.2) hT
    have hCset : C i.1 i.2 = G ⁻¹' P i.1 i.2 ∩ H ⁻¹' T := by
      ext ω
      rfl
    have hDset : D i.1 i.2 = G ⁻¹' P i.1 i.2 := by
      ext ω
      rfl
    have hC' : iidCodeMeasure (C i.1 i.2) =
        iidCodeMeasure (D i.1 i.2) * iidCodeMeasure (H ⁻¹' T) := by
      rw [hCset, hDset]
      exact hGH'
    calc
      iidCodeMeasure (J i) = iidCodeMeasure (A i.1 i.2) *
          iidCodeMeasure (C i.1 i.2) := by simpa [J] using hSMJ
      _ = iidCodeMeasure (A i.1 i.2) *
          (iidCodeMeasure (D i.1 i.2) * iidCodeMeasure (H ⁻¹' T)) := by rw [hC']
      _ = (iidCodeMeasure (A i.1 i.2) * iidCodeMeasure (D i.1 i.2)) *
          iidCodeMeasure (H ⁻¹' T) := by rw [mul_assoc]
      _ = iidCodeMeasure (O i) * iidCodeMeasure (H ⁻¹' T) := by
        rw [← hSMO]
  have hdisjJ : Pairwise (Disjoint on J) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    apply hij
    cases i with
    | mk k p =>
      cases j with
      | mk l q =>
        have hiA := hi.1
        have hjA := hj.1
        change τ ω = (k : ℕ∞) ∧ codePrefix k ω = p at hiA
        change τ ω = (l : ℕ∞) ∧ codePrefix l ω = q at hjA
        have hkl : k = l := by
          exact WithTop.coe_injective (hiA.1.symm.trans hjA.1)
        subst l
        have hpq : p = q := hiA.2.symm.trans hjA.2
        subst q
        rfl
  have hdisjO : Pairwise (Disjoint on O) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    apply hij
    cases i with
    | mk k p =>
      cases j with
      | mk l q =>
        have hiA := hi.1
        have hjA := hj.1
        change τ ω = (k : ℕ∞) ∧ codePrefix k ω = p at hiA
        change τ ω = (l : ℕ∞) ∧ codePrefix l ω = q at hjA
        have hkl : k = l := by
          exact WithTop.coe_injective (hiA.1.symm.trans hjA.1)
        subst l
        have hpq : p = q := hiA.2.symm.trans hjA.2
        subst q
        rfl
  have hunionJ : (⋃ i : Index, J i) = N ∩ U ∩ V := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨⟨k, p⟩, hω⟩
      rcases hω with ⟨⟨hk, hp⟩, hv⟩
      change τ ω = (k : ℕ∞) at hk
      change codePrefix k ω = p at hp
      change G (codeShift k ω) ∈ P k p ∧ H (codeShift k ω) ∈ T at hv
      have hpast := codePastVector_eq_prefix τ k ω hk
      refine ⟨⟨by change τ ω < ⊤; rw [hk]; exact ENat.natCast_lt_top _, ?_⟩, ?_⟩
      · change X ω ∈ S
        have hv1 := hv.1
        change F k (extendCodePrefix k p) (G (codeShift k ω)) ∈ S at hv1
        simpa [X, hk, hpast, hp] using hv1
      · change Y ω ∈ T
        simpa [Y, hk] using hv.2
    · rintro ⟨⟨hN, hU⟩, hV⟩
      change τ ω < ⊤ at hN
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hN.ne
      have hk' : τ ω = (k : ℕ∞) := hk.symm
      let p := codePrefix k ω
      have hpast := codePastVector_eq_prefix τ k ω hk'
      refine Set.mem_iUnion.mpr ⟨⟨k, p⟩, ?_⟩
      change X ω ∈ S at hU
      change Y ω ∈ T at hV
      have hU' : F k (extendCodePrefix k p) (G (codeShift k ω)) ∈ S := by
        simpa [X, p, hk', hpast] using hU
      have hV' : H (codeShift k ω) ∈ T := by simpa [Y, hk'] using hV
      have hfuture : codeShift k ω ∈ C k p := by
        change G (codeShift k ω) ∈ P k p ∧ H (codeShift k ω) ∈ T
        constructor
        · change F k (extendCodePrefix k p) (G (codeShift k ω)) ∈ S
          exact hU'
        · exact hV'
      change ω ∈ A k p ∩ codeShift k ⁻¹' C k p
      refine ⟨?_, ?_⟩
      · change τ ω = (k : ℕ∞) ∧ codePrefix k ω = p
        exact ⟨hk', rfl⟩
      · exact hfuture
  have hunionO : (⋃ i : Index, O i) = N ∩ U := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨⟨k, p⟩, hω⟩
      rcases hω with ⟨⟨hk, hp⟩, hv⟩
      change τ ω = (k : ℕ∞) at hk
      change codePrefix k ω = p at hp
      change G (codeShift k ω) ∈ P k p at hv
      have hpast := codePastVector_eq_prefix τ k ω hk
      refine ⟨by change τ ω < ⊤; rw [hk]; exact ENat.natCast_lt_top _, ?_⟩
      change X ω ∈ S
      change F k (extendCodePrefix k p) (G (codeShift k ω)) ∈ S at hv
      simpa [X, hk, hpast, hp] using hv
    · rintro ⟨hN, hU⟩
      change τ ω < ⊤ at hN
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hN.ne
      have hk' : τ ω = (k : ℕ∞) := hk.symm
      let p := codePrefix k ω
      have hpast := codePastVector_eq_prefix τ k ω hk'
      refine Set.mem_iUnion.mpr ⟨⟨k, p⟩, ?_⟩
      change ω ∈ A k p ∩ codeShift k ⁻¹' D k p
      refine ⟨?_, ?_⟩
      · change τ ω = (k : ℕ∞) ∧ codePrefix k ω = p
        exact ⟨hk', rfl⟩
      change X ω ∈ S at hU
      have hU' : F k (extendCodePrefix k p) (G (codeShift k ω)) ∈ S := by
        simpa [X, p, hk', hpast] using hU
      change G (codeShift k ω) ∈ P k p
      change F k (extendCodePrefix k p) (G (codeShift k ω)) ∈ S
      exact hU'
  have hsum : iidCodeMeasure (N ∩ U ∩ V) =
      iidCodeMeasure (H ⁻¹' T) * iidCodeMeasure (N ∩ U) := by
    rw [← hunionJ, ← hunionO, measure_iUnion hdisjJ hJm, measure_iUnion hdisjO hOm]
    calc
      (∑' i : Index, iidCodeMeasure (J i)) =
          ∑' i : Index, iidCodeMeasure (O i) * iidCodeMeasure (H ⁻¹' T) :=
        tsum_congr hpieceJ
      _ = iidCodeMeasure (H ⁻¹' T) * ∑' i : Index, iidCodeMeasure (O i) := by
        exact ENNReal.tsum_mul_right.trans (mul_comm _ _)
  have hY : iidCodeMeasure V = iidCodeMeasure (H ⁻¹' T) := by
    have hmap := map_comp_codeShift_stoppingTime τ hτ hfin hH
    have hm := (hH.comp (measurable_codeShift_toNat τ hτ))
    have hmapT := congrArg (fun m : Measure β => m T) hmap
    change iidCodeMeasure ((fun ω => H (codeShift (τ ω).toNat ω)) ⁻¹' T) =
      iidCodeMeasure (H ⁻¹' T)
    calc
      iidCodeMeasure ((fun ω => H (codeShift (τ ω).toNat ω)) ⁻¹' T) =
          (iidCodeMeasure.map (fun ω => H (codeShift (τ ω).toNat ω))) T :=
        (Measure.map_apply hm hT).symm
      _ = (iidCodeMeasure.map H) T := hmapT
      _ = iidCodeMeasure (H ⁻¹' T) := Measure.map_apply hH hT
  have hfiniteUV : N ∩ U ∩ V =ᵐ[iidCodeMeasure] U ∩ V := by
    filter_upwards [hfin] with ω hω
    simp [N, hω]
  have hfiniteU : N ∩ U =ᵐ[iidCodeMeasure] U := by
    filter_upwards [hfin] with ω hω
    simp [N, hω]
  calc
    iidCodeMeasure (U ∩ V) = iidCodeMeasure (N ∩ U ∩ V) :=
      measure_congr hfiniteUV.symm
    _ = iidCodeMeasure (H ⁻¹' T) * iidCodeMeasure (N ∩ U) := hsum
    _ = iidCodeMeasure V * iidCodeMeasure U := by rw [← hY, measure_congr hfiniteU]
    _ = iidCodeMeasure U * iidCodeMeasure V := mul_comm _ _

end DirectedDistances.Probability
