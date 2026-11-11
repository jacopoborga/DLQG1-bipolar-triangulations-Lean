module

public import DirectedDistances.KMSW.InftyCutCore
public import DirectedDistances.KMSW.RPhaseLawTransfer
import DirectedDistances.KMSW.DirectedContainLaw1









public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk

/-- An infinite family of vertices that separate every allocated start in a
finite family once their IDs lie beyond those starts yields infinitely many
common finite-avoidance vertices. The separation property is stated with the
exact avoiding-reachable-set predicate `FiniteAvoidance` -/
theorem infinite_common_finiteAvoidance_of_separatingVertices
    {w : ℕ → Fin 3} (A : Finset ℕ) (S : Set (PresentVertex w))
    (hS : S.Infinite)
    (hsep : ∀ z ∈ S, ∀ i ∈ A, A.sup id < z.id →
      FiniteAvoidance (⟨i⟩ : PresentVertex w) z) :
    {c : PresentVertex w | ∀ i ∈ A,
      FiniteAvoidance (⟨i⟩ : PresentVertex w) c}.Infinite := by
  classical
  let M : ℕ := A.sup id
  let E : Set (PresentVertex w) := {z | z.id ≤ M}
  have hE : E.Finite := by
    refine (Set.finite_range
      (fun i : Fin (M + 1) => (⟨i.val⟩ : PresentVertex w))).subset ?_
    intro z hz
    change z.id ≤ M at hz
    refine ⟨⟨z.id, by omega⟩, ?_⟩
    cases z
    rfl
  have hgood : (S \ E).Infinite := by
    by_contra hnot
    have hfin : (S \ E).Finite := by
      by_contra hfin
      exact hnot hfin
    have hsub : S ⊆ (S \ E) ∪ E := by
      intro z hz
      by_cases he : z ∈ E
      · exact Or.inr he
      · exact Or.inl ⟨hz, he⟩
    exact hS ((hfin.union hE).subset hsub)
  apply hgood.mono
  intro z hz
  rcases hz with ⟨hzS, hzE⟩
  intro i hi
  apply hsep z hzS i hi
  have hiM : i ≤ M := Finset.le_sup (f := id) hi
  have hzM : M < z.id := by
    have : ¬ z.id ≤ M := by simpa [E] using hzE
    omega
  exact hzM

private theorem quadrantSplitState_codeShift_zero (ω : ℕ → Fin 3) :
    ∀ n, RandomWalk.quadrantSplitState (RandomWalk.codeShift 0 ω) n =
      RandomWalk.quadrantSplitState ω n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change RandomWalk.quadrantSplitAdvance
        (RandomWalk.quadrantSplitState (RandomWalk.codeShift 0 ω) n)
        (RandomWalk.codeShift 0 ω (n + 1)) =
        RandomWalk.quadrantSplitAdvance
          (RandomWalk.quadrantSplitState ω n) (ω (n + 1))
      rw [ih]
      simp [RandomWalk.codeShift]

private theorem quadrantRCode_codeShift_zero (ω : ℕ → Fin 3) (k : ℕ) :
    RandomWalk.quadrantRCode (RandomWalk.codeShift 0 ω) k =
      RandomWalk.quadrantRCode ω k := by
  classical
  let P (ν : ℕ → Fin 3) :=
    ∃ n, (RandomWalk.quadrantSplitState ν n).rCount = k + 1
  have hP : P (RandomWalk.codeShift 0 ω) ↔ P ω := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [quadrantSplitState_codeShift_zero] using hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [quadrantSplitState_codeShift_zero] using hn⟩
  change (if h : P (RandomWalk.codeShift 0 ω) then
      (RandomWalk.codeShift 0 ω) (Nat.find h) else 0) =
    (if h : P ω then ω (Nat.find h) else 0)
  by_cases h : P ω
  · have hs : P (RandomWalk.codeShift 0 ω) := hP.mpr h
    rw [dite_eq_left hs, dite_eq_left h]
    have hfind : Nat.find hs = Nat.find h := by
      apply Nat.find_congr'
      intro n
      simp [quadrantSplitState_codeShift_zero]
    rw [hfind]
    have hpos : Nat.find h ≠ 0 := by
      intro hzero
      have hspec := Nat.find_spec h
      rw [hzero, RandomWalk.quadrantSplitState] at hspec
      simp [RandomWalk.quadrantSplitStart] at hspec
    simp [RandomWalk.codeShift, hpos]
  · have hs : ¬ P (RandomWalk.codeShift 0 ω) := fun hs => h (hP.mp hs)
    simp [hs, h]

private theorem quadrantLCode_codeShift_zero (ω : ℕ → Fin 3) (k : ℕ) :
    RandomWalk.quadrantLCode (RandomWalk.codeShift 0 ω) k =
      RandomWalk.quadrantLCode ω k := by
  classical
  let P (ν : ℕ → Fin 3) :=
    ∃ n, (RandomWalk.quadrantSplitState ν n).lCount = k + 1
  have hP : P (RandomWalk.codeShift 0 ω) ↔ P ω := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [quadrantSplitState_codeShift_zero] using hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [quadrantSplitState_codeShift_zero] using hn⟩
  change (if h : P (RandomWalk.codeShift 0 ω) then
      (RandomWalk.codeShift 0 ω) (Nat.find h) else 0) =
    (if h : P ω then ω (Nat.find h) else 0)
  by_cases h : P ω
  · have hs : P (RandomWalk.codeShift 0 ω) := hP.mpr h
    rw [dite_eq_left hs, dite_eq_left h]
    have hfind : Nat.find hs = Nat.find h := by
      apply Nat.find_congr'
      intro n
      simp [quadrantSplitState_codeShift_zero]
    rw [hfind]
    have hpos : Nat.find h ≠ 0 := by
      intro hzero
      have hspec := Nat.find_spec h
      rw [hzero, RandomWalk.quadrantSplitState] at hspec
      simp [RandomWalk.quadrantSplitStart] at hspec
    simp [RandomWalk.codeShift, hpos]
  · have hs : ¬ P (RandomWalk.codeShift 0 ω) := fun hs => h (hP.mp hs)
    simp [hs, h]

private theorem phaseSplit_codeShift_zero (ω : ℕ → Fin 3) :
    RandomWalk.phaseSplit (RandomWalk.codeShift 0 ω) =
      RandomWalk.phaseSplit ω := by
  apply Prod.ext <;> funext i <;> by_cases hi : i = 0
  · simp [RandomWalk.phaseSplit, hi]
  · simp [RandomWalk.phaseSplit, hi, quadrantRCode_codeShift_zero]
  · simp [RandomWalk.phaseSplit, hi]
  · simp [RandomWalk.phaseSplit, hi, quadrantLCode_codeShift_zero]

private theorem rCodeSequence_codeShift_zero (ω : ℕ → Fin 3) :
    rCodeSequence (RandomWalk.codeShift 0 ω) = rCodeSequence ω := by
  funext i
  change pitmanCode
      (fun j => (RandomWalk.phaseSplit (RandomWalk.codeShift 0 ω)).1 (j + 1)) i =
    pitmanCode (fun j => (RandomWalk.phaseSplit ω).1 (j + 1)) i
  rw [phaseSplit_codeShift_zero]

/-- Almost surely, for every boundary-hit witness and every family of finite
sets of IDs allocated in the corresponding R-phase maps, each window has
infinitely many common finite-avoidance vertices. This is the P2 premise of
`boundary_windowFiniteAvoidance_of_rPhaseCommonRegions`
left-hit code law of `RPhaseLawTransfer`, and the hit-time rewrite is
`DirectedContainLaw1.codeFstFirstHit_eq_boundaryHitTime`. -/
theorem ae_cutWindowRPhaseCodes_infinite_common_finiteAvoidance :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ A : ℕ → Finset ℕ,
        (∀ K i, i ∈ A K → ∃ N,
          i < (kmswStage (cutWindowRPhaseCodes ω h K) N).nextVertex) →
        ∀ K : ℕ,
          {c : PresentVertex (cutWindowRPhaseCodes ω h K) |
            ∀ i ∈ A K, FiniteAvoidance
              (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) c}.Infinite := by
  have hfixed : ∀ K : ℕ, ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ A : ℕ → Finset ℕ,
        (∀ i, i ∈ A K → ∃ N,
          i < (kmswStage (cutWindowRPhaseCodes ω h K) N).nextVertex) →
        {c : PresentVertex (cutWindowRPhaseCodes ω h K) |
          ∀ i ∈ A K, FiniteAvoidance
            (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) c}.Infinite := by
    intro K
    by_cases hK : K = 0
    · subst K
      filter_upwards [ae_rCodeSequence_infinite_common_finiteAvoidance_any_allocated]
        with ω hω
      intro h A halloc
      have hmodel : cutWindowRPhaseCodes ω h 0 = rCodeSequence ω := by
        change rCodeSequence (RandomWalk.codeShift
          (boundaryHitTime (fun i => ω (i + 1)) h 0) ω) = _
        rw [boundaryHitTime_zero]
        exact rCodeSequence_codeShift_zero ω
      rw [hmodel]
      exact hω (A 0) (by simpa [hmodel] using halloc)
    · have hKpos : 1 ≤ K := by omega
      have hleft := ae_rCodeSequence_properties_and_window_at_leftHit
        (-(K : ℤ)) (by omega)
      filter_upwards [hleft] with ω hω
      intro h A halloc
      have htime := codeFstFirstHit_eq_boundaryHitTime
        ω h (by omega : -(K : ℤ) ≤ -1)
      have htimeNat :
          (RandomWalk.codeFstFirstHit (-(K : ℤ)) ω).toNat =
            boundaryHitTime (fun i => ω (i + 1)) h (-(K : ℤ)) := by
        rw [htime]
        rfl
      have hmodel : cutWindowRPhaseCodes ω h K =
          rCodeSequence (RandomWalk.codeShift
            (RandomWalk.codeFstFirstHit (-(K : ℤ)) ω).toNat ω) := by
        simp only [cutWindowRPhaseCodes, htimeNat]
      rw [hmodel]
      rcases hω with ⟨_, _, _, _, _, hfamilies⟩
      exact hfamilies (A K) (by simpa [hmodel] using halloc)
  let P : (ℕ → Fin 3) → ℕ → Prop := fun ω K =>
    ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ A : ℕ → Finset ℕ,
        (∀ i, i ∈ A K → ∃ N,
          i < (kmswStage (cutWindowRPhaseCodes ω h K) N).nextVertex) →
        {c : PresentVertex (cutWindowRPhaseCodes ω h K) |
          ∀ i ∈ A K, FiniteAvoidance
            (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) c}.Infinite
  have hfixed' : ∀ K, ∀ᵐ ω ∂iidCodeMeasure, P ω K := by
    intro K
    simpa only [P] using hfixed K
  have hall : ∀ᵐ ω ∂iidCodeMeasure, ∀ K, P ω K :=
    ae_all_iff.mpr hfixed'
  filter_upwards [hall] with ω hω
  intro h A halloc K
  exact hω K h A (fun i hi => halloc K i hi)

end DirectedDistances.KMSW
