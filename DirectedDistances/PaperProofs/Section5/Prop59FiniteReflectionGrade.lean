module

public import DirectedDistances.PaperProofs.Section5.Prop59FiniteMarkAudit
public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorFacedCompat
public import DirectedDistances.PaperProofs.Section5.Prop59OrderedRootIndexing
public import DirectedDistances.Paper.Section3.BdyReverse
public import DirectedDistances.PlanarMap.KMSWRightPrefixReversalClass

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory

/-! Helper toward Proposition 5.9. The source proof's finite comparison is between
the marked classes `M^bc_{ell+1,1}(n-1)` and `M^bc_{1,ell+1}(n-1)`; the latter
edge count in both KMSW carriers is `n + ell + 1`. Lemma 3.18 transports the
class by reversing the first `ell` right-boundary edges, and the uniform mark
is reindexed by `Fin.rev`. -/

/-- Helper toward Proposition 5.9: the finite KMSW class for
`M^bc_{ell+1,1}(n-1)`, indexed by total geometric edges. -/
abbrev Prop59LeftFiniteClass (n ell : ℕ) :=
  {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}

/-- Helper toward Proposition 5.9: the finite KMSW class for
`M^bc_{1,ell+1}(n-1)`, indexed by total geometric edges. -/
abbrev Prop59RightFiniteClass (n ell : ℕ) :=
  {q : KMSWMapIsoClass 1 (ell + 1) (n + (ell + 1)) // q.IsChanneled}

abbrev Prop59LeftFiniteSimpleClass (n ell : ℕ) :=
  {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
    q.IsChanneled ∧ q.IsSimpleOuterBoundary}

abbrev Prop59RightFiniteSimpleClass (n ell : ℕ) :=
  {q : KMSWMapIsoClass 1 (ell + 1) (n + (ell + 1)) //
    q.IsChanneled ∧ q.IsSimpleOuterBoundary}

private abbrev Prop59ReversedRawClass (n ell : ℕ) :=
  {q : KMSWMapIsoClass (1 + ell) ((ell + 1) - ell) (n + (ell + 1)) //
    q.IsChanneled ∧ q.IsSimpleOuterBoundary}

/-- Helper toward Proposition 5.9. On the endpoint carriers, channeling
Lemma 3.18. -/
private noncomputable def prop59LeftClassSimpleEquiv (n ell : ℕ) (hell : 0 < ell) :
    Prop59LeftFiniteClass n ell ≃ Prop59LeftFiniteSimpleClass n ell where
  toFun q := ⟨q.1, q.2,
    KMSWMapIsoClass.isSimpleOuterBoundary_of_rightEndpoint (by omega) q.1⟩
  invFun q := ⟨q.1, q.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Helper toward Proposition 5.9. On the endpoint carriers, channeling
Lemma 3.18. -/
private noncomputable def prop59RightClassSimpleEquiv (n ell : ℕ) (hell : 0 < ell) :
    Prop59RightFiniteClass n ell ≃ Prop59RightFiniteSimpleClass n ell where
  toFun q := ⟨q.1, q.2,
    KMSWMapIsoClass.isSimpleOuterBoundary_of_leftEndpoint (by omega) q.1⟩
  invFun q := ⟨q.1, q.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The natural-number index normalization in the output of the prefix
reversal (`1 + ell`, `(ell + 1) - ell`) to the printed endpoint indices
(`ell + 1`, `1`). -/
private noncomputable def prop59NormalizeReversedClass (n ell : ℕ) :
    Prop59ReversedRawClass n ell ≃ Prop59LeftFiniteSimpleClass n ell := by
  have h₁ : 1 + ell = ell + 1 := by omega
  have h₂ : (ell + 1) - ell = 1 := by omega
  have htype : Prop59ReversedRawClass n ell = Prop59LeftFiniteSimpleClass n ell := by
    unfold Prop59ReversedRawClass Prop59LeftFiniteSimpleClass
    exact congrArg₂
      (fun a b : ℕ =>
        {q : KMSWMapIsoClass a b (n + (ell + 1)) //
          q.IsChanneled ∧ q.IsSimpleOuterBoundary}) h₁ h₂
  exact Equiv.cast htype

/-- Helper toward Proposition 5.9. This is the finite class bijection from
`M^bc_{ell+1,1}(n-1)` to `M^bc_{1,ell+1}(n-1)` supplied by Lemma 3.18 with
`(ell,r,k)=(1,ell+1,ell)`, expressed on the KMSW class carriers. -/
noncomputable def prop59FiniteReflectionClassEquiv (n ell : ℕ) (hell : 0 < ell) :
    Prop59LeftFiniteClass n ell ≃ Prop59RightFiniteClass n ell := by
  let e : Prop59RightFiniteSimpleClass n ell ≃ Prop59ReversedRawClass n ell :=
    KMSWMapIsoClass.kmswRightPrefixReversalClassEquiv
    (ℓ := 1) (r := ell + 1) (n := n + (ell + 1)) ell
      (by omega) (by omega) (by omega)
  exact (prop59LeftClassSimpleEquiv n ell hell).trans
    ((e.trans (prop59NormalizeReversedClass n ell)).symm.trans
      (prop59RightClassSimpleEquiv n ell hell).symm)

/-- Helper toward Proposition 5.9. The explicit bijection on marked finite
sample spaces pairs the class reversal from Lemma 3.18 with reversal of the
uniform boundary-mark index. -/
theorem prop59FiniteReflectionMarkedBijective (n ell : ℕ) (hell : 0 < ell) :
    Function.Bijective
      (fun p : Prop59LeftFiniteClass n ell × Fin ell =>
        (prop59FiniteReflectionClassEquiv n ell hell p.1, p.2.rev)) := by
  constructor
  · rintro ⟨q, i⟩ ⟨q', j⟩ h
    have hq : prop59FiniteReflectionClassEquiv n ell hell q =
        prop59FiniteReflectionClassEquiv n ell hell q' := congrArg Prod.fst h
    have hi : i.rev = j.rev := congrArg Prod.snd h
    exact Prod.ext ((prop59FiniteReflectionClassEquiv n ell hell).injective hq)
      (Fin.rev_bijective.1 hi)
  · rintro ⟨q, i⟩
    refine ⟨((prop59FiniteReflectionClassEquiv n ell hell).symm q, i.rev), ?_⟩
    exact Prod.ext
      (Equiv.apply_symm_apply (prop59FiniteReflectionClassEquiv n ell hell) q)
      (Fin.rev_rev i)

/-- Helper toward Proposition 5.9. Lemma 3.18's finite class bijection also
transports the uniform ordered boundary mark, with index reversed. This is
`n-1` grade on both sides. -/
theorem prop59FiniteReflectionMarkedUniform (n ell : ℕ) (hell : 0 < ell) :
    let Qₗ := Prop59LeftFiniteClass n ell
    let Qᵣ := Prop59RightFiniteClass n ell
    letI : Fintype Qₗ := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : Fintype Qᵣ := Fintype.ofEquiv Qₗ
      (prop59FiniteReflectionClassEquiv n ell hell)
    letI : MeasurableSpace Qₗ := ⊤
    letI : MeasurableSpace Qᵣ := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    ((uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))).map
      (fun p => (prop59FiniteReflectionClassEquiv n ell hell p.1, p.2.rev)) =
        (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell)) := by
  let Qₗ := Prop59LeftFiniteClass n ell
  let Qᵣ := Prop59RightFiniteClass n ell
  letI : Fintype Qₗ := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
  letI : Fintype Qᵣ := Fintype.ofEquiv Qₗ
    (prop59FiniteReflectionClassEquiv n ell hell)
  letI : MeasurableSpace Qₗ := ⊤
  letI : MeasurableSpace Qᵣ := ⊤
  letI : MeasurableSpace (Fin ell) := ⊤
  have hclass := uniformCountingMeasure_map_of_bijective
    (prop59FiniteReflectionClassEquiv n ell hell)
    (prop59FiniteReflectionClassEquiv n ell hell).bijective
  have hmark := uniformCountingMeasure_map_of_bijective
    (Fin.rev (n := ell)) Fin.rev_bijective
  have hprod := Measure.map_prod_map
    (uniformCountingMeasure Qₗ) (uniformCountingMeasure (Fin ell))
    (measurable_of_countable (prop59FiniteReflectionClassEquiv n ell hell))
    (measurable_of_countable (Fin.rev (n := ell)))
  change
    ((uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))).map
        (Prod.map (prop59FiniteReflectionClassEquiv n ell hell) Fin.rev) = _
  calc
    _ = ((uniformCountingMeasure Qₗ).map
          (prop59FiniteReflectionClassEquiv n ell hell)).prod
          ((uniformCountingMeasure (Fin ell)).map Fin.rev) := hprod.symm
    _ = (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell)) := by
      rw [hclass, hmark]





























end DirectedDistances.PaperProofs.Section5
