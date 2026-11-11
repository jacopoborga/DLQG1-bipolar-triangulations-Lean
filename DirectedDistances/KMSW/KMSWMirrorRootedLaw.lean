module

public import DirectedDistances.KMSW.KMSWMirrorChainIndex
public import DirectedDistances.KMSW.KMSWMirrorSymmetryFinite
public import DirectedDistances.KMSW.KMSWLeftProcedureLiteral
public import DirectedDistances.KMSW.KMSWDiskFiniteSample

/-! Finite rooted mirror symmetry with the root recorded as an ordered boundary dart.
The mirror flips the root dart. This is the proposed I4 reading, NOT adopted; -/

public section
namespace DirectedDistances.PlanarMap

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
@[expose] def rootedFiniteDirectedMapSetoid :
    Setoid (Σ k : ℕ, DirectedMapWithMissing (Fin k) × Fin k) where
  r M N := ∃ I : DirectedMapWithMissingIso M.2.1 N.2.1,
    I.toEquiv M.2.2 = N.2.2
  iseqv := by
    constructor
    · intro M
      exact ⟨DirectedMapWithMissingIso.refl M.2.1, rfl⟩
    · rintro M N ⟨I, hI⟩
      refine ⟨I.symm, ?_⟩
      change I.toEquiv.symm N.2.2 = M.2.2
      rw [← hI, Equiv.symm_apply_apply]
    · rintro M N P ⟨I, hI⟩ ⟨J, hJ⟩
      refine ⟨I.trans J, ?_⟩
      change J.toEquiv (I.toEquiv M.2.2) = P.2.2
      rw [hI, hJ]

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
@[expose] def RootedFiniteDirectedMapClass : Type :=
  Quotient rootedFiniteDirectedMapSetoid

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
@[expose] noncomputable def DirectedMapWithMissing.toRootedClass {D : Type*}
    [Fintype D] [DecidableEq D] (M : DirectedMapWithMissing D) (d : D) :
    RootedFiniteDirectedMapClass :=
  Quotient.mk rootedFiniteDirectedMapSetoid
    ⟨Fintype.card D, M.transport (Fintype.equivFin D), Fintype.equivFin D d⟩

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
theorem DirectedMapWithMissing.toRootedClass_eq_iff {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (M : DirectedMapWithMissing D) (d : D)
    (N : DirectedMapWithMissing E) (d' : E) :
    M.toRootedClass d = N.toRootedClass d' ↔
      ∃ I : DirectedMapWithMissingIso M N, I.toEquiv d = d' := by
  constructor
  · intro h
    obtain ⟨I, hI⟩ := Quotient.exact h
    refine ⟨(M.transportIso (Fintype.equivFin D)).trans
      (I.trans (N.transportIso (Fintype.equivFin E)).symm), ?_⟩
    change I.toEquiv (Fintype.equivFin D d) = Fintype.equivFin E d' at hI
    change (Fintype.equivFin E).symm (I.toEquiv (Fintype.equivFin D d)) = d'
    rw [hI, Equiv.symm_apply_apply]
  · rintro ⟨I, hI⟩
    refine Quotient.sound ⟨(M.transportIso (Fintype.equivFin D)).symm.trans
      (I.trans (N.transportIso (Fintype.equivFin E))), ?_⟩
    change Fintype.equivFin E
      (I.toEquiv ((Fintype.equivFin D).symm (Fintype.equivFin D d))) =
        Fintype.equivFin E d'
    rw [Equiv.symm_apply_apply, hI]

end DirectedDistances.PlanarMap

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap MeasureTheory

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
@[expose] noncomputable def rootedDecorated {ℓ N : ℕ}
    (p : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} × Fin (ℓ - 1)) :
    RootedFiniteDirectedMapClass :=
  p.1.val.out.partialMap.toRootedClass (p.1.val.out.B.leftPath.darts.get
    ⟨p.2.val, by rw [p.1.val.out.B.leftPath.darts_length]; have := p.2.isLt; omega⟩)

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
@[expose] noncomputable def rootedMirror {ℓ N : ℕ}
    (p : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} × Fin (ℓ - 1)) :
    RootedFiniteDirectedMapClass :=
  p.1.val.out.partialMap.mirror.toRootedClass
    (p.1.val.out.partialMap.edgeInv (p.1.val.out.B.leftPath.darts.get
      ⟨p.2.val, by rw [p.1.val.out.B.leftPath.darts_length]; have := p.2.isLt; omega⟩))

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
theorem rootedDecorated_mirror {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (q : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled}) (k : Fin (ℓ - 1)) :
    rootedDecorated (kmswMirrorSymmetryEquiv ℓ N hℓ q, Fin.rev k) =
      rootedMirror (q, k) := by
  obtain ⟨I⟩ := kmswMirrorSymmetryEquiv_partialMapIso ℓ N hℓ q
  apply (DirectedMapWithMissing.toRootedClass_eq_iff _ _ _ _).mpr
  exact ⟨I, kmswMirrorSymmetryEquiv_missing_dart_rev hℓ q I k⟩

/-- finite rooted mirror-symmetry law; the root is an ordered boundary dart
(I4 proposed reading, NOT adopted; the mirror flips the root dart); -/
theorem rootedDecorated_uniform_eq_rootedMirror (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedDecorated =
      ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedMirror := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  let : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  let f := fun p : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} × Fin (ℓ - 1) =>
    (kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ p.1, Fin.rev p.2)
  have h := congrArg (fun μ => μ.map (rootedDecorated (ℓ := ℓ) (N := n + ℓ)))
    (kmswMirrorSymmetryEquiv_uniform_prod ℓ n hℓ)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h
  have hf : rootedDecorated ∘ f = rootedMirror := by
    funext p
    exact rootedDecorated_mirror hℓ p.1 p.2
  change _ = _ at h
  rw [hf] at h
  exact h.symm

end DirectedDistances.KMSW
