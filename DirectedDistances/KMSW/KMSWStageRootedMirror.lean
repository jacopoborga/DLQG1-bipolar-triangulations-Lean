module

public import DirectedDistances.KMSW.KMSWDiskRootedLaw
public import DirectedDistances.KMSW.KMSWMirrorRootedLaw
public import DirectedDistances.KMSW.KMSWMirrorSymmetryFinite

/-! Finite rooted mirror symmetry for the stage map, with the selected first-hit dart
flipped by the mirror. I4 is a proposed reading, NOT adopted. These are helpers only. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap MeasureTheory

private def stageMirrorIso {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {M : DirectedMapWithMissing D}
    {N : DirectedMapWithMissing E} (I : DirectedMapWithMissingIso M N) :
    DirectedMapWithMissingIso M.mirror N.mirror where
  toEquiv := I.toEquiv
  rot_comm := by
    intro d
    change I.toEquiv (M.rot.symm d) = N.rot.symm (I.toEquiv d)
    apply N.rot.injective
    rw [← I.rot_comm]
    simp only [Equiv.apply_symm_apply]
  edgeInv_comm := I.edgeInv_comm
  missing_iff := I.missing_iff
  tail_iff := I.tail_iff
  outer_iff := by
    intro d
    rw [DirectedMapWithMissing.mirror_isOuter_iff,
      DirectedMapWithMissing.mirror_isOuter_iff]
    rw [← I.edgeInv_comm]
    exact I.outer_iff _

/-- Helper toward prop-uihbot-sym / prop-disk-bs-conv
KMSW stage map rooted at the first-hit edge (I4 proposed ordered-dart reading,
not the paper result. -/
@[expose] noncomputable def rootedStageMirror {ℓ n : ℕ}
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) : RootedFiniteDirectedMapClass :=
  (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) p.1.val) n).mirror.toRootedClass
    ((kmswStageDirectedMap (finiteCodeExtend (n := n + 1) p.1.val) n).edgeInv
      (kmswDiskRootDart p.1 p.2))

/-- Helper toward prop-uihbot-sym / prop-disk-bs-conv
KMSW stage map rooted at the first-hit edge (I4 proposed ordered-dart reading,
not the paper result. -/
theorem rootedMirror_eq_rootedStageMirror {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    rootedMirror (kmswLeftEndpointSideEquiv ℓ n hℓ c, k) =
      rootedStageMirror (c, k) := by
  obtain ⟨I⟩ := kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ c
  apply (DirectedMapWithMissing.toRootedClass_eq_iff _ _ _ _).mpr
  refine ⟨stageMirrorIso I, ?_⟩
  change I.toEquiv
    ((kmswLeftEndpointSideEquiv ℓ n hℓ c).val.out.partialMap.edgeInv _) = _
  rw [I.edgeInv_comm, iso_leftPathDart_eq_rootDart hℓ c _ I k]

/-- Helper toward prop-uihbot-sym / prop-disk-bs-conv
KMSW stage map rooted at the first-hit edge (I4 proposed ordered-dart reading,
not the paper result. -/
theorem rootedStage_uniform_eq_rootedStageMirror (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStage =
      ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStageMirror := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  let : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  let f := fun p : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} × Fin (ℓ - 1) =>
    ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1, p.2)
  have h := congrArg (fun μ => μ.map (rootedStageMirror (ℓ := ℓ) (n := n)))
    (kmswDiskFiniteSample_uniform_prod ℓ n hℓ)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h
  have hf : rootedStageMirror ∘ f = rootedMirror := by
    funext p
    exact (rootedMirror_eq_rootedStageMirror hℓ
      ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1) p.2).symm.trans
        (congrArg (fun q => rootedMirror (q, p.2))
          ((kmswLeftEndpointSideEquiv ℓ n hℓ).apply_symm_apply p.1))
  rw [hf] at h
  exact (rootedDecorated_uniform_eq_rootedStage ℓ n hℓ).symm.trans
    ((rootedDecorated_uniform_eq_rootedMirror ℓ n hℓ).trans h)

/-- Helper toward prop-uihbot-sym / prop-disk-bs-conv
KMSW stage map rooted at the first-hit edge (I4 proposed ordered-dart reading,
not the paper result. -/
theorem rootedStage_walkMirror {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    rootedStage (kmswWalkMirrorEquiv ℓ n hℓ c, Fin.rev k) =
      rootedStageMirror (c, k) := by
  have he : kmswLeftEndpointSideEquiv ℓ n hℓ (kmswWalkMirrorEquiv ℓ n hℓ c) =
      kmswMirrorSymmetryEquiv ℓ (n + ℓ) hℓ (kmswLeftEndpointSideEquiv ℓ n hℓ c) :=
    (kmswLeftEndpointSideEquiv ℓ n hℓ).apply_symm_apply _
  rw [← rootedDecorated_eq_rootedStage hℓ, he, rootedDecorated_mirror hℓ]
  exact rootedMirror_eq_rootedStageMirror hℓ c k

end DirectedDistances.KMSW
