module

public import DirectedDistances.KMSW.StageMapCongr
public import DirectedDistances.KMSW.KMSWMirrorRootedLaw

/-! # Fresh-window determinism of KMSW stage maps

The finite stages here start from the canonical initial state. They do not identify
a patch inside a global map or define a graph-distance ball. The root frame keeps
the edge identity and its Boolean side, including when that edge is missing. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
theorem kmswStage_nextEdge_eq_of_prefix (w w' : ℕ → Fin 3) (m : ℕ)
    (hcode : ∀ i < m, w i = w' i) :
    (kmswStage w m).nextEdge = (kmswStage w' m).nextEdge :=
  congrArg State.nextEdge (kmswStage_eq_of_prefix w w' m hcode)

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
theorem kmswStageDirectedMapIsoOfPrefix_apply (w w' : ℕ → Fin 3) (m : ℕ)
    (hcode : ∀ i < m, w i = w' i)
    (e : Fin (kmswStage w m).nextEdge) (b : Bool) :
    (kmswStageDirectedMapIsoOfPrefix w w' m hcode).toEquiv (e, b) =
      (Fin.cast (kmswStage_nextEdge_eq_of_prefix w w' m hcode) e, b) := by
  obtain ⟨he, hb⟩ := kmswStageDirectedMapIsoOfPrefix_val w w' m hcode (e, b)
  exact Prod.ext (Fin.ext he) hb

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
theorem kmswStageDirectedMap_toRootedClass_eq_of_prefix
    (w w' : ℕ → Fin 3) (m : ℕ) (hcode : ∀ i < m, w i = w' i)
    (e : Fin (kmswStage w m).nextEdge) (b : Bool) :
    (kmswStageDirectedMap w m).toRootedClass (e, b) =
      (kmswStageDirectedMap w' m).toRootedClass
        (Fin.cast (kmswStage_nextEdge_eq_of_prefix w w' m hcode) e, b) := by
  apply (DirectedMapWithMissing.toRootedClass_eq_iff _ _ _ _).mpr
  exact ⟨kmswStageDirectedMapIsoOfPrefix w w' m hcode,
    kmswStageDirectedMapIsoOfPrefix_apply w w' m hcode e b⟩

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
@[expose] def kmswFreshWindowDirectedMapIso (w w' : ℕ → Fin 3) (s s' m : ℕ)
    (hcode : ∀ i < m, w (s + i) = w' (s' + i)) :
    DirectedMapWithMissingIso
      (kmswStageDirectedMap (fun i => w (s + i)) m)
      (kmswStageDirectedMap (fun i => w' (s' + i)) m) :=
  kmswStageDirectedMapIsoOfPrefix (fun i => w (s + i)) (fun i => w' (s' + i))
    m hcode

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
theorem kmswFreshWindowDirectedMapIso_apply (w w' : ℕ → Fin 3) (s s' m : ℕ)
    (hcode : ∀ i < m, w (s + i) = w' (s' + i))
    (e : Fin (kmswStage (fun i => w (s + i)) m).nextEdge) (b : Bool) :
    (kmswFreshWindowDirectedMapIso w w' s s' m hcode).toEquiv (e, b) =
      (Fin.cast (kmswStage_nextEdge_eq_of_prefix
        (fun i => w (s + i)) (fun i => w' (s' + i)) m hcode) e, b) :=
  kmswStageDirectedMapIsoOfPrefix_apply
    (fun i => w (s + i)) (fun i => w' (s' + i)) m hcode e b

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
@[expose] noncomputable def kmswFreshWindowClass (m : ℕ) :
    (Fin m → Fin 3) → FiniteDirectedMapClass :=
  fun c => (kmswStageDirectedMap
    (fun i => if hi : i < m then c ⟨i, hi⟩ else 0) m).toClass

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
theorem kmswFreshWindowClass_eq (u : ℕ → Fin 3) (m : ℕ) :
    (kmswStageDirectedMap u m).toClass =
      kmswFreshWindowClass m (fun i => u i) := by
  apply (DirectedMapWithMissing.toClass_eq_toClass_iff _ _).mpr
  refine ⟨kmswStageDirectedMapIsoOfPrefix u
    (fun i => if hi : i < m then u (⟨i, hi⟩ : Fin m) else 0) m ?_⟩
  intro i hi
  simp only [dite_eq_left hi]

/-- fresh-window determinism of KMSW stage maps with a root frame (Definition 3.8 -/
theorem exists_kmswFreshWindowClass (m : ℕ) :
    ∃ F : (Fin m → Fin 3) → FiniteDirectedMapClass,
      ∀ u : ℕ → Fin 3, (kmswStageDirectedMap u m).toClass = F (fun i => u i) :=
  ⟨kmswFreshWindowClass m, fun u => kmswFreshWindowClass_eq u m⟩

end DirectedDistances.KMSW
