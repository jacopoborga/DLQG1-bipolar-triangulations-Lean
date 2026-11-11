module

public import DirectedDistances.KMSW.Lemma79StageLeftBoundary
public import DirectedDistances.KMSW.KMSWConstructedRealization
public import DirectedDistances.KMSW.ConstructedBoundaryVertices
public import DirectedDistances.KMSW.Lemma79MarkHeadline
public import DirectedDistances.KMSW.StoppedLeftBoundaryMarkAE
public import DirectedDistances.KMSW.Lemma79MarkTransport

public section
namespace DirectedDistances.KMSW

open Filter
open DirectedDistances.PlanarMap

/-- Coherent finite-stage and classified limit drawings for the stopped-map
bridge. Helper toward Lemma 7.9 (`lem-uiqbot-boltzmann`), not a paper result. -/
structure CoherentRealizationWitness (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) where
  Q : ∀ n, StageDrawing w n
  hExtends : ∀ n, StageExtends w n (Q n) (Q (n + 1))
  G : ∀ n, MonotoneStageInvariant w n (Q n)
  P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot w hfin) (kmswLimitDartVertex w)
  pos_agree : ∀ n v, P.pos v.val = (Q n).pos v
  arc_agree : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d
  U : P.Face
  unbounded : P.IsUnbounded U
  unique_unbounded : ∀ F : P.Face, P.IsUnbounded F → F = U
  borders : ∀ d, P.dartBorders d U ↔ limitExternalDart w d

/-- Under a coherent classified realization, the geometric left boundary of
the limit drawing agrees with the code-side orbit boundary. Helper toward
Lemma 7.9 (`lem-uiqbot-boltzmann`), not a paper result. See -/
theorem topLeftBoundaryVertex_iff_mapLeftBoundaryVertex
    {w : ℕ → Fin 3} {hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (W : CoherentRealizationWitness w hfin)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (v : ℕ) :
    TopLeftBoundaryVertex w W.P W.U v ↔ mapLeftBoundaryVertex w hfin v := by
  have htop := topLeftBoundaryVertex_iff_uiqbotLeftBoundaryVertex w
    htrans hR hL0 W.P W.U W.borders v
  have hmap := mapLeftBoundaryVertex_iff_limit w hfin htrans v
  exact htop.trans hmap.symm

/-- The stopped list is the geometric upper-left path of the unique unbounded
face of the preceding stage. Helper toward Lemma 7.9
(`lem-uiqbot-boltzmann`), not a paper result. See -/
theorem stoppedLeftBoundaryVertex_iff_stageLeftBoundaryVertex
    {w : ℕ → Fin 3} {hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (W : CoherentRealizationWitness w hfin) {t : ℕ} (ht : 1 ≤ t)
    (v : ℕ) :
    ∃ Us : (W.Q (t - 1)).Face,
      (W.Q (t - 1)).IsUnbounded Us ∧
      (∀ F : (W.Q (t - 1)).Face, (W.Q (t - 1)).IsUnbounded F → F = Us) ∧
      (v ∈ stoppedLeftBoundaryVertices w t ↔
        StageLeftBoundaryVertex (W.Q (t - 1)) Us v) := by
  obtain ⟨Us, hUs, hUnique, _⟩ :=
    kmswStage_UL_path_borders_exterior (W.G (t - 1))
  refine ⟨Us, hUs, hUnique, ?_⟩
  rw [stageLeftBoundaryVertex_iff (W.G (t - 1)) Us hUs v]
  rw [stageLeftBoundaryVertices_eq_stopped w (t - 1), Nat.sub_add_cancel ht]

private theorem getD_mem_of_lt {α : Type*} {xs : List α} {i : ℕ} {d : α}
    (hi : i < xs.length) : xs.getD i d ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => exact List.mem_cons_of_mem x (ih (by simp at hi ⊢; omega))

/-- The code-side last-shared criterion transports to the stage and limit
geometric boundaries. Its final exclusion is post-hit only. Helper toward
Lemma 7.9 (`lem-uiqbot-boltzmann`), not a paper result. See -/
theorem stoppedMark_last_shared_geometric
    {w : ℕ → Fin 3} {hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (W : CoherentRealizationWitness w hfin) {r t m ell : ℕ}
    (ht : 1 ≤ t)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (c : KMSWWalkClass ell r t)
    (hprefix : ∀ i : Fin (t - 1), c.val i = w i.val)
    (hmell : m ≤ ell)
    (_hm : m ≤ (L w t).toNat)
    (hcode : mapLeftBoundaryVertex w hfin
      ((stoppedLeftBoundaryVertices w t).getD m 0))
    (hcodeLater : ∀ j, m < j → j ≤ (L w t).toNat →
      ¬ mapLeftBoundaryVertex w hfin
        ((stoppedLeftBoundaryVertices w t).getD j 0)) :
    ∃ Us : (W.Q (t - 1)).Face,
      (W.Q (t - 1)).IsUnbounded Us ∧
      StageLeftBoundaryVertex (W.Q (t - 1)) Us
        ((stoppedLeftBoundaryVertices w t).getD m 0) ∧
      TopLeftBoundaryVertex w W.P W.U
        ((stoppedLeftBoundaryVertices w t).getD m 0) ∧
      ∀ j, m < j → j ≤ (L w t).toNat →
        ¬ (StageLeftBoundaryVertex (W.Q (t - 1)) Us
              ((stoppedLeftBoundaryVertices w t).getD j 0) ∧
            TopLeftBoundaryVertex w W.P W.U
              ((stoppedLeftBoundaryVertices w t).getD j 0)) := by
  have hprefix' : ∀ i < t - 1, codeExtend c i = w i := by
    intro i hi
    rw [codeExtend_of_lt c i hi]
    exact hprefix ⟨i, hi⟩
  have hstage : kmswStage (codeExtend c) (t - 1) = kmswStage w (t - 1) :=
    kmswStage_eq_of_prefix _ _ _ hprefix'
  have hrunlen := kmswWalkClassBase_leftDartRun_length ht c
  have hulLen : (kmswStage w (t - 1)).UL.length = ell := by
    have h := hrunlen
    simpa [kmswStageULDartRun, stageDarts, hstage] using h
  have hidx : m < (stageLeftBoundaryVertices w (t - 1)).length := by
    simp [stageLeftBoundaryVertices, hulLen]
    omega
  have hlist : (stoppedLeftBoundaryVertices w t).getD m 0 ∈
      stoppedLeftBoundaryVertices w t := by
    have hmem := getD_mem_of_lt (xs := stageLeftBoundaryVertices w (t - 1))
      (i := m) (d := 0) hidx
    rw [stageLeftBoundaryVertices_eq_stopped w (t - 1), Nat.sub_add_cancel ht]
      at hmem
    exact hmem
  obtain ⟨Us, hUs, hUnique, hstageIff⟩ :=
    stoppedLeftBoundaryVertex_iff_stageLeftBoundaryVertex W ht _
  have hstageM : StageLeftBoundaryVertex (W.Q (t - 1)) Us
      ((stoppedLeftBoundaryVertices w t).getD m 0) :=
    hstageIff.mp hlist
  have htopM : TopLeftBoundaryVertex w W.P W.U
      ((stoppedLeftBoundaryVertices w t).getD m 0) :=
    (topLeftBoundaryVertex_iff_mapLeftBoundaryVertex W htrans hR hL0 _).2 hcode
  refine ⟨Us, hUs, hstageM, htopM, ?_⟩
  intro j hj hjbound hboth
  exact hcodeLater j hj hjbound
    ((topLeftBoundaryVertex_iff_mapLeftBoundaryVertex W htrans hR hL0 _).1 hboth.2)

end DirectedDistances.KMSW
