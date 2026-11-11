module

public import DirectedDistances.KMSW.KMSWWindowEventualCapture
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem rel_stage_congr {u u' : ℕ → Fin 3} {m : ℕ}
    (hcode : ∀ i < m, u i = u' i) : kmswStage u m = kmswStage u' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change kmswStep (kmswStage u m) (u m) = kmswStep (kmswStage u' m) (u' m)
      rw [ih (fun i hi => hcode i (by omega)), hcode m (by omega)]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result. -/
@[expose] def kmswWindowCaptureEventRel (u : ℕ → Fin 3) (m r c : ℕ) : Prop :=
  c < (kmswStage u m).nextVertex ∧
    (∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      2 ≤ v ∧ ∀ k < m, v = (kmswStage u k).nextVertex →
        (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ [])) ∧
    (∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) (r - 1) c,
      ¬ UpperFrontierEndpoint (kmswStage u m) v)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
The entire radius ball avoids the upper frontier. -/
@[expose] def kmswWindowCaptureEventStrongRel (u : ℕ → Fin 3) (m r c : ℕ) : Prop :=
  kmswWindowCaptureEventRel u m r c ∧
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      ¬ UpperFrontierEndpoint (kmswStage u m) v

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
The original capture event implies the relaxed event. -/
theorem kmswWindowCaptureEventRel_of_captureEvent (u : ℕ → Fin 3) (m r c : ℕ)
    (hev : kmswWindowCaptureEvent u m r c) : kmswWindowCaptureEventRel u m r c := by
  refine ⟨hev.1, ?_, hev.2.2⟩
  intro v hv
  refine ⟨(hev.2.1 v hv).1, ?_⟩
  intro k hk hcreate
  exact ((hev.2.1 v hv).2 k hk hcreate).1

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
The original strong capture event implies the relaxed strong event. -/
theorem kmswWindowCaptureEventStrongRel_of_captureEventStrong
    (u : ℕ → Fin 3) (m r c : ℕ) (hev : kmswWindowCaptureEventStrong u m r c) :
    kmswWindowCaptureEventStrongRel u m r c := by
  exact ⟨kmswWindowCaptureEventRel_of_captureEvent u m r c hev.1, hev.2⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
Window steps creating a ball vertex at a left seam. -/
@[expose] noncomputable def kmswBallLeftSeamSet
    (u : ℕ → Fin 3) (m r c : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter (fun k =>
    (∃ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      v = (kmswStage u k).nextVertex) ∧
    kmswCodeStep (u k) = .left ∧ (kmswStage u k).UL.dropLast.reverse = [])

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
Only letters with indices strictly below `m` affect the relaxed event. -/
theorem kmswWindowCaptureEventRel_congr (u u' : ℕ → Fin 3) (m r c : ℕ)
    (hcode : ∀ i < m, u i = u' i) :
    kmswWindowCaptureEventRel u m r c ↔ kmswWindowCaptureEventRel u' m r c := by
  have hstage (k : ℕ) (hk : k ≤ m) : kmswStage u k = kmswStage u' k :=
    rel_stage_congr (fun i hi => hcode i (by omega))
  have hdown (v : ℕ) :
      (∀ k < m, v = (kmswStage u k).nextVertex →
        (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ [])) ↔
      (∀ k < m, v = (kmswStage u' k).nextVertex →
        (kmswCodeStep (u' k) = .down → (kmswStage u' k).UR ≠ [])) := by
    constructor
    · intro h k hk hv
      rw [← hstage k (by omega)] at hv ⊢
      rw [← hcode k hk]
      exact h k hk hv
    · intro h k hk hv
      rw [hstage k (by omega)] at hv ⊢
      rw [hcode k hk]
      exact h k hk hv
  unfold kmswWindowCaptureEventRel
  rw [hstage m le_rfl]
  simp_rw [hdown]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
Only letters with indices strictly below `m` affect the relaxed strong event. -/
theorem kmswWindowCaptureEventStrongRel_congr (u u' : ℕ → Fin 3) (m r c : ℕ)
    (hcode : ∀ i < m, u i = u' i) :
    kmswWindowCaptureEventStrongRel u m r c ↔
      kmswWindowCaptureEventStrongRel u' m r c := by
  have hs := rel_stage_congr hcode
  unfold kmswWindowCaptureEventStrongRel
  rw [kmswWindowCaptureEventRel_congr u u' m r c hcode, hs]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
Only letters with indices strictly below `m` affect the seam set. -/
theorem kmswBallLeftSeamSet_congr (u u' : ℕ → Fin 3) (m r c : ℕ)
    (hcode : ∀ i < m, u i = u' i) :
    kmswBallLeftSeamSet u m r c = kmswBallLeftSeamSet u' m r c := by
  classical
  have hstage (k : ℕ) (hk : k ≤ m) : kmswStage u k = kmswStage u' k :=
    rel_stage_congr (fun i hi => hcode i (by omega))
  unfold kmswBallLeftSeamSet
  apply Finset.ext
  intro k
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hk : k < m
  · rw [hstage m le_rfl, hstage k (by omega), hcode k hk]
  · simp only [hk, false_and]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
The relaxed event is a measurable cylinder event in the code stream. -/
theorem measurableSet_kmswWindowCaptureEventRel (m r c : ℕ) :
    MeasurableSet {u : ℕ → Fin 3 | kmswWindowCaptureEventRel u m r c} := by
  let pref : (ℕ → Fin 3) → (Fin m → Fin 3) := fun u i => u i.val
  let extend : (Fin m → Fin 3) → (ℕ → Fin 3) :=
    fun a i => if hi : i < m then a ⟨i, hi⟩ else 0
  let A : Set (Fin m → Fin 3) := {a | kmswWindowCaptureEventRel (extend a) m r c}
  have hpref : Measurable pref :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have heq : {u : ℕ → Fin 3 | kmswWindowCaptureEventRel u m r c} = pref ⁻¹' A := by
    ext u
    change kmswWindowCaptureEventRel u m r c ↔
      kmswWindowCaptureEventRel (extend (pref u)) m r c
    apply kmswWindowCaptureEventRel_congr
    intro i hi
    dsimp only [extend, pref]
    rw [dite_eq_left hi]
  rw [heq]
  exact hA.preimage hpref

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
The relaxed strong event is a measurable cylinder event in the code stream. -/
theorem measurableSet_kmswWindowCaptureEventStrongRel (m r c : ℕ) :
    MeasurableSet {u : ℕ → Fin 3 | kmswWindowCaptureEventStrongRel u m r c} := by
  let pref : (ℕ → Fin 3) → (Fin m → Fin 3) := fun u i => u i.val
  let extend : (Fin m → Fin 3) → (ℕ → Fin 3) :=
    fun a i => if hi : i < m then a ⟨i, hi⟩ else 0
  let A : Set (Fin m → Fin 3) := {a | kmswWindowCaptureEventStrongRel (extend a) m r c}
  have hpref : Measurable pref :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have heq : {u : ℕ → Fin 3 | kmswWindowCaptureEventStrongRel u m r c} =
      pref ⁻¹' A := by
    ext u
    change kmswWindowCaptureEventStrongRel u m r c ↔
      kmswWindowCaptureEventStrongRel (extend (pref u)) m r c
    apply kmswWindowCaptureEventStrongRel_congr
    intro i hi
    dsimp only [extend, pref]
    rw [dite_eq_left hi]
  rw [heq]
  exact hA.preimage hpref

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
the left non-seam clause; left seams are certified separately; not the paper result.
Each specified seam set gives a measurable cylinder event in the code stream. -/
theorem measurableSet_kmswBallLeftSeamSet (m r c : ℕ) (S : Finset ℕ) :
    MeasurableSet {u : ℕ → Fin 3 | kmswBallLeftSeamSet u m r c = S} := by
  let pref : (ℕ → Fin 3) → (Fin m → Fin 3) := fun u i => u i.val
  let extend : (Fin m → Fin 3) → (ℕ → Fin 3) :=
    fun a i => if hi : i < m then a ⟨i, hi⟩ else 0
  let A : Set (Fin m → Fin 3) := {a | kmswBallLeftSeamSet (extend a) m r c = S}
  have hpref : Measurable pref :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have heq : {u : ℕ → Fin 3 | kmswBallLeftSeamSet u m r c = S} = pref ⁻¹' A := by
    ext u
    change kmswBallLeftSeamSet u m r c = S ↔
      kmswBallLeftSeamSet (extend (pref u)) m r c = S
    have hs : kmswBallLeftSeamSet u m r c =
        kmswBallLeftSeamSet (extend (pref u)) m r c := by
      apply kmswBallLeftSeamSet_congr
      intro i hi
      dsimp only [extend, pref]
      rw [dite_eq_left hi]
    rw [hs]
  rw [heq]
  exact hA.preimage hpref

end DirectedDistances.KMSW
