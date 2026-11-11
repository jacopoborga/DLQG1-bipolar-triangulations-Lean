module

public import DirectedDistances.KMSW.CutEquivalenceConverse
public import DirectedDistances.KMSW.KMSWWindowCaptureEventRel
public import DirectedDistances.KMSW.MeasurableCutEvents

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW





theorem activeInitial_congr {u u' : ℕ → Fin 3} {n : ℕ}
    (h : ∀ i < n, u i = u' i) : activeInitial u n = activeInitial u' n := by
  rw [CutConverse.activeInitial_eq, CutConverse.activeInitial_eq]
  change (kmswStage u n).west (kmswStage u n).active =
    (kmswStage u' n).west (kmswStage u' n).active
  rw [kmswStage_congr h]





@[expose] noncomputable def kmswBallLeftSeamKmax
    (u : ℕ → Fin 3) (m r c t0 : ℕ) : ℕ :=
  (kmswBallLeftSeamSet u m r c).sup (fun k => (L u k - L u t0).toNat)





theorem kmswBallLeftSeamKmax_le_iff (u : ℕ → Fin 3) (m r c t0 K0 : ℕ) :
    kmswBallLeftSeamKmax u m r c t0 ≤ K0 ↔
      ∀ k ∈ kmswBallLeftSeamSet u m r c, L u k - L u t0 ≤ (K0 : ℤ) := by
  classical
  unfold kmswBallLeftSeamKmax
  rw [Finset.sup_le_iff]
  have htoNat (z : ℤ) : z.toNat ≤ K0 ↔ z ≤ (K0 : ℤ) := by
    cases z with
    | ofNat n => simp [Int.toNat]
    | negSucc n => simp [Int.toNat]; omega
  constructor
  · intro h k hk
    exact (htoNat (L u k - L u t0)).mp (h k hk)
  · intro h k hk
    exact (htoNat (L u k - L u t0)).mpr (h k hk)






@[expose] def kmswWindowCaptureEventK (N r K0 : ℕ) (u : ℕ → Fin 3) : Prop :=
  kmswWindowCaptureEventStrongRel u (2 * N) r (activeInitial u N) ∧
    kmswBallLeftSeamKmax u (2 * N) r (activeInitial u N) N ≤ K0

private theorem kmswBallLeftSeamKmax_congr (u u' : ℕ → Fin 3)
    (m r c t0 : ℕ) (ht0 : t0 ≤ m) (hcode : ∀ i < m, u i = u' i) :
    kmswBallLeftSeamKmax u m r c t0 = kmswBallLeftSeamKmax u' m r c t0 := by
  classical
  unfold kmswBallLeftSeamKmax
  rw [kmswBallLeftSeamSet_congr u u' m r c hcode]
  apply Finset.sup_congr rfl
  intro k hk
  rw [L_congr (fun i hi => hcode i (by
    have hklt := (Finset.mem_filter.mp hk).1
    have hklt' := Finset.mem_range.mp hklt
    omega)),
    L_congr (fun i hi => hcode i (by omega))]





theorem kmswWindowCaptureEventK_congr (N r K0 : ℕ) (u u' : ℕ → Fin 3)
    (h : ∀ i < 2 * N, u i = u' i) :
    kmswWindowCaptureEventK N r K0 u ↔ kmswWindowCaptureEventK N r K0 u' := by
  unfold kmswWindowCaptureEventK
  rw [kmswWindowCaptureEventStrongRel_congr u u' (2 * N) r
    (activeInitial u N) h]
  have hroot : activeInitial u N = activeInitial u' N :=
    activeInitial_congr (fun i hi => h i (by omega))
  rw [hroot]
  rw [kmswBallLeftSeamKmax_congr u u' (2 * N) r (activeInitial u' N) N
    (by omega) h]





theorem measurableSet_kmswWindowCaptureEventK (N r K0 : ℕ) :
    MeasurableSet {u : ℕ → Fin 3 | kmswWindowCaptureEventK N r K0 u} := by
  let pref : (ℕ → Fin 3) → (Fin (2 * N) → Fin 3) := fun u i => u i.val
  let extend : (Fin (2 * N) → Fin 3) → (ℕ → Fin 3) :=
    fun a i => if hi : i < 2 * N then a ⟨i, hi⟩ else 0
  let A : Set (Fin (2 * N) → Fin 3) :=
    {a | kmswWindowCaptureEventK N r K0 (extend a)}
  have hpref : Measurable pref := Measurable.of_eval fun i => measurable_pi_apply i.val
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have heq : {u : ℕ → Fin 3 | kmswWindowCaptureEventK N r K0 u} = pref ⁻¹' A := by
    ext u
    change kmswWindowCaptureEventK N r K0 u ↔
      kmswWindowCaptureEventK N r K0 (extend (pref u))
    apply kmswWindowCaptureEventK_congr
    intro i hi
    dsimp only [extend, pref]
    rw [dite_eq_left hi]
  rw [heq]
  exact hA.preimage hpref





theorem kmswWindowCaptureEventK_mono (N r K K' : ℕ) (u : ℕ → Fin 3)
    (h : K ≤ K') (hev : kmswWindowCaptureEventK N r K u) :
    kmswWindowCaptureEventK N r K' u := by
  exact ⟨hev.1, hev.2.trans h⟩

end DirectedDistances.KMSW
