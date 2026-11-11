module

public import DirectedDistances.KMSW.KMSWWholePlaneFaces

public section
namespace DirectedDistances.KMSW

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
@[expose] def shiftWord (W : ℤ → Fin 3) (n : ℕ) : ℤ → Fin 3 :=
  fun k => W (k + (n : ℤ))

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem shiftedStream_shiftWord (W : ℤ → Fin 3) (n N : ℕ) :
    shiftedStream (shiftWord W n) (N + n) = shiftedStream W N := by
  funext i
  unfold shiftedStream shiftWord
  congr 1
  omega

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneVertexTrans_shiftWord (W : ℤ → Fin 3) (n N M : ℕ)
    (h : N ≤ M) :
    wholePlaneVertexTrans (shiftWord W n) (N + n) (M + n) (Nat.add_le_add_right h n) =
      wholePlaneVertexTrans W N M h := by
  unfold wholePlaneVertexTrans
  rw [shiftedStream_shiftWord, Nat.add_sub_add_right]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneEdgeTrans_shiftWord (W : ℤ → Fin 3) (n N M : ℕ)
    (h : N ≤ M) :
    wholePlaneEdgeTrans (shiftWord W n) (N + n) (M + n) (Nat.add_le_add_right h n) =
      wholePlaneEdgeTrans W N M h := by
  unfold wholePlaneEdgeTrans
  rw [shiftedStream_shiftWord, Nat.add_sub_add_right]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneDartTrans_shiftWord (W : ℤ → Fin 3) (n N M : ℕ)
    (h : N ≤ M) :
    wholePlaneDartTrans (shiftWord W n) (N + n) (M + n) (Nat.add_le_add_right h n) =
      wholePlaneDartTrans W N M h := by
  funext d
  exact Prod.ext (congrFun (wholePlaneEdgeTrans_shiftWord W n N M h) d.1) rfl

private theorem vertexShift_rel (W : ℤ → Fin 3) (n : ℕ)
    (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneVertexRel W a b) :
    wholePlaneVertexι (shiftWord W n) (a.1 + n) a.2 =
      wholePlaneVertexι (shiftWord W n) (b.1 + n) b.2 := by
  obtain ⟨M, ha, hb, he⟩ := hab
  apply Quotient.sound
  refine ⟨M + n, Nat.add_le_add_right ha n, Nat.add_le_add_right hb n, ?_⟩
  simpa only [wholePlaneVertexTrans, shiftedStream_shiftWord,
      Nat.add_sub_add_right] using he

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
@[expose] def wholePlaneVertexShift (W : ℤ → Fin 3) (n : ℕ) :
    WholePlaneVertex W → WholePlaneVertex (shiftWord W n) :=
  Quotient.lift (fun a => wholePlaneVertexι (shiftWord W n) (a.1 + n) a.2)
    (by
      intro a b hab
      exact vertexShift_rel W n a b hab)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneVertexShift_ι (W : ℤ → Fin 3) (n N v : ℕ) :
    wholePlaneVertexShift W n (wholePlaneVertexι W N v) =
      wholePlaneVertexι (shiftWord W n) (N + n) v := rfl

private theorem edgeShift_rel (W : ℤ → Fin 3) (n : ℕ)
    (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) :
    wholePlaneEdgeι (shiftWord W n) (a.1 + n) a.2 =
      wholePlaneEdgeι (shiftWord W n) (b.1 + n) b.2 := by
  obtain ⟨M, ha, hb, he⟩ := hab
  apply Quotient.sound
  refine ⟨M + n, Nat.add_le_add_right ha n, Nat.add_le_add_right hb n, ?_⟩
  simpa only [wholePlaneEdgeTrans, shiftedStream_shiftWord,
      Nat.add_sub_add_right] using he

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
@[expose] def wholePlaneEdgeShift (W : ℤ → Fin 3) (n : ℕ) :
    WholePlaneEdge W → WholePlaneEdge (shiftWord W n) :=
  Quotient.lift (fun a => wholePlaneEdgeι (shiftWord W n) (a.1 + n) a.2)
    (by
      intro a b hab
      exact edgeShift_rel W n a b hab)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneEdgeShift_ι (W : ℤ → Fin 3) (n N v : ℕ) :
    wholePlaneEdgeShift W n (wholePlaneEdgeι W N v) =
      wholePlaneEdgeι (shiftWord W n) (N + n) v := rfl

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
@[expose] def wholePlaneDartShift (W : ℤ → Fin 3) (n : ℕ) :
    WholePlaneDart W → WholePlaneDart (shiftWord W n) :=
  fun d => (wholePlaneEdgeShift W n d.1, d.2)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneDartShift_ι (W : ℤ → Fin 3) (n N : ℕ) (d : ℕ × Bool) :
    wholePlaneDartShift W n (wholePlaneDartι W N d) =
      wholePlaneDartι (shiftWord W n) (N + n) d := rfl

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneVertexShift_bijective (W : ℤ → Fin 3) (n : ℕ) :
    Function.Bijective (wholePlaneVertexShift W n) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    rintro ⟨N, v⟩ ⟨M, z⟩ he
    obtain ⟨L, hN, hM, he⟩ := Quotient.exact he
    dsimp only at hN hM he
    obtain ⟨K, rfl⟩ : ∃ K, L = K + n := ⟨L - n, by omega⟩
    have hNK : N ≤ K := by omega
    have hMK : M ≤ K := by omega
    apply Quotient.sound
    refine ⟨K, hNK, hMK, ?_⟩
    simpa only [wholePlaneVertexTrans, shiftedStream_shiftWord,
      Nat.add_sub_add_right] using he
  · intro y
    refine Quotient.inductionOn y ?_
    rintro ⟨N, v⟩
    refine ⟨wholePlaneVertexι W N
      (wholePlaneVertexTrans (shiftWord W n) N (N + n) (by omega) v), ?_⟩
    exact congrFun (wholePlaneVertexι_trans (shiftWord W n) N (N + n) (by omega)) v

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneEdgeShift_bijective (W : ℤ → Fin 3) (n : ℕ) :
    Function.Bijective (wholePlaneEdgeShift W n) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    rintro ⟨N, v⟩ ⟨M, z⟩ he
    obtain ⟨L, hN, hM, he⟩ := Quotient.exact he
    dsimp only at hN hM he
    obtain ⟨K, rfl⟩ : ∃ K, L = K + n := ⟨L - n, by omega⟩
    have hNK : N ≤ K := by omega
    have hMK : M ≤ K := by omega
    apply Quotient.sound
    refine ⟨K, hNK, hMK, ?_⟩
    simpa only [wholePlaneEdgeTrans, shiftedStream_shiftWord,
      Nat.add_sub_add_right] using he
  · intro y
    refine Quotient.inductionOn y ?_
    rintro ⟨N, v⟩
    refine ⟨wholePlaneEdgeι W N
      (wholePlaneEdgeTrans (shiftWord W n) N (N + n) (by omega) v), ?_⟩
    exact congrFun (wholePlaneEdgeι_trans (shiftWord W n) N (N + n) (by omega)) v

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneDartShift_bijective (W : ℤ → Fin 3) (n : ℕ) :
    Function.Bijective (wholePlaneDartShift W n) := by
  constructor
  · rintro ⟨e, b⟩ ⟨f, c⟩ h
    exact Prod.ext ((wholePlaneEdgeShift_bijective W n).1 (congrArg Prod.fst h))
      (show b = c from congrArg Prod.snd h)
  · rintro ⟨e, b⟩
    obtain ⟨f, hf⟩ := (wholePlaneEdgeShift_bijective W n).2 e
    exact ⟨(f, b), Prod.ext hf rfl⟩

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
@[expose] noncomputable def wholePlaneVertexShiftEquiv (W : ℤ → Fin 3) (n : ℕ) :
    WholePlaneVertex W ≃ WholePlaneVertex (shiftWord W n) :=
  Equiv.ofBijective (wholePlaneVertexShift W n) (wholePlaneVertexShift_bijective W n)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
@[expose] noncomputable def wholePlaneEdgeShiftEquiv (W : ℤ → Fin 3) (n : ℕ) :
    WholePlaneEdge W ≃ WholePlaneEdge (shiftWord W n) :=
  Equiv.ofBijective (wholePlaneEdgeShift W n) (wholePlaneEdgeShift_bijective W n)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
@[expose] noncomputable def wholePlaneDartShiftEquiv (W : ℤ → Fin 3) (n : ℕ) :
    WholePlaneDart W ≃ WholePlaneDart (shiftWord W n) :=
  Equiv.ofBijective (wholePlaneDartShift W n) (wholePlaneDartShift_bijective W n)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneEdgeShift_west (W : ℤ → Fin 3) (n : ℕ) (e : WholePlaneEdge W) :
    wholePlaneEdgeWest (shiftWord W n) (wholePlaneEdgeShift W n e) =
      wholePlaneVertexShift W n (wholePlaneEdgeWest W e) := by
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change wholePlaneVertexι (shiftWord W n) (N + n)
    (edgeWest (shiftedStream (shiftWord W n) (N + n)) e) =
      wholePlaneVertexι (shiftWord W n) (N + n) (edgeWest (shiftedStream W N) e)
  rw [shiftedStream_shiftWord]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneEdgeShift_east (W : ℤ → Fin 3) (n : ℕ) (e : WholePlaneEdge W) :
    wholePlaneEdgeEast (shiftWord W n) (wholePlaneEdgeShift W n e) =
      wholePlaneVertexShift W n (wholePlaneEdgeEast W e) := by
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change wholePlaneVertexι (shiftWord W n) (N + n)
    (edgeEast (shiftedStream (shiftWord W n) (N + n)) e) =
      wholePlaneVertexι (shiftWord W n) (N + n) (edgeEast (shiftedStream W N) e)
  rw [shiftedStream_shiftWord]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneEdgePresent_shift (W : ℤ → Fin 3) (n : ℕ) (e : WholePlaneEdge W) :
    wholePlaneEdgePresent (shiftWord W n) (wholePlaneEdgeShift W n e) ↔
      wholePlaneEdgePresent W e := by
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change wholePlaneEdgePresent (shiftWord W n)
    (wholePlaneEdgeι (shiftWord W n) (N + n) e) ↔
      wholePlaneEdgePresent W (wholePlaneEdgeι W N e)
  rw [wholePlaneEdgePresent_ι, wholePlaneEdgePresent_ι]
  constructor
  · rintro ⟨M, hNM, hp⟩
    obtain ⟨K, rfl⟩ : ∃ K, M = K + n := ⟨M - n, by omega⟩
    refine ⟨K, by omega, fun L hKL => ?_⟩
    have h := hp (L + n) (Nat.add_le_add_right hKL n)
    simpa only [wholePlaneEdgeTrans, shiftedStream_shiftWord,
      Nat.add_sub_add_right] using h
  · rintro ⟨M, hNM, hp⟩
    refine ⟨M + n, Nat.add_le_add_right hNM n, fun L hML => ?_⟩
    obtain ⟨K, rfl⟩ : ∃ K, L = K + n := ⟨L - n, by omega⟩
    have h := hp K (by omega)
    simpa only [wholePlaneEdgeTrans, shiftedStream_shiftWord,
      Nat.add_sub_add_right] using h

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneFresh_shiftWord (W : ℤ → Fin 3) (n N M : ℕ)
    (h : N ≤ M) (v : ℕ) :
    wholePlaneFresh (shiftWord W n) (N + n) (M + n) (Nat.add_le_add_right h n) v ↔
      wholePlaneFresh W N M h v := by
  unfold wholePlaneFresh
  rw [shiftedStream_shiftWord, Nat.add_sub_add_right, wholePlaneVertexTrans_shiftWord]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneRotationHypothesis_of_shiftWord (W : ℤ → Fin 3) (n : ℕ)
    (H' : WholePlaneRotationHypothesis (shiftWord W n)) : WholePlaneRotationHypothesis W := by
  constructor
  · intro N
    have h := H'.1 (N + n)
    simpa only [shiftedStream_shiftWord] using h
  · intro N v
    obtain ⟨M, hNM, hf⟩ := H'.2 (N + n) v
    obtain ⟨K, rfl⟩ : ∃ K, M = K + n := ⟨M - n, by omega⟩
    refine ⟨K, by omega, fun L hKL => ?_⟩
    have h := hf (L + n) (Nat.add_le_add_right hKL n)
    simpa only [wholePlaneFresh, wholePlaneVertexTrans, shiftedStream_shiftWord,
      Nat.add_sub_add_right] using h

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem kmswInfRot_congr_stream {w w' : ℕ → Fin 3} (hw : w = w')
    (h : KMSWFiniteIncidence w) : kmswInfRot w h = kmswInfRot w' (hw ▸ h) := by
  subst w'
  rfl

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneRotation_shift (W : ℤ → Fin 3) (n : ℕ)
    (H' : WholePlaneRotationHypothesis (shiftWord W n)) (x : WholePlaneDart W) :
    wholePlaneDartShiftEquiv W n
        (wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H') x) =
      wholePlaneRotation (shiftWord W n) H' (wholePlaneDartShiftEquiv W n x) := by
  let H := wholePlaneRotationHypothesis_of_shiftWord W n H'
  obtain ⟨q, b⟩ := x
  refine Quotient.inductionOn q ?_
  rintro ⟨N, e⟩
  change wholePlaneDartShift W n (wholePlaneRot W H (wholePlaneDartι W N (e, b))) =
    wholePlaneRot (shiftWord W n) H' (wholePlaneDartι (shiftWord W n) (N + n) (e, b))
  obtain ⟨M, hNM, hM⟩ := wholePlaneRot_eventually W H N (e, b)
  obtain ⟨L, hNL, hL⟩ :=
    wholePlaneRot_eventually (shiftWord W n) H' (N + n) (e, b)
  let K := max M L
  have hMK : M ≤ K := Nat.le_max_left M L
  have hLK : L ≤ K + n := by dsimp only [K]; omega
  have hx := congrArg (wholePlaneDartShift W n) (hM K hMK)
  rw [wholePlaneDartShift_ι] at hx
  have hy := hL (K + n) hLK
  have ht : wholePlaneDartTrans (shiftWord W n) (N + n) (K + n)
      (hNL.trans hLK) (e, b) =
      wholePlaneDartTrans W N K (hNM.trans hMK) (e, b) :=
    congrFun (wholePlaneDartTrans_shiftWord W n N K (hNM.trans hMK)) (e, b)
  have hr : kmswInfRot (shiftedStream (shiftWord W n) (K + n)) (H'.1 (K + n)) =
      kmswInfRot (shiftedStream W K) (H.1 K) :=
    kmswInfRot_congr_stream (shiftedStream_shiftWord W n K) (H'.1 (K + n))
  rw [ht, hr] at hy
  exact hx.symm.trans hy

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneRotation_symm_shift (W : ℤ → Fin 3) (n : ℕ)
    (H' : WholePlaneRotationHypothesis (shiftWord W n)) (x : WholePlaneDart W) :
    wholePlaneDartShiftEquiv W n
        ((wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H')).symm x) =
      (wholePlaneRotation (shiftWord W n) H').symm (wholePlaneDartShiftEquiv W n x) := by
  apply (wholePlaneRotation (shiftWord W n) H').injective
  rw [Equiv.apply_symm_apply]
  have h := wholePlaneRotation_shift W n H'
    ((wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H')).symm x)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

private theorem perm_pow_intertwine {α β : Type*} (f : α → β)
    (r : Equiv.Perm α) (s : Equiv.Perm β) (h : ∀ x, f (r x) = s (f x))
    (k : ℕ) (x : α) : f ((r ^ k) x) = (s ^ k) (f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, h, ih, pow_succ', Equiv.Perm.mul_apply]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneRotation_pow_shift (W : ℤ → Fin 3) (n : ℕ)
    (H' : WholePlaneRotationHypothesis (shiftWord W n)) (k : ℕ) (x : WholePlaneDart W) :
    wholePlaneDartShiftEquiv W n
        ((wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H') ^ k) x) =
      (wholePlaneRotation (shiftWord W n) H' ^ k) (wholePlaneDartShiftEquiv W n x) := by
  exact perm_pow_intertwine (wholePlaneDartShiftEquiv W n)
    (wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H'))
    (wholePlaneRotation (shiftWord W n) H') (wholePlaneRotation_shift W n H') k x

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneRotation_symm_pow_shift (W : ℤ → Fin 3) (n : ℕ)
    (H' : WholePlaneRotationHypothesis (shiftWord W n)) (k : ℕ) (x : WholePlaneDart W) :
    wholePlaneDartShiftEquiv W n
        (((wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H')).symm ^ k)
          x) =
      ((wholePlaneRotation (shiftWord W n) H').symm ^ k) (wholePlaneDartShiftEquiv W n x) := by
  exact perm_pow_intertwine (wholePlaneDartShiftEquiv W n)
    (wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H')).symm
    (wholePlaneRotation (shiftWord W n) H').symm (wholePlaneRotation_symm_shift W n H') k x

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
isomorphism of the whole-plane colimit for paper starts n > 0; not the paper result. -/
theorem wholePlaneRotation_zpow_shift (W : ℤ → Fin 3) (n : ℕ)
    (H' : WholePlaneRotationHypothesis (shiftWord W n)) (k : ℤ) (x : WholePlaneDart W) :
    wholePlaneDartShiftEquiv W n
        ((wholePlaneRotation W (wholePlaneRotationHypothesis_of_shiftWord W n H') ^ k) x) =
      (wholePlaneRotation (shiftWord W n) H' ^ k) (wholePlaneDartShiftEquiv W n x) := by
  cases k with
  | ofNat k =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using wholePlaneRotation_pow_shift W n H' k x
  | negSucc k =>
    simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using
      wholePlaneRotation_symm_pow_shift W n H' (k + 1) x

end DirectedDistances.KMSW
