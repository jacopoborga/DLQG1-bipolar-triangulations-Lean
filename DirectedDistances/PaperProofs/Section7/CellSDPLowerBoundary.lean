module

public import DirectedDistances.PaperProofs.Section7.CellLDPLowerAlignment
public import DirectedDistances.RandomWalk.CellLDPLowerBoundaryTime
public import DirectedDistances.RandomWalk.CellSDPLowerBdy
public import DirectedDistances.KMSW.RunBoundaryVertexLabels
public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.RightStationaryGeometry

/-! Supporting lemmas for paper labels `lem-cell-sdp-lower` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW DirectedDistances.RandomWalk



theorem boundaryHitTime_shift_eq_codeSndFirstHit (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℕ) (hk : 1 ≤ k) :
    ((boundaryHitTime (fun i => ω (i + 1)) h (k : ℤ) : ℕ) : ℕ∞) =
      RandomWalk.codeSndFirstHit (-(k : ℤ)) ω := by
  classical
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let a : ℤ := -(k : ℤ)
  have hsource : ∃ n, R w n = a := h.rightHit (k : ℤ) (by exact_mod_cast hk)
  have hwalk (n : ℕ) : R w n = (RandomWalk.codeWalk ω n).2 := by
    simpa [w] using (show R (fun i => ω (i + 1)) n =
      (RandomWalk.codeWalk ω n).2 by
        simp [R, RandomWalk.codeWalk, Prod.snd_sum])
  have hcode : ∃ n, (RandomWalk.codeWalk ω n).2 = a := by
    obtain ⟨n, hn⟩ := hsource
    exact ⟨n, by rw [← hwalk n]; exact hn⟩
  have hfind : Nat.find hsource = Nat.find hcode := by
    apply le_antisymm
    · have hc : R w (Nat.find hcode) = a := by
        rw [hwalk]
        exact Nat.find_spec hcode
      exact Nat.find_min' hsource hc
    · have hs : (RandomWalk.codeWalk ω (Nat.find hsource)).2 = a := by
        rw [← hwalk]
        exact Nat.find_spec hsource
      exact Nat.find_min' hcode hs
  have htime : boundaryHitTime w h (k : ℤ) = Nat.find hsource := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : (k : ℤ) ≠ 0),
      dite_eq_left (by omega : 0 < (k : ℤ))]
  rw [htime]
  unfold RandomWalk.codeSndFirstHit
  rw [dite_eq_left hcode, hfind]



theorem boundaryHitTime_le_of_codeSndFirstHit_le (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k N : ℕ) (hk : 1 ≤ k)
    (hN : RandomWalk.codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)) :
    boundaryHitTime (fun i => ω (i + 1)) h (k : ℤ) ≤ N := by
  rw [← boundaryHitTime_shift_eq_codeSndFirstHit ω h k hk] at hN
  exact ENat.natCast_le_natCast.mp hN



theorem codeSndFirstHit_le_prob_ge (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    1 - 4 * (k : ℝ) / Real.sqrt N ≤
      iidCodeMeasure.real {ω | RandomWalk.codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} :=
  _root_.DirectedDistances.RandomWalk.codeSndFirstHit_le_prob_ge k N hk hN

private theorem lr_mem_mono {w : ℕ → Fin 3} {m n e : ℕ} (hmn : m ≤ n)
    (he : e ∈ (kmswStage w m).LR) : e ∈ (kmswStage w n).LR := by
  induction n, hmn using Nat.le_induction with
  | base => exact he
  | succ n _ ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w n
    rw [ht]
    exact List.mem_append_left _ ih

private theorem right_hit_active_mem_LR (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    act w (boundaryHitTime w h k) ∈
      (kmswStage w (boundaryHitTime w h k)).LR := by
  let τ := boundaryHitTime w h k
  have hτpos : 0 < τ := by
    by_contra hn
    have hτ0 : τ = 0 := by omega
    have hh := boundaryHitTime_right_spec w h hk
    change boundaryHitTime w h k = 0 at hτ0
    rw [hτ0] at hh
    simp [R] at hh
    omega
  have hτfind : τ = Nat.find (h.rightHit k hk) := by
    dsimp [τ, boundaryHitTime]
    simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_left (by omega : 0 < k)]
  have hno : ∀ j < τ, R w j ≠ -k := by
    intro j hj heq
    rw [hτfind] at hj
    exact (Nat.find_min' (h.rightHit k hk) heq).not_gt hj
  have hstrict : ∀ j < τ, -k < R w j := by
    intro j hj
    induction j with
    | zero => simp [R]; omega
    | succ j ih =>
      have hprev := ih (by omega)
      have hstep : R w j - 1 ≤ R w (j + 1) := by
        rw [show R w (j + 1) = R w j +
          (RandomWalk.lazyTwoDimensionalStep (w j)).2 by exact Finset.sum_range_succ _ _]
        have hb : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).2 := by
          unfold RandomWalk.lazyTwoDimensionalStep
          split_ifs <;> omega
        omega
      have hnot := hno (j + 1) (by omega)
      omega
  let m := τ - 1
  have hτeq : τ = m + 1 := by dsimp [m]; omega
  have hspec : R w τ = -k := by
    simpa [τ] using boundaryHitTime_right_spec w h hk
  have hsum : R w (m + 1) = R w m +
      (RandomWalk.lazyTwoDimensionalStep (w m)).2 := Finset.sum_range_succ _ _
  rw [← hτeq] at hsum
  have hmval : R w m = -k + 1 := by
    have hlt := hstrict m (by omega)
    have hb : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w m)).2 := by
      unfold RandomWalk.lazyTwoDimensionalStep
      split_ifs <;> omega
    rw [hsum] at hspec
    omega
  have hmin : minR w m = R w m := by
    obtain ⟨i, hi, heq⟩ := runningMin_attained (R w) m
    change minR w m = R w i at heq
    have hle := runningMin_le (R w) m m le_rfl
    change minR w m ≤ R w m at hle
    have hlow : -k + 1 ≤ R w i := by
      have hiτ : i < τ := by omega
      have := hstrict i hiτ
      omega
    omega
  have hURlen : (kmswStage w m).UR.length = 0 := by
    have hlen := kmswStage_UR_length w m
    rw [hmval, hmin] at hlen
    have : ((kmswStage w m).UR.length : ℤ) = 0 := by omega
    exact_mod_cast this
  have hUR : (kmswStage w m).UR = [] := List.length_eq_zero_iff.mp hURlen
  have hdown : w m = 2 := by
    have hstep : (RandomWalk.lazyTwoDimensionalStep (w m)).2 = -1 := by
      rw [hsum, hmval] at hspec
      omega
    have hc : w m = 0 ∨ w m = 1 ∨ w m = 2 := by
      have := (w m).isLt
      omega
    rcases hc with h0 | h1 | h2
    · simp [h0, RandomWalk.lazyTwoDimensionalStep] at hstep
    · simp [h1, RandomWalk.lazyTwoDimensionalStep] at hstep
    · exact h2
  have hstage : kmswStage w τ = kmswStepOfStep (kmswStage w m) .down := by
    rw [hτeq]
    change kmswStep (kmswStage w m) (w m) = _
    rw [hdown]
    simp [kmswStep, kmswCodeStep]
  have hact : act w τ = (kmswStage w m).nextEdge := by
    change (kmswStage w τ).active = _
    rw [hstage]
    simp [kmswStepOfStep, hUR, State.addEdge]
  rw [hact, hstage]
  simp [kmswStepOfStep, hUR]




theorem boundaryVertex_mem_LR_endpoint_of_hit {w : ℕ → Fin 3}
    (h : BoundaryHitWitnesses w) {K n r : ℕ} (hr : 1 ≤ r)
    (hrK : r ≤ K) (ht : boundaryHitTime w h (K : ℤ) ≤ n) :
    ∃ e ∈ (kmswStage w n).LR,
      (kmswStage w n).west e = boundaryVertex w h (r : ℤ) ∨
        (kmswStage w n).east e = boundaryVertex w h (r : ℤ) := by
  by_cases hr1 : r = 1
  · subst r
    refine ⟨0, ?_, Or.inr ?_⟩
    · exact lr_mem_mono (Nat.zero_le n) (by simp [kmswStage, kmswInit])
    · exact (initial_edge_endpoints w n).2.trans (boundaryVertex_one w h).symm
  · have hrZ : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    have hrKZ : (r : ℤ) ≤ (K : ℤ) := by exact_mod_cast hrK
    have hmono := boundaryHitTime_right_mono w h
      (a := (r : ℤ)) (b := (K : ℤ)) hrZ hrKZ
    have htime : boundaryHitTime w h (r : ℤ) ≤ n := hmono.trans ht
    let τ := boundaryHitTime w h (r : ℤ)
    have hmem := right_hit_active_mem_LR w h (k := (r : ℤ)) hrZ
    have hmem' : act w τ ∈ (kmswStage w τ).LR := by simpa [τ] using hmem
    have hmemn := lr_mem_mono htime hmem'
    have hwest := boundaryVertex_right_hit_eq w h (k := (r : ℤ)) hrZ
    refine ⟨act w τ, hmemn, Or.inl ?_⟩
    calc
      (kmswStage w n).west (act w τ) = (kmswStage w τ).west (act w τ) :=
        (kmswStage_endpoints_stable w htime (act_lt_nextEdge w le_rfl)).1
      _ = activeInitial w τ := (CutConverse.activeInitial_eq w τ).symm
      _ = boundaryVertex w h (r : ℤ) := by simpa [τ] using hwest.symm




theorem boundaryVertices_mem_LR_prob_ge (K n : ℕ) (hK : 1 ≤ K) (hn : 1 ≤ n) :
    1 - 4 * (K : ℝ) / Real.sqrt n ≤
      iidCodeMeasure.real {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ r, 1 ≤ r → r ≤ K →
          ∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
              (kmswStage (fun i => ω (i + 1)) n).east e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)} := by
  have hhit := _root_.DirectedDistances.RandomWalk.codeSndFirstHit_le_prob_ge K n hK hn
  have hsubset : {ω | RandomWalk.codeSndFirstHit (-(K : ℤ)) ω ≤ (n : ℕ∞)} ≤ᵐ[iidCodeMeasure]
      {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ r, 1 ≤ r → r ≤ K →
          ∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
              (kmswStage (fun i => ω (i + 1)) n).east e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)} := by
    filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω hω hωhit
    refine ⟨hω, fun r hr hrK => ?_⟩
    have ht := boundaryHitTime_le_of_codeSndFirstHit_le ω hω K n hK hωhit
    exact boundaryVertex_mem_LR_endpoint_of_hit hω hr hrK ht
  have hmono := MeasureTheory.measure_mono_ae hsubset
  have hreal := ENNReal.toReal_mono (by finiteness) hmono
  exact hhit.trans hreal

end DirectedDistances.PaperProofs.Section7

