module

public import DirectedDistances.PaperProofs.Section7.CellSDPLowerUpperUnconditional
import DirectedDistances.PaperProofs.Section7.CellLDPUpperRouteUp
import DirectedDistances.KMSW.StageIncidenceChains
import Mathlib.Data.Int.Interval

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/





















public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem upper_left_record_time (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : q ≤ -1) (hvalue : L w m = q)
    (hrecord : ∀ j < m, q < L w j) :
    boundaryHitTime w h q = m := by
  have hle : boundaryHitTime w h q ≤ m := by
    have ht : boundaryHitTime w h q = Nat.find (h.leftHit q hq) := by
      simp only [boundaryHitTime, dite_eq_right (by omega : q ≠ 0),
        dite_eq_right (by omega : ¬ 0 < q)]
    rw [ht]
    exact Nat.find_min' (h.leftHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_left_spec w h hq
    have hstrict := hrecord (boundaryHitTime w h q) hlt
    rw [hfirst] at hstrict
    exact (lt_irrefl q) hstrict
  omega

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem upper_right_record_time (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : 1 ≤ q) (hvalue : R w m = -q)
    (hrecord : ∀ j < m, R w m < R w j) :
    boundaryHitTime w h q = m := by
  have hle : boundaryHitTime w h q ≤ m := by
    have ht : boundaryHitTime w h q = Nat.find (h.rightHit q hq) := by
      simp only [boundaryHitTime, dite_eq_right (by omega : q ≠ 0),
        dite_eq_left (by omega : 0 < q)]
    rw [ht]
    exact Nat.find_min' (h.rightHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_right_spec w h hq
    have hstrict := hrecord (boundaryHitTime w h q) hlt
    rw [hvalue] at hstrict
    rw [hfirst] at hstrict
    exact (lt_irrefl (-q)) hstrict
  omega

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem finite_LL_label (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n e v : ℕ) (heLL : e ∈ (kmswStage w n).LL)
    (hend : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ k : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ k ∧ k ≤ 0 ∧
      boundaryVertex w h k = v := by
  rw [kmswStage_LL_eq] at heLL
  obtain ⟨m, hm, heq⟩ := List.mem_map.mp heLL
  have hm' := List.mem_reverse.mp hm
  have hcond : 0 < m ∧ ∀ j < m, L w m < L w j :=
    of_decide_eq_true (List.mem_filter.mp hm').2
  have hmle : m ≤ n := by
    have := List.mem_range.mp (List.mem_filter.mp hm').1
    omega
  let q := L w m
  have hq : q ≤ -1 := by
    have hzero : L w 0 = 0 := by simp [L]
    have hrec0 := hcond.2 0 (by omega)
    dsimp [q]
    omega
  have hmin := runningMin_le (L w) n m hmle
  have hlen := kmswStage_LL_length w n
  change minL w n ≤ L w m at hmin
  have htime : boundaryHitTime w h q = m :=
    upper_left_record_time w h hq rfl (by simpa [q] using hcond.2)
  have hleft : (kmswStage w m).west (kmswLLCreatedEdge w m) = boundaryVertex w h q ∧
      (kmswStage w m).east (kmswLLCreatedEdge w m) = boundaryVertex w h (q + 1) ∧
      (kmswStage w m).present (kmswLLCreatedEdge w m) = false := by
    simpa [htime] using boundaryVertex_left_missing_edge w h hq
  have heq' : e = kmswLLCreatedEdge w m := by simpa using heq.symm
  have hnextPositive : 0 < (kmswStage w m).nextEdge := by
    have hmono := kmswStage_nextEdge_mono w (Nat.zero_le m)
    simp [kmswStage, kmswInit] at hmono
    omega
  have hebound : kmswLLCreatedEdge w m < (kmswStage w m).nextEdge := by
    dsimp [kmswLLCreatedEdge]
    omega
  have hstable := kmswStage_endpoints_stable w hmle hebound
  rcases hend with hwest | heast
  · refine ⟨q, by dsimp [q]; omega, by omega, ?_⟩
    calc
      boundaryVertex w h q = (kmswStage w m).west (kmswLLCreatedEdge w m) := hleft.1.symm
      _ = (kmswStage w n).west e := by rw [heq']; exact hstable.1.symm
      _ = v := hwest
  · refine ⟨q + 1, by dsimp [q]; omega, by omega, ?_⟩
    calc
      boundaryVertex w h (q + 1) = (kmswStage w m).east (kmswLLCreatedEdge w m) :=
        hleft.2.1.symm
      _ = (kmswStage w n).east e := by rw [heq']; exact hstable.2.symm
      _ = v := heast

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem finite_LR_label (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n e v : ℕ) (heLR : e ∈ (kmswStage w n).LR)
    (hend : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ k : ℤ, 0 ≤ k ∧ k ≤ ((kmswStage w n).LR.length : ℤ) ∧
      boundaryVertex w h k = v := by
  rw [kmswStage_LR_eq] at heLR
  obtain ⟨m, hm, heq⟩ := List.mem_map.mp heLR
  have hrecord : ∀ j < m, R w m < R w j := of_decide_eq_true (List.mem_filter.mp hm).2
  have hmle : m ≤ n := by
    have := List.mem_range.mp (List.mem_filter.mp hm).1
    omega
  have hmin := runningMin_le (R w) n m hmle
  have hlen := kmswStage_LR_length w n
  change minR w n ≤ R w m at hmin
  have hmin0 := runningMin_le (R w) n 0 (Nat.zero_le n)
  change minR w n ≤ 0 at hmin0
  by_cases hm0 : m = 0
  · subst m
    have heq' : e = 0 := by simpa [act, kmswStage, kmswInit] using heq.symm
    have hebound : e < (kmswStage w 0).nextEdge := by simp [heq', kmswStage, kmswInit]
    have hstable := kmswStage_endpoints_stable w hmle hebound
    rcases hend with hwest | heast
    · refine ⟨0, by omega, by omega, ?_⟩
      rw [boundaryVertex_zero]
      calc
        0 = (kmswStage w 0).west e := by rw [heq']; rfl
        _ = (kmswStage w n).west e := hstable.1.symm
        _ = v := hwest
    · refine ⟨1, by omega, by omega, ?_⟩
      rw [boundaryVertex_one]
      calc
        1 = (kmswStage w 0).east e := by rw [heq']; rfl
        _ = (kmswStage w n).east e := hstable.2.symm
        _ = v := heast
  · have hzero : R w 0 = 0 := by simp [R]
    have hrecord0 := hrecord 0 (by omega)
    let q := -R w m
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hvalue : R w m = -q := by dsimp [q]; omega
    obtain ⟨N, hNbound, hN⟩ := boundaryVertex_right_edge w h hq
    have htime : boundaryHitTime w h q = m :=
      upper_right_record_time w h hq hvalue hrecord
    have hqN : m ≤ N := by rw [← htime]; exact hNbound
    have hstableMN := kmswStage_endpoints_stable w hmle
      (act_lt_nextEdge w (Nat.le_refl m))
    have hstableMN' := kmswStage_endpoints_stable w hqN
      (act_lt_nextEdge w (Nat.le_refl m))
    have hNedge := hN N le_rfl
    have heq' : e = act w m := by simpa using heq.symm
    rcases hend with hwest | heast
    · refine ⟨q, by omega, by dsimp [q]; omega, ?_⟩
      calc
        boundaryVertex w h q = (kmswStage w N).west (act w m) := by
          rw [← htime]
          exact (hNedge.2.2.1).symm
        _ = (kmswStage w m).west (act w m) := hstableMN'.1
        _ = (kmswStage w n).west e := by rw [heq']; exact hstableMN.1.symm
        _ = v := hwest
    · refine ⟨q + 1, by omega, by dsimp [q]; omega, ?_⟩
      calc
        boundaryVertex w h (q + 1) = (kmswStage w N).east (act w m) := by
          rw [← htime]
          exact (hNedge.2.2.2).symm
        _ = (kmswStage w m).east (act w m) := hstableMN'.2
        _ = (kmswStage w n).east e := by rw [heq']; exact hstableMN.2.symm
        _ = v := heast



/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem cellSdpUpper_lower_endpoint_label (w : ℕ → Fin 3) (n : ℕ)
    (h : BoundaryHitWitnesses w) (x : ℕ)
    (hx : ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
      (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) :
    ∃ ℓ : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ ℓ ∧
      ℓ ≤ ((kmswStage w n).LR.length : ℤ) ∧ boundaryVertex w h ℓ = x := by
  obtain ⟨e, he, hend⟩ := hx
  rcases List.mem_append.mp he with he | he
  · obtain ⟨k, hkL, hk0, hkx⟩ := finite_LL_label w h n e x he hend
    exact ⟨k, hkL, by omega, hkx⟩
  · obtain ⟨k, hk0, hkR, hkx⟩ := finite_LR_label w h n e x he hend
    exact ⟨k, by omega, hkR, hkx⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem chain_vertex_ranks (s : State) (r : ℕ → ℚ) (es : List ℕ)
    (hne : es ≠ []) (hc : WestEastChain s es)
    (hr : ∀ e ∈ es, r (s.west e) < r (s.east e)) :
    List.IsChain (· < ·)
      ((es.map (fun e => r (s.west e))) ++ [r (s.east (es.getLast hne))]) := by
  induction es with
  | nil => exact (hne rfl).elim
  | cons e es ih =>
    cases es with
    | nil => simpa only [List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.getLast_singleton, List.isChain_cons_cons,
        List.isChain_singleton, and_true] using hr e (by simp only [List.mem_singleton])
    | cons f fs =>
      have ht := ih (List.cons_ne_nil f fs) hc.tail
        (fun a ha => hr a (List.mem_cons_of_mem e ha))
      have hef : s.east e = s.west f := hc.rel
      have he : r (s.west e) < r (s.west f) := by
        rw [← hef]
        exact hr e List.mem_cons_self
      simp only [List.map_cons, List.cons_append, List.getLast_cons_cons]
      exact List.isChain_cons_cons.mpr ⟨he, ht⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
labels exhausts the integer interval. This is a finite counting argument. -/
private theorem bounded_labels_exhaust (vs : List ℕ) (a b : ℤ) (f : ℤ → ℕ)
    (hv : vs.Nodup) (hlen : vs.length = (b + 1 - a).toNat)
    (hlabels : ∀ v ∈ vs, ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ v = f k) :
    ∀ k : ℤ, a ≤ k → k ≤ b → f k ∈ vs := by
  classical
  let g : ℕ → ℤ := fun v => if h : v ∈ vs then Classical.choose (hlabels v h) else 0
  have hg (v : ℕ) (h : v ∈ vs) : a ≤ g v ∧ g v ≤ b ∧ v = f (g v) := by
    simpa only [g, dite_eq_left h] using Classical.choose_spec (hlabels v h)
  have hsub : vs.toFinset.image g ⊆ Finset.Icc a b := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨(hg v (List.mem_toFinset.mp hv)).1,
      (hg v (List.mem_toFinset.mp hv)).2.1⟩
  have hinj : Set.InjOn g (vs.toFinset : Set ℕ) := by
    intro v hv v' hv' heq
    rw [(hg v (List.mem_toFinset.mp hv)).2.2,
      (hg v' (List.mem_toFinset.mp hv')).2.2, heq]
  have heq : vs.toFinset.image g = Finset.Icc a b := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hv, hlen,
      Int.card_Icc]
  intro k hka hkb
  have hk : k ∈ vs.toFinset.image g := by
    rw [heq]
    exact Finset.mem_Icc.mpr ⟨hka, hkb⟩
  obtain ⟨v, hv, hvk⟩ := Finset.mem_image.mp hk
  have hv' := List.mem_toFinset.mp hv
  rw [← hvk, ← (hg v hv').2.2]
  exact hv'

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
upper endpoint. Strict ranks ensure that the upper chain has no repeated vertices. -/
private theorem cellSdpUpper_upper_label_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (k : ℤ)
    (hkL : -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k)
    (hkR : k ≤ ((kmswStage w n).UR.length : ℤ) + 1) :
    ∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
      (kmswStage w n).west e = kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hn k) ∨
        (kmswStage w n).east e = kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hn k) := by
  let s := kmswStage w n
  let es := s.UL ++ s.UR
  have hne : es ≠ [] :=
    List.append_ne_nil_of_left_ne_nil (kmswStage_UL_nonempty_active_last w n).1 _
  let vs := es.map s.west ++ [s.east (es.getLast hne)]
  have hmem (v : ℕ) (hv : v ∈ vs) :
      ∃ e ∈ es, s.west e = v ∨ s.east e = v := by
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
      exact ⟨e, he, Or.inl rfl⟩
    · have heq := List.mem_singleton.mp hv
      exact ⟨es.getLast hne, List.getLast_mem hne, Or.inr heq.symm⟩
  have hr : ∀ e ∈ es,
      kmswStageRank w n (s.west e) < kmswStageRank w n (s.east e) := by
    intro e he
    apply kmswStageRank_strict w n e
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e
      (by change e ∈ s.UL ++ s.UR at he
          simp only [List.mem_append] at he ⊢
          exact Or.inl (Or.inl he))
  have hc := chain_vertex_ranks s (kmswStageRank w n) es hne
    (kmswStage_boundary_chain_invariant w n).1 hr
  have hnodup : vs.Nodup := by
    apply List.Nodup.of_map (kmswStageRank w n)
    have hp := (List.isChain_iff_pairwise.mp hc).nodup
    simpa only [vs, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def] using hp
  have hpos : 0 < s.UL.length :=
    List.length_pos_iff.mpr (kmswStage_UL_nonempty_active_last w n).1
  have hlen : vs.length =
      (((s.UR.length : ℤ) + 1) + 1 - (-((s.UL.length - 1 : ℕ) : ℤ))).toNat := by
    simp only [vs, List.length_append, List.length_map, List.length_singleton, es]
    omega
  have hlabels : ∀ v ∈ vs, ∃ j : ℤ,
      -((s.UL.length - 1 : ℕ) : ℤ) ≤ j ∧ j ≤ (s.UR.length : ℤ) + 1 ∧
      v = kmswWindowVertexMapInf w n (boundaryVertex (fun i => w (n + i)) hn j) := by
    intro v hv
    obtain ⟨e, he, hend⟩ := hmem v hv
    exact stage_upper_endpoint_future_boundary_bounded w n hn e v he hend
  exact hmem _ (bounded_labels_exhaust vs _ _ _ hnodup hlen hlabels k hkL hkR)

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
the deterministic statements above hold for every code and every hit witness. -/
theorem cellSdpUpper_boundaryLabelIdentification_proved :
    cellSdpUpper_boundaryLabelIdentification := by
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  intro n h0 hn
  constructor
  · exact cellSdpUpper_lower_endpoint_label (fun i => ω (i + 1)) n h0
  · exact cellSdpUpper_upper_label_endpoint (fun i => ω (i + 1)) n hn

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
future labels `-1, 0, 1` with the three consecutive original vertices `0, 1, 2`. -/
private theorem cellSdpUpper_down_window_labels (w : ℕ → Fin 3) (hw : w 0 = 2)
    (hn : BoundaryHitWitnesses (fun i => w (1 + i))) :
    kmswWindowVertexMapInf w 1 (boundaryVertex (fun i => w (1 + i)) hn (-1)) = 0 ∧
      kmswWindowVertexMapInf w 1 (boundaryVertex (fun i => w (1 + i)) hn 0) = 1 ∧
      kmswWindowVertexMapInf w 1 (boundaryVertex (fun i => w (1 + i)) hn 1) = 2 := by
  have hzero : kmswWindowVertexMapInf w 1
      (boundaryVertex (fun i => w (1 + i)) hn 0) = 1 := by
    rw [boundaryVertex_zero, kmswWindowVertexMapInf_eq_stage w 1 0 0 (by change 0 < 2; omega)]
    simp only [kmswWindowPatchVertexMap, ite_true, kmswStage, kmswStep, hw,
      kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
    rfl
  have hone : kmswWindowVertexMapInf w 1
      (boundaryVertex (fun i => w (1 + i)) hn 1) = 2 := by
    rw [boundaryVertex_one, kmswWindowVertexMapInf_eq_stage w 1 0 1 (by change 1 < 2; omega)]
    simp only [kmswWindowPatchVertexMap, kmswStage, kmswStep, hw,
      kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
    rfl
  obtain ⟨k, hkL, hkR, hk⟩ := stage_upper_endpoint_future_boundary_bounded w 1 hn 0 0
    (by simp [kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep, kmswInit,
      State.addEdge])
    (Or.inl (by simp [kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]))
  have hkL' : -1 ≤ k := by
    simpa [kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep, kmswInit,
      State.addEdge] using hkL
  have hkR' : k ≤ 1 := by
    simpa [kmswStage, kmswStep, hw, kmswCodeStep, kmswStepOfStep, kmswInit,
      State.addEdge] using hkR
  have hkneg : k = -1 := by
    by_cases hk0 : k = 0
    · rw [hk0, hzero] at hk
      omega
    by_cases hk1 : k = 1
    · rw [hk1, hone] at hk
      omega
    omega
  exact ⟨by simpa only [hkneg] using hk.symm, hzero, hone⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
would force an upper bound on a shifted left Busemann value after a down cell. -/
private theorem cellSdpUpper_confinement_forces_down_bound
    (hconf : cellSdpUpper_selectedTargetConfinement) :
    ∀ᵐ ω ∂iidCodeMeasure, ω 1 = 2 →
      busemannSDPMeasurableVersion (codeShift 1 ω) (-1) ≤ 1 := by
  have hshift : ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hn : BoundaryHitWitnesses (fun i => ω (1 + i + 1)),
        IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (1 + i + 1)) hn)
          (busemannSDPMeasurableVersion (codeShift 1 ω)) := by
    have hmap : ∀ᵐ η ∂iidCodeMeasure.map (codeShift 1),
        ∃ h : BoundaryHitWitnesses (fun i => η (i + 1)),
          IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => η (i + 1)) h)
            (busemannSDPMeasurableVersion η) := by
      rw [map_codeShift]
      exact iidCodes_ae_busemannSDPMeasurableVersion
    have he := (Measure.tendsto_ae_map
      (measurable_codeShift 1).aemeasurable).eventually hmap
    filter_upwards [he] with ω hω
    have htail : (fun i => codeShift 1 ω (i + 1)) = fun i => ω (1 + i + 1) := by
      funext i
      simp only [codeShift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_assoc]
    rw [htail] at hω
    exact hω
  filter_upwards [hconf, cell_sdp_separator_targets, iidCodes_ae_boundaryHitWitnesses,
    hshift] with ω hc hs h0 hf
  dsimp only at hc hs
  intro hw
  obtain ⟨hn, hX⟩ := hf
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  have hw' : w 0 = 2 := hw
  obtain ⟨hminus, hzero, _⟩ := cellSdpUpper_down_window_labels w hw' hn
  obtain ⟨J, hJ⟩ := hc hs 1 h0 hn 0 (by omega) (by omega) (-1)
  let y := Classical.choose (hs 1 h0 hn 0 (-1))
  have hy := Classical.choose_spec (hs 1 h0 hn 0 (-1))
  have hry : ∀ j, Reachable (boundaryPresentVertex (fun i => w (1 + i)) hn 0) (y j) := by
    intro j
    have hsR : (((kmswStage w 1).UR.length + 1 : ℕ) : ℤ) = 1 := by
      simp [kmswStage, kmswStep, hw', kmswCodeStep, kmswStepOfStep, kmswInit,
        State.addEdge]
    have hyR : Reachable (boundaryPresentVertex (fun i => w (1 + i)) hn 1)
        (y j) := by
      simpa only [← hsR] using (hy.2.1 j).2
    exact (boundaryVertex_nonneg_reachable (fun i => w (1 + i)) hn
      (k := 0) (l := 1) (by omega) (by omega)).trans hyR
  obtain ⟨N, hN⟩ := hX.2 0 (-1) y hy.1 (fun j => ⟨hry j, (hy.2.1 j).1⟩)
  let j := max J N
  have hcf := hJ j (Nat.le_max_left _ _)
  have hbus := hN j (Nat.le_max_right _ _)
  let Y : PresentVertex w := ⟨kmswWindowVertexMapInf w 1 (y j).id⟩
  have hle : sdp (⟨0⟩ : PresentVertex w) Y ≤
      1 + sdp (boundaryPresentVertex (fun i => w (1 + i)) hn 0) (y j) := by
    have hroot : sdp (⟨0⟩ : PresentVertex w) ⟨1⟩ ≤ 1 := by
      exact (sdp_limit_le_sdp_stage w 0 ⟨0⟩ ⟨1⟩).trans_eq (sdp_stage_x0_x1 w 0)
    have hemb := cellSdpUpper_window_sdp_le w 1
      (boundaryPresentVertex (fun i => w (1 + i)) hn 0) (y j)
    change sdp (⟨kmswWindowVertexMapInf w 1
      (boundaryVertex (fun i => w (1 + i)) hn 0)⟩ : PresentVertex w) Y ≤ _ at hemb
    rw [hzero] at hemb
    exact (sdp_triangle (⟨0⟩ : PresentVertex w) ⟨1⟩ Y).trans
      (add_le_add hroot hemb)
  have hfinite := present_sdp_ne_top (hry j)
  have hsumfinite : 1 + sdp
      (boundaryPresentVertex (fun i => w (1 + i)) hn 0) (y j) ≠ ⊤ := by
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinite
    rw [← hm]
    exact ENat.natCast_ne_top (1 + m)
  have hnat := ENat.toNat_le_toNat hle hsumfinite
  rw [ENat.toNat_add (by exact ENat.one_ne_top) hfinite] at hnat
  simp only [ENat.toNat_one] at hnat
  change (sdp (boundaryPresentVertex (fun i => w (1 + i)) hn (-1)) (y j)).toNat ≤
    (sdp (⟨kmswWindowVertexMapInf w 1
      (boundaryVertex (fun i => w (1 + i)) hn (-1))⟩ : PresentVertex w) Y).toNat at hcf
  rw [hminus] at hcf
  have hz := hX.1
  change busemannSDPMeasurableVersion (codeShift 1 ω) (-1) -
    busemannSDPMeasurableVersion (codeShift 1 ω) 0 =
      ((sdp (boundaryPresentVertex (fun i => w (1 + i)) hn (-1)) (y j)).toNat : ℤ) -
        ((sdp (boundaryPresentVertex (fun i => w (1 + i)) hn 0) (y j)).toNat : ℤ)
    at hbus
  omega

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem firstCode_mass (c : Fin 3) :
    iidCodeMeasure {ω | ω 1 = c} = (3 : ENNReal)⁻¹ := by
  have hinj : Function.Injective lazyTwoDimensionalStep := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [lazyTwoDimensionalStep]
  have hevent : {ω : ℕ → Fin 3 | ω 1 = c} =
      (fun ω => codeWalk ω (0 + 1) - codeWalk ω 0) ⁻¹'
        {lazyTwoDimensionalStep c} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      codeWalk_succ_sub, zero_add]
    exact ⟨fun h => congrArg lazyTwoDimensionalStep h, fun h => hinj h⟩
  have hm : Measurable (fun ω : ℕ → Fin 3 =>
      codeWalk ω (0 + 1) - codeWalk ω 0) := by
    simp only [codeWalk_succ_sub]
    exact (measurable_of_countable lazyTwoDimensionalStep).comp (measurable_pi_apply 1)
  rw [hevent, ← Measure.map_apply hm (measurableSet_singleton _),
    map_codeWalk_increment, Measure.uniformOfFinset_apply_singleton]
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
rules out an almost-sure upper bound of one on the left Busemann value. -/
private theorem cellSdpUpper_left_value_not_bounded :
    ¬ (∀ᵐ ω ∂iidCodeMeasure, busemannSDPMeasurableVersion ω (-1) ≤ 1) := by
  intro hbound
  let D : (ℕ → Fin 3) → ℤ := fun ω =>
    busemannSDPMeasurableVersion ω 0 - busemannSDPMeasurableVersion ω (-1)
  have hm : Measurable D :=
    (measurable_busemannSDPMeasurableVersion 0).sub
      (measurable_busemannSDPMeasurableVersion (-1))
  have hsym : iidCodeMeasure.map D = iidCodeMeasure.map (fun ω => -D ω) := by
    exact hsymSdp_sdpCode
  have hlo : ∀ᵐ ω ∂iidCodeMeasure, -1 ≤ D ω := by
    filter_upwards [hbound] with ω hω
    dsimp only [D]
    rw [busemannSDPMeasurableVersion_zero]
    omega
  have hmap : ∀ᵐ d ∂iidCodeMeasure.map D, (-1 : ℤ) ≤ d :=
    (ae_map_iff hm.aemeasurable measurableSet_Ici).mpr hlo
  rw [hsym] at hmap
  have hhi := (Measure.tendsto_ae_map hm.neg.aemeasurable).eventually hmap
  have hab : ∀ᵐ ω ∂iidCodeMeasure, |((D ω : ℤ) : ℝ)| ≤ 1 := by
    filter_upwards [hlo, hhi] with ω hl hh
    change -1 ≤ -(D ω) at hh
    have hh' : D ω ≤ 1 := by omega
    exact abs_le.mpr ⟨by exact_mod_cast hl, by exact_mod_cast hh'⟩
  obtain ⟨c, hc, _, htail⟩ := busemann_tail_sdp_sdpCode
  obtain ⟨R, hR⟩ := (htail.def hc).exists_forall_of_atTop
  let x : ℝ := max 2 R
  have hx : 1 < x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hp : 0 < x ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hnull : iidCodeMeasure {ω | x ≤ |((D ω : ℤ) : ℝ)|} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hab] with ω hω
    linarith
  have hz : iidCodeMeasure.real {ω | x ≤ |((D ω : ℤ) : ℝ)|} = 0 := by
    change (iidCodeMeasure {ω | x ≤ |((D ω : ℤ) : ℝ)|}).toReal = 0
    rw [hnull, ENNReal.toReal_zero]
  have hr := hR x (le_max_right _ _)
  change ‖iidCodeMeasure.real {ω | x ≤ |((D ω : ℤ) : ℝ)|} -
    2 * c * x ^ (-(4 / 3 : ℝ))‖ ≤ c * ‖x ^ (-(4 / 3 : ℝ))‖ at hr
  rw [hz, zero_sub, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * c * x ^ (-(4 / 3 : ℝ))),
    abs_of_pos hp] at hr
  nlinarith only [hr, mul_pos hc hp]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
for the current code-level models: the original cell supplies a missing future edge. -/
theorem cellSdpUpper_selectedTargetConfinement_false :
    ¬ cellSdpUpper_selectedTargetConfinement := by
  intro hconf
  have hb := cellSdpUpper_confinement_forces_down_bound hconf
  let B : Set (ℤ → ℤ) := {X | 1 < X (-1)}
  have hB : MeasurableSet B := (measurable_pi_apply (-1)) measurableSet_Ioi
  have hi :=
    indepFun_firstCode_busemannSDPMeasurableVersion_shift.measure_inter_preimage_eq_mul
      {2} B (measurableSet_singleton _) hB
  have hnull : iidCodeMeasure
      ((fun ω : ℕ → Fin 3 => ω 1) ⁻¹' {2} ∩
        (fun ω => busemannSDPMeasurableVersion (fun i => ω (i + 1))) ⁻¹' B) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hb] with ω hω
    change ¬ (ω 1 = 2 ∧ 1 < busemannSDPMeasurableVersion
      (fun i => ω (i + 1)) (-1))
    rw [busemannSDPMeasurableVersion_shift_eq]
    exact fun h => (not_lt_of_ge (hω h.1)) h.2
  have hfirst : iidCodeMeasure ((fun ω : ℕ → Fin 3 => ω 1) ⁻¹' {2}) ≠ 0 := by
    change iidCodeMeasure {ω | ω 1 = 2} ≠ 0
    rw [firstCode_mass]
    norm_num
  have htailzero : iidCodeMeasure
      ((fun ω => busemannSDPMeasurableVersion (fun i => ω (i + 1))) ⁻¹' B) = 0 := by
    rw [hnull] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left hfirst
  have hm : Measurable busemannSDPMeasurableVersion :=
    measurable_pi_iff.mpr measurable_busemannSDPMeasurableVersion
  have hms : Measurable (fun ω : ℕ → Fin 3 =>
      busemannSDPMeasurableVersion (fun i => ω (i + 1))) :=
    hm.comp (measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1))
  have hbasezero : iidCodeMeasure (busemannSDPMeasurableVersion ⁻¹' B) = 0 := by
    rw [← Measure.map_apply hm hB, ← iidCodeMeasure_map_busemannSDPMeasurableVersion_shift,
      Measure.map_apply hms hB]
    exact htailzero
  apply cellSdpUpper_left_value_not_bounded
  have ha := measure_eq_zero_iff_ae_notMem.mp hbasezero
  filter_upwards [ha] with ω hω
  change ¬ 1 < busemannSDPMeasurableVersion ω (-1) at hω
  exact le_of_not_gt hω

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
A shortest ambient suffix may use the cell and leave it at a different upper vertex.
Its length is therefore compared with the seam distance minus the entire upper-boundary
Busemann oscillation, rather than with the future distance from its original start.
A last-exit decomposition and the finite upper-boundary range plausibly prove this
obligation. That geometric proof is not supplied here. -/
@[expose] def cellSdpUpper_boundaryOscillationConfinement : Prop :=
  ∀ w : ℕ → Fin 3, ∀ n : ℕ,
    ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)), ∀ Xn : ℤ → ℤ,
      IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => w (n + i)) hn) Xn →
      ∀ Mn : ℤ,
        (∀ k : ℤ,
          -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k →
          k ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
          |Xn k - Xn (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)| ≤ Mn) →
        ∀ k : ℤ,
          -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k →
          k ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
          ∀ y : ℕ → PresentVertex (fun i => w (n + i)), Function.Injective y →
            (∀ j, Reachable (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
              Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
                (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) →
            ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
              ((sdp (boundaryPresentVertex (fun i => w (n + i)) hn
                (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)).toNat : ℤ) - Mn ≤
              ((sdp
                (⟨kmswWindowVertexMapInf w n
                  (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)
                (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)).toNat : ℤ)

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
from the corrected OPEN oscillation premise. The Busemann characterizations,
fluctuation bounds, geodesic, and separator targets are explicit, as in the
existing first-bullet helper. This does not assert the probabilistic two-bullet
conclusion or discharge deterministic reversal transport. -/
theorem cellSdpUpper_first_bullet_of_boundaryOscillation
    (hconf : cellSdpUpper_boundaryOscillationConfinement) (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (X Xn : ℤ → ℤ) (M0 Mn : ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X)
    (hXn : IsBoundaryBusemannSDP
      (boundaryPresentVertex (fun i => w (n + i)) hn) Xn)
    (hM0 : ∀ ℓ : ℤ,
      -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
      ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
      |X ℓ - X ((kmswStage w n).LR.length : ℤ)| ≤ M0)
    (hMn : ∀ k : ℤ,
      -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k →
      k ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
      |Xn k - Xn (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)| ≤ Mn)
    (ℓ : ℤ)
    (hℓ : -((kmswStage w n).LL.length : ℤ) ≤ ℓ ∧
      ℓ ≤ ((kmswStage w n).LR.length : ℤ))
    (hℓStage : boundaryVertex w h0 ℓ < (kmswStage w n).nextVertex)
    (P : InfinitePresentPath w (boundaryPresentVertex w h0 ℓ))
    (hP : P.HasShortestSegments)
    (hTargets : ∀ k : ℤ,
      ∃ y : ℕ → PresentVertex (fun i => w (n + i)), Function.Injective y ∧
        (∀ j, Reachable
          (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
          Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
            (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
        (∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w))) :
    ∃ k : ℤ,
      -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
      k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
      sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
        ⟨kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
        (((2 * M0 + 2 * Mn).toNat : ℕ) : ℕ∞) := by
  let u : ℕ → Fin 3 := fun i => w (n + i)
  let σ0 : ℤ := (kmswStage w n).LR.length
  let σn : ℤ := (kmswStage w n).UR.length + 1
  let x : PresentVertex w := boundaryPresentVertex w h0 ℓ
  let xs : PresentVertex w := boundaryPresentVertex w h0 σ0
  let img : PresentVertex u → PresentVertex w :=
    fun v => ⟨kmswWindowVertexMapInf w n v.id⟩
  obtain ⟨T, hExit, hBefore, k, hkL, hkR, hkId, hq, hStage, hLimit⟩ :=
    cell_sdp_geodesic_exit_future_boundary w P hP n hℓStage hn
  let xk : PresentVertex u := boundaryPresentVertex u hn k
  obtain ⟨y, hy, hreach, havoid⟩ := hTargets k
  obtain ⟨J, hconfJ⟩ := hconf w n hn Xn hXn Mn hMn k hkL hkR y hy hreach
  let ytail : ℕ → PresentVertex u := fun r => y (J + r)
  have hytail : Function.Injective ytail := by
    intro a b hab
    have hsum : J + a = J + b := hy (by simpa [ytail] using hab)
    exact Nat.add_left_cancel hsum
  have hytailReach : ∀ r, Reachable xk (ytail r) ∧
      Reachable (boundaryPresentVertex u hn σn) (ytail r) := by
    intro r
    simpa [ytail, xk, σn, u] using hreach (J + r)
  have hytailAvoid : ∀ r, FiniteAvoidance x (img (ytail r)) := by
    intro r
    simpa [ytail, x, img, u] using havoid (J + r)
  obtain ⟨j, s, hj, hs, hvisit⟩ :=
    sdp_separator_targets_infinite_selection w n h0 ℓ P ytail hytail hytailAvoid
  let Y : ℕ → PresentVertex u := fun r => ytail (j r)
  have hYinj : Function.Injective Y := hytail.comp hj
  have hYfuture : ∀ r, Reachable xk (Y r) ∧
      Reachable (boundaryPresentVertex u hn σn) (Y r) :=
    fun r => hytailReach (j r)
  have hYbase : ∀ r, Reachable x (img (Y r)) ∧ Reachable xs (img (Y r)) := by
    intro r
    constructor
    · have hr : Reachable x (P.initial (s r)).1 := ⟨(P.initial (s r)).2⟩
      rw [hvisit r] at hr
      exact hr
    · have hseam := presentSdp_rightBoundary_seam_eq w n (Y r).id h0 hn
      have hfinite : sdp (boundaryPresentVertex w h0 σ0)
          ⟨kmswWindowVertexMapInf w n (Y r).id⟩ ≠ ⊤ := by
        change sdp (⟨boundaryVertex w h0 σ0⟩ : PresentVertex w)
          ⟨kmswWindowVertexMapInf w n (Y r).id⟩ ≠ ⊤
        rw [← hseam]
        exact present_sdp_ne_top (hYfuture r).2
      by_contra hnot
      exact hfinite ((sdp_eq_top_iff_not_reachable).2 hnot)
  have himginj : Function.Injective img := by
    intro a b hab
    have hid := kmswWindowVertexMapInf_injective w n
      (congrArg PresentVertex.id hab)
    cases a
    cases b
    cases hid
    rfl
  let V : ℕ → PresentVertex w := fun r => img (Y r)
  have hVinj : Function.Injective V := himginj.comp hYinj
  have hVbase : ∀ r, Reachable x (V r) ∧ Reachable xs (V r) := hYbase
  obtain ⟨N0, hN0⟩ := hX.2 ℓ σ0 V hVinj hVbase
  let r : ℕ := max T N0
  have hrT : T ≤ r := by dsimp [r]; exact Nat.le_max_left _ _
  have hr0 : N0 ≤ r := by
    dsimp [r]
    exact Nat.le_max_right _ _
  have hrs : r ≤ s r := by
    induction r with
    | zero => exact Nat.zero_le _
    | succ r ih =>
      have hmono : s r < s (r + 1) := hs (Nat.lt_succ_self r)
      omega
  let W : PresentVertex w := V r
  let z : PresentVertex w := (P.initial T).1
  have hW : (P.initial (s r)).1 = W := hvisit r
  have hdistXW : sdp x W = (s r : ℕ∞) := by
    rw [← hW]
    change sdp (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
      (P.initial (s r)).1 = _
    rw [← (isShortest_iff_length_eq_sdp _).mp
      (P.initial_isShortest w hP (s r))]
    exact_mod_cast P.prefix_length (s r)
  have hQend : ((P.shift T).initial (s r - T)).1 = W := by
    change (P.initial (T + (s r - T))).1 = W
    have hsum : T + (s r - T) = s r := by omega
    rw [hsum]
    exact hW
  have hdistZW : sdp z W = ((s r - T : ℕ) : ℕ∞) := by
    rw [← hQend]
    rw [← (isShortest_iff_length_eq_sdp _).mp
      ((P.shift T).initial_isShortest w
        (P.shift_hasShortestSegments hP T) (s r - T)),
      (P.shift T).prefix_length]
  have hgeoExit : ((sdp x W).toNat : ℤ) - ((sdp z W).toNat : ℤ) = T := by
    rw [hdistXW, hdistZW]
    simp only [ENat.toNat_natCast]
    have hTle : T ≤ s r := hrT.trans hrs
    omega
  have hdxz : ((sdp x z).toNat : ℤ) = T := by
    change ((sdp (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
      (P.initial T).1).toNat : ℤ) = T
    have hh := congrArg (fun d : ℕ∞ => (d.toNat : ℤ)) hLimit
    simpa [boundaryPresentVertex] using hh
  have hZ : z = img (boundaryPresentVertex u hn k) := by
    exact congrArg (fun id => (⟨id⟩ : PresentVertex w)) hkId
  have hgeo : ((sdp x z).toNat : ℤ) =
      ((sdp x W).toNat : ℤ) - ((sdp z W).toNat : ℤ) := by
    omega
  have hgeoChain : ((sdp x z).toNat : ℤ) =
      ((sdp x W).toNat : ℤ) -
        ((sdp (img (boundaryPresentVertex u hn k)) W).toNat : ℤ) := by
    simpa only [hZ] using hgeo
  have hXid : ((sdp x W).toNat : ℤ) - ((sdp xs W).toNat : ℤ) =
      X ℓ - X σ0 := by
    have h := hN0 r hr0
    dsimp [V, W] at h
    linarith
  have hseam : sdp (boundaryPresentVertex u hn σn) (Y r) =
      sdp xs (img (Y r)) := by
    exact presentSdp_rightBoundary_seam_eq w n (Y r).id h0 hn
  have hseamInt :
      ((sdp (boundaryPresentVertex u hn σn) (Y r)).toNat : ℤ) =
        ((sdp xs W).toNat : ℤ) := by
    simpa [W, V, xs, σ0, img, u] using
      congrArg (fun d : ℕ∞ => (d.toNat : ℤ)) hseam
  have hconfR := hconfJ (J + j r) (by omega)
  have hconfInt :
      ((sdp (boundaryPresentVertex u hn σn) (Y r)).toNat : ℤ) - Mn ≤
        ((sdp (img (boundaryPresentVertex u hn k)) W).toNat : ℤ) := by
    simpa [W, V, Y, ytail, img, u, boundaryPresentVertex, σn] using hconfR
  have hM0ell := hM0 ℓ hℓ.1 hℓ.2
  have hMnK := hMn k hkL (by omega)
  have hM0nonneg : 0 ≤ M0 := (abs_nonneg _).trans hM0ell
  have hMnnonneg : 0 ≤ Mn := (abs_nonneg _).trans hMnK
  have hM0upper : X ℓ - X σ0 ≤ M0 := (abs_le.mp hM0ell).2
  have hMnlower : -(Mn) ≤ Xn k - Xn σn := (abs_le.mp hMnK).1
  have hTbound : (T : ℤ) ≤ 2 * M0 + 2 * Mn := by
    omega
  have hBnonneg : 0 ≤ 2 * M0 + 2 * Mn := by omega
  have hTnat : T ≤ (2 * M0 + 2 * Mn).toNat := by
    have hcast : ((2 * M0 + 2 * Mn).toNat : ℤ) = 2 * M0 + 2 * Mn :=
      Int.toNat_of_nonneg hBnonneg
    have hbound : (T : ℤ) ≤ ((2 * M0 + 2 * Mn).toNat : ℤ) := by
      rw [hcast]
      exact hTbound
    exact_mod_cast hbound
  refine ⟨k, hkL, hkR, ?_⟩
  rw [hStage]
  exact_mod_cast hTnat


end DirectedDistances.PaperProofs.Section7
