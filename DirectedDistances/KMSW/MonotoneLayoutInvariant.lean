module

public import DirectedDistances.KMSW.MonotoneLayoutData
public import DirectedDistances.KMSW.MonotoneStageCertificate
public import DirectedDistances.PlanarMap.RoofPolyline
public import DirectedDistances.KMSW.MonotoneStageFaces






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set



@[expose] def isFreshLeftMissing (w : ℕ → Fin 3) (n e : ℕ) : Prop :=
  w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = [] ∧
    e = (kmswStage w n).nextEdge + 1

instance (w : ℕ → Fin 3) (n e : ℕ) : Decidable (isFreshLeftMissing w n e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))



@[expose] noncomputable def layoutArc (w : ℕ → Fin 3) : ℕ → ℕ → Polyline
  | 0, _ => segmentArc (layoutPos w 0 0) (layoutPos w 0 1)
  | n + 1, e =>
    if e < (kmswStage w n).nextEdge then layoutArc w n e
    else if e ∈ freshEdges w n then
      let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
      let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
      if isFreshLeftMissing w n e then segmentArc a b
      else roofArc a b (n + 1) (rampSlope w n)
    else layoutArc w n e



theorem layoutArc_old (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    layoutArc w (n + 1) e = layoutArc w n e := by
  simp only [layoutArc, ite_eq_left he]



theorem layoutArc_fresh (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ freshEdges w n) :
    layoutArc w (n + 1) e =
      if isFreshLeftMissing w n e then
        segmentArc (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e))
          (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e))
      else roofArc (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e))
        (n + 1) (rampSlope w n) := by
  have hn : ¬ e < (kmswStage w n).nextEdge :=
    not_lt.mpr (Finset.mem_Ico.mp he).1
  simp only [layoutArc, ite_eq_right hn, ite_eq_left he]

private theorem old_endpoint_positions (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    layoutPos w (n + 1) ((kmswStage w (n + 1)).west e) =
        layoutPos w n ((kmswStage w n).west e) ∧
      layoutPos w (n + 1) ((kmswStage w (n + 1)).east e) =
        layoutPos w n ((kmswStage w n).east e) := by
  obtain ⟨hw, hb⟩ := kmswStage_endpoints_stable w (Nat.le_succ n) he
  obtain ⟨hv, hu⟩ := kmswStage_endpoints_lt_nextVertex w n e he
  rw [hw, hb]
  exact ⟨layoutPos_old_vertex w n _ hv, layoutPos_old_vertex w n _ hu⟩

private theorem allocated_re_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (layoutPos w n ((kmswStage w n).west e)).re <
      (layoutPos w n ((kmswStage w n).east e)).re := by
  change (kmswStageRank w n ((kmswStage w n).west e) : ℝ) <
    (kmswStageRank w n ((kmswStage w n).east e) : ℝ)
  exact_mod_cast kmswStageRank_strict w n e he



theorem layoutArc_endpoints (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (layoutArc w n e).start = layoutPos w n ((kmswStage w n).west e) ∧
      (layoutArc w n e).finish = layoutPos w n ((kmswStage w n).east e) := by
  induction n with
  | zero =>
    have he0 : e = 0 := by change e < 1 at he; omega
    subst e
    exact ⟨segmentArc_start _ _, segmentArc_finish _ _⟩
  | succ n ih =>
    by_cases ho : e < (kmswStage w n).nextEdge
    · rw [layoutArc_old w n e ho]
      obtain ⟨hw, hb⟩ := old_endpoint_positions w n e ho
      rw [hw, hb]
      exact ih ho
    · have hf : e ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, he⟩
      rw [layoutArc_fresh w n e hf]
      split
      · exact ⟨segmentArc_start _ _, segmentArc_finish _ _⟩
      · exact ⟨roofArc_start _ _ _ _, roofArc_finish _ _ _ _⟩



theorem layoutArc_points_pairwise (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    List.Pairwise (fun z z' : ℂ => z.re < z'.re) (layoutArc w n e).points := by
  induction n with
  | zero =>
    apply segmentArc_points_pairwise
    norm_num [layoutPos, kmswStageRank]
  | succ n ih =>
    by_cases ho : e < (kmswStage w n).nextEdge
    · rw [layoutArc_old w n e ho]
      exact ih ho
    · have hf : e ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, he⟩
      rw [layoutArc_fresh w n e hf]
      obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n e hf
      split
      · exact segmentArc_points_pairwise (allocated_re_lt w (n + 1) e he)
      · exact roofArc_points_pairwise (rampSlope_pos w n) ha hb
          (freshEdges_ramp_widths_lt w n e hf)



theorem layoutArc_start (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (layoutArc w n e).start = layoutPos w n ((kmswStage w n).west e) :=
  (layoutArc_endpoints w n e he).1



theorem layoutArc_finish (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (layoutArc w n e).finish = layoutPos w n ((kmswStage w n).east e) :=
  (layoutArc_endpoints w n e he).2



theorem layoutArc_image_fresh (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ freshEdges w n) :
    let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
    let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
    (layoutArc w (n + 1) e).image =
      {z | a.re ≤ z.re ∧ z.re ≤ b.re ∧ z.im =
        if isFreshLeftMissing w n e then segmentHeight a b z.re
        else roofHeight a b (n + 1) (rampSlope w n) z.re} := by
  dsimp only
  rw [layoutArc_fresh w n e he]
  obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n e he
  by_cases hm : isFreshLeftMissing w n e
  · simp only [hm, ↓reduceIte]
    exact segmentArc_image (allocated_re_lt w (n + 1) e (Finset.mem_Ico.mp he).2)
  · simp only [hm, ↓reduceIte]
    exact roofArc_image (rampSlope_pos w n) ha hb (freshEdges_ramp_widths_lt w n e he)



theorem layoutArc_image_graph (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    ∃ f : ℝ → ℝ, (layoutArc w n e).image =
      {z | (layoutPos w n ((kmswStage w n).west e)).re ≤ z.re ∧
        z.re ≤ (layoutPos w n ((kmswStage w n).east e)).re ∧ z.im = f z.re} := by
  induction n with
  | zero =>
    have he0 : e = 0 := by change e < 1 at he; omega
    subst e
    refine ⟨segmentHeight (layoutPos w 0 0) (layoutPos w 0 1), ?_⟩
    exact segmentArc_image (allocated_re_lt w 0 0 he)
  | succ n ih =>
    by_cases ho : e < (kmswStage w n).nextEdge
    · obtain ⟨hw, hb⟩ := old_endpoint_positions w n e ho
      rw [layoutArc_old w n e ho, hw, hb]
      exact ih ho
    · have hf : e ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, he⟩
      refine ⟨(fun x => if isFreshLeftMissing w n e then
        segmentHeight (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e))
          (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)) x
        else roofHeight (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e))
          (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e))
          (n + 1) (rampSlope w n) x), layoutArc_image_fresh w n e hf⟩

private theorem segmentArc_height_lower {a b z : ℂ} (hab : a.re < b.re)
    (hz : z ∈ (segmentArc a b).image) : min a.im b.im ≤ z.im := by
  rw [segmentArc_image hab] at hz
  have hzseg := (mem_segment_iff_height hab).mpr hz
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hzseg
  have ha := mul_le_mul_of_nonneg_left (min_le_left a.im b.im) hs
  have hb := mul_le_mul_of_nonneg_left (min_le_right a.im b.im) ht
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  calc
    min a.im b.im = (s + t) * min a.im b.im := by rw [hst, one_mul]
    _ = s * min a.im b.im + t * min a.im b.im := by ring
    _ ≤ s * a.im + t * b.im := add_le_add ha hb

private theorem roofArc_height_lower {a b z : ℂ} {H M : ℝ}
    (hM : 0 < M) (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re)
    (hz : z ∈ (roofArc a b H M).image) : min a.im b.im ≤ z.im := by
  rw [roofArc_image hM ha hb hfit] at hz
  obtain ⟨hl, hr, hh⟩ := hz
  rw [hh]
  apply le_min
  · exact (min_le_left a.im b.im).trans ha
  · apply le_min
    · exact (min_le_left a.im b.im).trans
        (le_add_of_nonneg_right (mul_nonneg hM.le (sub_nonneg.mpr hl)))
    · exact (min_le_right a.im b.im).trans
        (le_add_of_nonneg_right (mul_nonneg hM.le (sub_nonneg.mpr hr)))



theorem layoutArc_height_lower (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    ∀ z ∈ (layoutArc w n e).image,
      min (layoutPos w n ((kmswStage w n).west e)).im
        (layoutPos w n ((kmswStage w n).east e)).im ≤ z.im := by
  induction n with
  | zero =>
    have he0 : e = 0 := by change e < 1 at he; omega
    subst e
    exact fun z hz => segmentArc_height_lower (allocated_re_lt w 0 0 he) hz
  | succ n ih =>
    by_cases ho : e < (kmswStage w n).nextEdge
    · obtain ⟨hw, hb⟩ := old_endpoint_positions w n e ho
      rw [layoutArc_old w n e ho, hw, hb]
      exact ih ho
    · have hf : e ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, he⟩
      rw [layoutArc_fresh w n e hf]
      obtain ⟨ha, hb⟩ := freshEdges_endpoint_heights w n e hf
      split
      · exact fun z hz => segmentArc_height_lower (allocated_re_lt w (n + 1) e he) hz
      · exact fun z hz => roofArc_height_lower (rampSlope_pos w n) ha hb
          (freshEdges_ramp_widths_lt w n e hf) hz




structure MonotoneStageInvariant (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    extends MonotoneStageCertificate w n P where
  cover_lower : ∀ e : Fin (kmswStage w n).nextEdge,
    e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∨ ∃ i, e.val ∈ capLower i
  cover_upper : ∀ e : Fin (kmswStage w n).nextEdge,
    e.val ∈ (kmswStage w n).LL ++ (kmswStage w n).LR ∨ ∃ i, e.val ∈ capUpper i
  upper_lipschitz_margin : ∃ L : ℝ, 0 ≤ L ∧ L < rampSlope w n ∧
    ∀ x ∈ Set.Icc xmin xmax, ∀ y ∈ Set.Icc xmin xmax,
      |upper x - upper y| ≤ L * |x - y|
  image_height_le : ∀ z ∈ P.image, z.im ≤ (n : ℝ)
  pos_layout : ∀ v : Fin (kmswStage w n).nextVertex,
    P.pos v = layoutPos w n v.val
  arc_layout : ∀ d : StageDart (kmswStage w n).nextEdge,
    P.arc d = if d.2 then (layoutArc w n d.1.val).reverse else layoutArc w n d.1.val



@[expose] noncomputable def kmswStage0MonotoneInvariant (w : ℕ → Fin 3) :
    MonotoneStageInvariant w 0 (kmswStage0Drawing w) := by
  refine
    { toMonotoneStageCertificate := kmswStage0MonotoneCertificate w
      cover_lower := ?_
      cover_upper := ?_
      upper_lipschitz_margin := ?_
      image_height_le := ?_
      pos_layout := ?_
      arc_layout := ?_ }
  · intro e
    have he0 : e.val = 0 := by have he := e.isLt; change e.val < 1 at he; omega
    exact Or.inl (by simp [kmswStage, kmswInit, he0])
  · intro e
    have he0 : e.val = 0 := by have he := e.isLt; change e.val < 1 at he; omega
    exact Or.inl (by simp [kmswStage, kmswInit, he0])
  · refine ⟨0, le_rfl, rampSlope_pos w 0, ?_⟩
    intro x hx y hy
    simp [kmswStage0MonotoneCertificate]
  · intro z hz
    have hzseg : z ∈ segment ℝ (0 : ℂ) 1 :=
      (Set.ext_iff.mp (kmswStage0Drawing_image w) z).mp hz
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hzseg
    simp
  · intro v
    change Fin 2 at v
    fin_cases v <;> apply Complex.ext <;>
      norm_num [kmswStage0Drawing, layoutPos, kmswStageRank, layoutHeight]
  · rintro ⟨e, b⟩
    cases b <;>
      simp [kmswStage0Drawing, kmswStage0Arc, layoutArc, layoutPos,
        kmswStageRank, layoutHeight, segmentArc, Polyline.reverse] <;>
      constructor <;> rfl



theorem MonotoneStageInvariant.face_partition {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    (∀ i, ∃ F : P.Face, F.val = (G.cap i).region) ∧
      ∃ U : P.Face,
        U.val = (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ ∧
        P.IsUnbounded U ∧
        (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d :=
  monotoneStage_face_partition G.toMonotoneStageCertificate G.cover_lower G.cover_upper

end DirectedDistances.KMSW
