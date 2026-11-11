/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization4
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass9

/-! # Winding and parameter transport for the actual past patch

The past transfer preserves the ambient orientation and supplies actual
increasing arc reparameterizations, without identifying their schedules. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open WholePlanePastGlueData Set unitInterval

private def horizontalOrderHomeomorph (φ : ℝ ≃o ℝ) : ℂ ≃ₜ ℂ where
  toFun z := ⟨φ z.re, z.im⟩
  invFun z := ⟨φ.symm z.re, z.im⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp
  continuous_toFun := by
    simp_rw [Complex.mk_eq_add_mul_I]
    exact (Complex.continuous_ofReal.comp (φ.continuous.comp Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)
  continuous_invFun := by
    simp_rw [Complex.mk_eq_add_mul_I]
    exact (Complex.continuous_ofReal.comp (φ.symm.continuous.comp Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

private theorem horizontal_ratio (φ : ℝ ≃o ℝ) (z w : ℂ) (hne : z ≠ w) :
    (horizontalOrderHomeomorph φ z - horizontalOrderHomeomorph φ w) / (z - w) ∈
      Complex.slitPlane := by
  apply Or.inl
  rw [Complex.div_re, ← add_div]
  apply div_pos
  · change 0 < (φ z.re - φ w.re) * (z.re - w.re) + (z.im - w.im) * (z.im - w.im)
    rcases lt_trichotomy z.re w.re with h | h | h
    · have hx : 0 < (φ z.re - φ w.re) * (z.re - w.re) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr (φ.strictMono h)) (sub_neg.mpr h)
      nlinarith [sq_nonneg (z.im - w.im)]
    · have hy : z.im - w.im ≠ 0 := by
        intro hy
        exact hne (Complex.ext h (sub_eq_zero.mp hy))
      rw [h, sub_self, zero_mul, zero_add]
      exact mul_self_pos.mpr hy
    · have hx : 0 < (φ z.re - φ w.re) * (z.re - w.re) :=
        mul_pos (sub_pos.mpr (φ.strictMono h)) (sub_pos.mpr h)
      nlinarith [sq_nonneg (z.im - w.im)]
  · exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)

private theorem centered_winding {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ) :
    HasWinding (L.map (continuous_id.sub (continuous_const (y := w)))) 0 n ↔ HasWinding L w n := by
  change (∃ f : C(I, ℂ), (∀ t, Complex.exp (f t) = (L t - w) - 0) ∧ _) ↔ _
  simp only [sub_zero]
  rfl

private theorem horizontal_winding (φ : ℝ ≃o ℝ) {z : ℂ}
    (L : Path z z) (w : ℂ) (n : ℤ) (hw : w ∉ Set.range L)
    (hn : HasWinding L w n) :
    HasWinding (L.map (horizontalOrderHomeomorph φ).continuous)
      (horizontalOrderHomeomorph φ w) n := by
  let F := horizontalOrderHomeomorph φ
  let A := L.map (continuous_id.sub (continuous_const (y := w)))
  let B := (L.map F.continuous).map (continuous_id.sub (continuous_const (y := F w)))
  apply (centered_winding (L.map F.continuous) (F w) n).mp
  apply hasWinding_of_ratio_mem_slitPlane A B 0 n
  · intro t ht
    exact hw ⟨t, sub_eq_zero.mp ht⟩
  · intro t ht
    exact hw ⟨t, F.injective (sub_eq_zero.mp ht)⟩
  · intro t
    change ((F (L t) - F w) - 0) / ((L t - w) - 0) ∈ Complex.slitPlane
    simpa only [sub_zero] using horizontal_ratio φ (L t) w (fun ht => hw ⟨t, ht⟩)
  · exact (centered_winding L w n).mpr hn

private theorem horizontal_orientation (φ : ℝ ≃o ℝ) :
    OrientationPreserving (horizontalOrderHomeomorph φ) := by
  intro z L w hw n
  constructor
  · exact horizontal_winding φ L w n hw
  · intro hn
    have hw' : horizontalOrderHomeomorph φ w ∉
        Set.range (L.map (horizontalOrderHomeomorph φ).continuous) := by
      rintro ⟨t, ht⟩
      exact hw ⟨t, (horizontalOrderHomeomorph φ).injective ht⟩
    have hn' := horizontal_winding φ.symm
      (L.map (horizontalOrderHomeomorph φ).continuous)
      (horizontalOrderHomeomorph φ w) n hw' hn
    obtain ⟨f, hf, hi⟩ := hn'
    refine ⟨f, ?_, hi⟩
    intro t
    have ht := hf t
    change Complex.exp (f t) =
      horizontalOrderHomeomorph φ.symm (horizontalOrderHomeomorph φ (L t)) -
      horizontalOrderHomeomorph φ.symm (horizontalOrderHomeomorph φ w) at ht
    simpa [horizontalOrderHomeomorph] using ht

private def halfTurn : ℂ ≃ₜ ℂ where
  toFun z := -z
  invFun z := -z
  left_inv := neg_neg
  right_inv := neg_neg
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

private theorem halfTurn_winding {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ)
    (hn : HasWinding L w n) : HasWinding (L.map halfTurn.continuous) (halfTurn w) n := by
  obtain ⟨f, hf, hi⟩ := hn
  refine ⟨f + ContinuousMap.const I (Complex.log (-1)), ?_, ?_⟩
  · intro t
    change Complex.exp (f t + Complex.log (-1)) = -L t - -w
    rw [Complex.exp_add, hf t, Complex.exp_log (by norm_num)]
    ring
  · change (f 1 + Complex.log (-1)) - (f 0 + Complex.log (-1)) = _
    simpa only [add_sub_add_right_eq_sub] using hi

private theorem halfTurn_orientation : OrientationPreserving halfTurn := by
  intro z L w _ n
  constructor
  · exact halfTurn_winding L w n
  · intro hn
    have hn' := halfTurn_winding (L.map halfTurn.continuous) (halfTurn w) n hn
    obtain ⟨f, hf, hi⟩ := hn'
    refine ⟨f, ?_, hi⟩
    intro t
    have ht := hf t
    change Complex.exp (f t) = - -L t - - -w at ht
    simpa only [neg_neg] using ht

/-- Helper toward Proposition 3.9: the explicit past transfer preserves
all winding numbers, including its non-affine horizontal interpolation. -/
theorem uibotPastTransfer_orientationPreserving (φ : ℝ ≃o ℝ)
    (f0 fp : ℝ → ℝ) (h0 : Continuous f0) (hp : Continuous fp) :
    OrientationPreserving (pastTransferHomeomorph φ f0 fp h0 hp) := by
  let A := uibhbotVerticalSeamTransfer fp (fun _ => 0) hp continuous_const
  let B := horizontalOrderHomeomorph φ
  let C := uibhbotVerticalSeamTransfer (fun _ => 0) f0 continuous_const h0
  have he : ((A.trans B).trans halfTurn).trans C =
      pastTransferHomeomorph φ f0 fp h0 hp := by
    apply Homeomorph.ext
    intro z
    apply Complex.ext <;>
      simp [A, B, C, uibhbotVerticalSeamTransfer, horizontalOrderHomeomorph,
        halfTurn, pastTransferHomeomorph, pastTransfer]
    ring
  rw [← he]
  apply OrientationPreserving.trans
  · apply OrientationPreserving.trans
    · apply OrientationPreserving.trans
      · exact @uibhbotVerticalSeamTransfer_orientationPreserving fp (fun _ => 0) hp continuous_const
      · exact @horizontal_orientation φ
    · exact @halfTurn_orientation
  · exact @uibhbotVerticalSeamTransfer_orientationPreserving (fun _ => 0) f0 continuous_const h0

private theorem simpleArc_parameter (γ δ : I → ℂ)
    (hγc : Continuous γ) (hδc : Continuous δ)
    (hγi : Function.Injective γ) (hδi : Function.Injective δ)
    (hrange : Set.range γ = Set.range δ) (b : Bool)
    (h0 : γ 0 = δ (if b then 1 else 0))
    (h1 : γ 1 = δ (if b then 0 else 1)) :
    ∃ φ : I ≃ₜ I,
      (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
      ∀ t, γ t = δ (φ t) := by
  let eγ : I ≃ₜ Set.range γ := (hγc.isClosedEmbedding hγi).isEmbedding.toHomeomorph
  let eδ : I ≃ₜ Set.range δ := (hδc.isClosedEmbedding hδi).isEmbedding.toHomeomorph
  let φ : I ≃ₜ I := (eγ.trans (Homeomorph.setCongr hrange)).trans eδ.symm
  have hmatch (t : I) : δ (φ t) = γ t :=
    congrArg Subtype.val (eδ.apply_symm_apply ((Homeomorph.setCongr hrange) (eγ t)))
  have hzero : φ 0 = if b then 1 else 0 := hδi ((hmatch 0).trans h0)
  have hone : φ 1 = if b then 0 else 1 := hδi ((hmatch 1).trans h1)
  refine ⟨φ, ?_, ?_, fun t => (hmatch t).symm⟩
  · intro hb
    apply φ.continuous.strictMono_of_inj_boundedOrder _ φ.injective
    change φ 0 ≤ φ 1
    rw [hzero, hone, hb]
    exact zero_le_one
  · intro hb
    apply φ.continuous.strictAnti_of_inj_boundedOrder _ φ.injective
    change φ 1 ≤ φ 0
    rw [hzero, hone, hb]
    exact zero_le_one

private theorem graph_path_range_subset (f : ℝ → ℝ) (γ δ : I → ℂ)
    (hγc : Continuous γ) (hδc : Continuous δ) (hγi : Function.Injective γ)
    (hγ : ∀ t, (γ t).im = f (γ t).re) (hδ : ∀ t, (δ t).im = f (δ t).re)
    (h0 : γ 0 = δ 0) (h1 : γ 1 = δ 1) : Set.range γ ⊆ Set.range δ := by
  have hi : Function.Injective (fun t => (γ t).re) := by
    intro s t hst
    apply hγi
    exact Complex.ext hst ((hγ s).trans ((congrArg f hst).trans (hγ t).symm))
  have hc := Complex.continuous_re.comp hγc
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  have hb : (γ t).re ∈ Set.uIcc (δ 0).re (δ 1).re := by
    rw [← h0, ← h1]
    rcases hc.strictMono_of_inj_boundedOrder' hi with hm | hm
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hm.monotone (bot_le : (0 : I) ≤ t),
        hm.monotone (le_top : t ≤ (1 : I))⟩)
    · exact Set.mem_uIcc.mpr (Or.inr ⟨hm.antitone (le_top : t ≤ (1 : I)),
        hm.antitone (bot_le : (0 : I) ≤ t)⟩)
  have hδc' := Complex.continuous_re.comp hδc
  rcases Set.mem_uIcc.mp hb with hb | hb
  · obtain ⟨s, _, hs⟩ := intermediate_value_Icc (show (0 : I) ≤ 1 from zero_le_one)
      hδc'.continuousOn hb
    exact ⟨s, Complex.ext hs ((hδ s).trans ((congrArg f hs).trans (hγ t).symm))⟩
  · obtain ⟨s, _, hs⟩ := intermediate_value_Icc' (show (0 : I) ≤ 1 from zero_le_one)
      hδc'.continuousOn hb
    exact ⟨s, Complex.ext hs ((hδ s).trans ((congrArg f hs).trans (hγ t).symm))⟩

private theorem finiteDart_limitVertex (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    kmswLimitDartVertex w (d.1.val, d.2) = (stageVertex w n d).val := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp [kmswLimitDartVertex, stageVertex, stageEndpoint, hb, hw, he]

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
local notation "Qp" => familyQ (kmswPastCode W) (monotone_family_all (kmswPastCode W))
local notation "T" => PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W)
  h0 hpast ((And.left H) 0) (past_finiteIncidence W H)

/-- Helper toward Proposition 3.9: the actual seam transfer used by the
whole-plane glued drawing is orientation-preserving. -/
theorem uibotGlued_pastTransfer_orientation : OrientationPreserving T := by
  exact @uibotPastTransfer_orientationPreserving _ _ _ _ _

private theorem pastStage_start (n : ℕ)
    (d : StageDart (kmswStage (kmswPastCode W) n).nextEdge) :
    T (((Qp n).arc d).start) =
      ((G).arc (kmswPastDart W (d.1.val, d.2))).start := by
  rw [(Qp n).arc_start, (G).arc_start, pastDart_vertex,
    finiteDart_limitVertex, uibotGlued_pastStage_pos]

private theorem pastStage_finish (n : ℕ)
    (d : StageDart (kmswStage (kmswPastCode W) n).nextEdge) :
    T (((Qp n).arc d).finish) =
      ((G).arc (kmswPastDart W (d.1.val, d.2))).finish := by
  rw [(Qp n).arc_finish, (G).arc_finish, pastDart_flip]
  change T ((Qp n).pos (stageVertex _ n (edgeFlip _ d))) =
    (G).pos (wholePlaneDartVertex W (kmswPastDart W (d.1.val, !d.2)))
  rw [pastDart_vertex]
  have he := finiteDart_limitVertex (kmswPastCode W) n (edgeFlip _ d)
  change kmswLimitDartVertex _ (d.1.val, !d.2) = _ at he
  rw [he]
  exact (uibotGlued_pastStage_pos W h0 hpast H n (stageVertex _ n (edgeFlip _ d))).symm

/-- Helper toward Proposition 3.9: the actual past transfer carries every
finite past arc image, including the seam arcs chosen from the future side,
to its whole-plane image. -/
theorem uibotGlued_pastStage_arc_image_all (n : ℕ)
    (d : StageDart (kmswStage (kmswPastCode W) n).nextEdge) :
    ((G).arc (kmswPastDart W (d.1.val, d.2))).image = T '' ((Qp n).arc d).image := by
  by_cases hd : kmswPastSeamEdge W d.1.val
  · obtain ⟨j, hj⟩ := kmswPastSeamEdge_image_boundary W h0 d.1.val hd
    have hk : boundaryOuterEdge (kmswPastCode W) hpast (-j) = d.1.val := by
      apply kmswPastEdge_injective W
      exact (kmswPastEdge_seam_match_neg W h0 hpast (-j)).trans (by simpa using hj.symm)
    let f := seamFun (shiftedStream W 0) h0 (H.1 0)
    let γ : I → ℂ := fun t => T (((Qp n).arc d).toPath t)
    let δ : I → ℂ := ((G).arc (kmswPastDart W (d.1.val, d.2))).toPath
    have hγc : Continuous γ := (T).continuous.comp ((Qp n).arc d).toPath.continuous
    have hδc : Continuous δ := ((G).arc _).toPath.continuous
    have hγi : Function.Injective γ := (T).injective.comp
      (((Qp n).arc d).toPath_injective ((Qp n).arc_length d) ((Qp n).arc_simple d))
    have hδi : Function.Injective δ :=
      ((G).arc _).toPath_injective ((G).arc_length _) ((G).arc_simple _)
    have hγ (t : I) : (γ t).im = f (γ t).re := by
      let P := monotoneFamilyDrawing (kmswPastCode W) (past_finiteIncidence W H)
        (monotone_family_all (kmswPastCode W))
      have hm : ((Qp n).arc d).toPath t ∈ (P.arc (d.1.val, d.2)).image := by
        rw [show P.arc (d.1.val, d.2) = (Qp n).arc d from
          familyDrawing_arc (kmswPastCode W) (past_finiteIncidence W H)
            (monotone_family_all (kmswPastCode W)) n d, ← Polyline.range_toPath]
        exact ⟨t, rfl⟩
      have he : (P.arc (d.1.val, true)).image = (P.arc (d.1.val, d.2)).image := by
        cases hb : d.2
        · exact P.arc_image_flip (d.1.val, false)
        · rfl
      have hseam : (((Qp n).arc d).toPath t).im =
          seamFun (kmswPastCode W) hpast (past_finiteIncidence W H)
            (((Qp n).arc d).toPath t).re := by
        apply (show _ ∈ {z : ℂ | z.im = seamFun (kmswPastCode W) hpast
          (past_finiteIncidence W H) z.re} from ?_)
        rw [seamFun_graph (kmswPastCode W) hpast (past_finiteIncidence W H)]
        apply mem_iUnion.mpr
        refine ⟨-j, ?_⟩
        change _ ∈ (P.arc (boundaryOuterEdge (kmswPastCode W) hpast (-j), true)).image
        rw [hk, he]
        exact hm
      have ht := pastTransfer_height
        (PastDrawingTransfer.phi (shiftedStream W 0) (kmswPastCode W)
          h0 hpast (H.1 0) (past_finiteIncidence W H))
        f (seamFun (kmswPastCode W) hpast (past_finiteIncidence W H))
        (((Qp n).arc d).toPath t)
      rw [hseam, sub_self, neg_zero] at ht
      exact sub_eq_zero.mp ht
    have hδ (t : I) : (δ t).im = f (δ t).re := by
      have hm : δ t ∈ ((G).arc (kmswPastDart W
          (boundaryOuterEdge (kmswPastCode W) hpast (-j), d.2))).image := by
        rw [hk, ← Polyline.range_toPath]
        exact ⟨t, rfl⟩
      exact WholePlanePastGlueGeometry.past_seam_arc_graph W h0 hpast H (-j) d.2 hm
    have hzero : γ 0 = δ 0 := by
      simp only [γ, δ, Path.source]
      exact pastStage_start W h0 hpast H n d
    have hone : γ 1 = δ 1 := by
      simp only [γ, δ, Path.target]
      exact pastStage_finish W h0 hpast H n d
    have hrange : Set.range γ = Set.range δ := Set.Subset.antisymm
      (graph_path_range_subset f γ δ hγc hδc hγi hγ hδ hzero hone)
      (graph_path_range_subset f δ γ hδc hγc hδi hδ hγ hzero.symm hone.symm)
    change Set.range (T ∘ ((Qp n).arc d).toPath) =
      Set.range ((G).arc (kmswPastDart W (d.1.val, d.2))).toPath at hrange
    rw [Set.range_comp, Polyline.range_toPath, Polyline.range_toPath] at hrange
    exact hrange.symm
  · exact uibotGlued_pastStage_arc_image W h0 hpast H n d hd

/-- Helper toward Proposition 3.9: every past arc has an actual
interval reparameterization under the same ambient transfer. The parameter
is increasing or decreasing according to the target dart's storage reversal. -/
theorem uibotGlued_pastStage_arc_param (n : ℕ)
    (d : StageDart (kmswStage (kmswPastCode W) n).nextEdge)
    (b : Bool) :
    ∃ φ : I ≃ₜ I,
      (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
      ∀ t, T (((Qp n).arc d).toPath t) =
        ((G).arc (if b then wholePlaneDartFlip W (kmswPastDart W (d.1.val, d.2))
          else kmswPastDart W (d.1.val, d.2))).toPath (φ t) := by
  let D := kmswPastDart W (d.1.val, d.2)
  let E := if b then wholePlaneDartFlip W D else D
  refine simpleArc_parameter (fun t => T (((Qp n).arc d).toPath t))
    (fun t => ((G).arc E).toPath t)
    ((T).continuous.comp ((Qp n).arc d).toPath.continuous)
    (((G).arc E).toPath.continuous)
    ((T).injective.comp (((Qp n).arc d).toPath_injective
      ((Qp n).arc_length d) ((Qp n).arc_simple d)))
    (((G).arc E).toPath_injective ((G).arc_length E) ((G).arc_simple E))
    ?_ b ?_ ?_
  · change Set.range (T ∘ ((Qp n).arc d).toPath) = Set.range ((G).arc E).toPath
    rw [Set.range_comp, Polyline.range_toPath, Polyline.range_toPath]
    have hi := uibotGlued_pastStage_arc_image_all W h0 hpast H n d
    cases hb : b
    · simpa only [E, hb, Bool.false_eq_true, ite_false] using hi.symm
    · simpa only [E, hb, ite_true] using hi.symm.trans ((G).arc_image_flip D).symm
  · cases hb : b <;> simp only [E, hb, Bool.false_eq_true, ite_false, ite_true, Path.source, Path.target]
    · exact pastStage_start W h0 hpast H n d
    · rw [(G).arc_flip, Polyline.finish_reverse]
      exact pastStage_start W h0 hpast H n d
  · cases hb : b <;> simp only [E, hb, Bool.false_eq_true, ite_false, ite_true, Path.source, Path.target]
    · exact pastStage_finish W h0 hpast H n d
    · rw [(G).arc_flip, Polyline.start_reverse]
      exact pastStage_finish W h0 hpast H n d

/-- Helper toward Proposition 3.9: one ambient orientation-preserving
homeomorphism simultaneously transports every past-stage position and every
dart path, with the parameter monotonicity required by its flip. -/
theorem uibotGlued_pastStage_geometry (n : ℕ) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (kmswPastCode W) n).nextVertex,
        h ((Qp n).pos v) = (G).pos (kmswPastVertex W v.val)) ∧
      ∀ (d : StageDart (kmswStage (kmswPastCode W) n).nextEdge),
        ∀ b : Bool,
        ∃ φ : I ≃ₜ I,
          (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
          ∀ t, h (((Qp n).arc d).toPath t) =
            ((G).arc (if b then wholePlaneDartFlip W (kmswPastDart W (d.1.val, d.2))
              else kmswPastDart W (d.1.val, d.2))).toPath (φ t) := by
  refine ⟨T, ?_, ?_, ?_⟩
  · exact @uibotGlued_pastTransfer_orientation W h0 hpast H
  · intro v
    exact (uibotGlued_pastStage_pos W h0 hpast H n v).symm
  · exact uibotGlued_pastStage_arc_param W h0 hpast H n

/-- Helper toward Proposition 3.9: on the actual StageGeom-free finite
domain and whole-plane geometric edge quotients, the past transfer supplies
the position and arc-parameter fields with the chosen target storage flip.
This is a patch embedding, not a captured-ball equivalence. -/
theorem uibotGlued_pastStage_domain_geometry
    (hpresent : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (n : ℕ) (U : (Qp n).Face) (hU : (Qp n).IsUnbounded U)
    (hborder : ∀ d, (Qp n).dartBorders d U ↔
      (kmswStageDirectedMap (kmswPastCode W) n).IsOuter d) :
    let M := (kmswStageDrawingDomainRootedMapOfExteriorFace (Qp n) U hU hborder).map
    let M' := uibotWholePlaneGeometricMap W H (G) hpresent
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (kmswPastCode W) n).nextVertex,
        h (M.pos v) = M'.pos (kmswPastVertex W v.val)) ∧
      (∀ i : Fin (kmswStage (kmswPastCode W) n).triangles.length,
        ∃ F : (Qp n).Face, ∃ F' : (G).Face,
          F.val = ((familyG _ (monotone_family_all _) n).cap i).region ∧
            h '' F.val = F'.val) ∧
      ∀ e : (Qp n).GeometricEdge,
        let D := kmswPastDart W (e.out.1.val, e.out.2)
        let e' := Quotient.mk (G).edgeSetoid D
        ∃ b : Bool, e'.out = (if b then wholePlaneDartFlip W D else D) ∧
          ∃ φ : I ≃ₜ I,
            (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
            ∀ t, h (M.arc e t) = M'.arc e' (φ t) := by
  dsimp only
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · exact @uibotGlued_pastTransfer_orientation W h0 hpast H
  · intro v
    exact (uibotGlued_pastStage_pos W h0 hpast H n v).symm
  · intro i
    obtain ⟨F, F', hF, hmap⟩ := uibotGlued_pastStage_cap_face W h0 hpast H n i
    refine ⟨F, F', hF, ?_⟩
    exact hmap.symm
  · intro e
    let D := kmswPastDart W (e.out.1.val, e.out.2)
    let e' := Quotient.mk (G).edgeSetoid D
    rcases (G).geometricEdge_out_mk D with he | he
    · obtain ⟨φ, hm, ha, harc⟩ := uibotGlued_pastStage_arc_param W h0 hpast H n e.out false
      refine ⟨false, he, φ, hm, ha, ?_⟩
      intro t
      change T (((Qp n).arc e.out).toPath t) = ((G).arc e'.out).toPath (φ t)
      rw [show e'.out = D from he]
      exact harc t
    · obtain ⟨φ, hm, ha, harc⟩ := uibotGlued_pastStage_arc_param W h0 hpast H n e.out true
      refine ⟨true, he, φ, hm, ha, ?_⟩
      intro t
      change T (((Qp n).arc e.out).toPath t) = ((G).arc e'.out).toPath (φ t)
      rw [show e'.out = wholePlaneDartFlip W D from he]
      exact harc t

local notation "Qf" => familyQ (shiftedStream W 0) (monotone_family_all (shiftedStream W 0))

/-- Helper toward Proposition 3.9: canonical future arcs have increasing
or decreasing interval parameters for either stored whole-plane dart. -/
theorem uibotGlued_futureStage_arc_param (n : ℕ)
    (d : StageDart (kmswStage (shiftedStream W 0) n).nextEdge) (b : Bool) :
    ∃ φ : I ≃ₜ I,
      (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
      ∀ t, ((Qf n).arc d).toPath t =
        ((G).arc (if b then wholePlaneDartFlip W (wholePlaneDartι W 0 (d.1.val, d.2))
          else wholePlaneDartι W 0 (d.1.val, d.2))).toPath (φ t) := by
  let D := wholePlaneDartι W 0 (d.1.val, d.2)
  have hD : (G).arc D = (Qf n).arc d := uibotGlued_futureStage_arc W h0 hpast H n d
  cases b
  · refine ⟨Homeomorph.refl I, fun _ => strictMono_id, by simp, ?_⟩
    intro t
    exact congrArg (fun p : Polyline => p.toPath t) hD.symm
  · refine simpleArc_parameter (((Qf n).arc d).toPath)
      (((G).arc (wholePlaneDartFlip W D)).toPath)
      (((Qf n).arc d).toPath.continuous) (((G).arc _).toPath.continuous)
      (((Qf n).arc d).toPath_injective ((Qf n).arc_length d) ((Qf n).arc_simple d))
      (((G).arc _).toPath_injective ((G).arc_length _) ((G).arc_simple _))
      ?_ true ?_ ?_
    · rw [Polyline.range_toPath, Polyline.range_toPath]
      exact (congrArg Polyline.image hD.symm).trans ((G).arc_image_flip D).symm
    · simp only [ite_true, Path.source, Path.target]
      exact ((congrArg Polyline.finish ((G).arc_flip D)).trans
        ((Polyline.finish_reverse ((G).arc D)).trans (congrArg Polyline.start hD))).symm
    · simp only [ite_true, Path.source, Path.target]
      exact ((congrArg Polyline.start ((G).arc_flip D)).trans
        ((Polyline.start_reverse ((G).arc D)).trans (congrArg Polyline.finish hD))).symm

/-- Helper toward Proposition 3.9: on the actual StageGeom-free future
domain, the identity ambient homeomorphism supplies the position and arc
fields, including both possible storage flips on the geometric quotients.
The exterior certificate exists by `uibotCanonicalStage_exterior`. -/
theorem uibotGlued_futureStage_domain_geometry
    (hpresent : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (n : ℕ) (U : (Qf n).Face) (hU : (Qf n).IsUnbounded U)
    (hborder : ∀ d, (Qf n).dartBorders d U ↔
      (kmswStageDirectedMap (shiftedStream W 0) n).IsOuter d) :
    let M := (kmswStageDrawingDomainRootedMapOfExteriorFace (Qf n) U hU hborder).map
    let M' := uibotWholePlaneGeometricMap W H (G) hpresent
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (shiftedStream W 0) n).nextVertex,
        h (M.pos v) = M'.pos (wholePlaneVertexι W 0 v.val)) ∧
      (∀ i : Fin (kmswStage (shiftedStream W 0) n).triangles.length,
        ∃ F : (Qf n).Face, ∃ F' : (G).Face,
          F.val = ((familyG _ (monotone_family_all _) n).cap i).region ∧
            h '' F.val = F'.val) ∧
      ∀ e : (Qf n).GeometricEdge,
        let D := wholePlaneDartι W 0 (e.out.1.val, e.out.2)
        let e' := Quotient.mk (G).edgeSetoid D
        ∃ b : Bool, e'.out = (if b then wholePlaneDartFlip W D else D) ∧
          ∃ φ : I ≃ₜ I,
            (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
            ∀ t, h (M.arc e t) = M'.arc e' (φ t) := by
  dsimp only
  refine ⟨Homeomorph.refl ℂ, orientationPreserving_refl, ?_, ?_, ?_⟩
  · intro v
    exact (uibotGlued_futureStage_pos W h0 hpast H n v).symm
  · intro i
    obtain ⟨F, F', hF, hmap⟩ := uibotGlued_futureStage_cap_face W h0 hpast H n i
    refine ⟨F, F', hF, ?_⟩
    simpa only [Homeomorph.refl_apply, Set.image_id] using hmap.symm
  · intro e
    let D := wholePlaneDartι W 0 (e.out.1.val, e.out.2)
    let e' := Quotient.mk (G).edgeSetoid D
    rcases (G).geometricEdge_out_mk D with he | he
    · obtain ⟨φ, hm, ha, harc⟩ := uibotGlued_futureStage_arc_param W h0 hpast H n e.out false
      refine ⟨false, he, φ, hm, ha, ?_⟩
      intro t
      change ((Qf n).arc e.out).toPath t = ((G).arc e'.out).toPath (φ t)
      rw [show e'.out = D from he]
      exact harc t
    · obtain ⟨φ, hm, ha, harc⟩ := uibotGlued_futureStage_arc_param W h0 hpast H n e.out true
      refine ⟨true, he, φ, hm, ha, ?_⟩
      intro t
      change ((Qf n).arc e.out).toPath t = ((G).arc e'.out).toPath (φ t)
      rw [show e'.out = wholePlaneDartFlip W D from he]
      exact harc t

/- OPEN centered-ball comparison, with all binders; this is not a declaration:

∀ (n N r : ℕ) (hr : 0 < r)
  (w : Fin (n - 1) → Fin 3) (j : Fin n)
  (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (G : WholePlaneDrawing W H)
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (P : StageDrawing (finiteCodeExtend w) (n - 1))
  (U : P.Face) (hU : P.IsUnbounded U)
  (hborder : ∀ d, P.dartBorders d U ↔
    (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
  (hwindow : uibotFiniteRootWindow N w j =
    some (fun i => shiftedStream W N i.val))
  (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r),
  Nonempty (D39GeomBallIsoV2 r
    (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map
    (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega))
    (uibotWholePlaneGeometricMap W H G hp)
    (uibotWholePlaneGeometricRoot W H G)).

The proved geometry concerns canonical finite future/past patches and the
canonical glued drawing. It includes seam arcs, preserves their actual
parameter schedules via homeomorphisms, and preserves the original cap
faces. It does not produce a single chart identifying a centered finite-word
stage with the union of the past and future patches. It also does not prove
that arbitrary P and G are ambiently equivalent to these canonical choices,
or construct the bijection on all retained original faces of the captured
ball. Thus neither hwindow nor hcap is consumed by these partial results.
The earlier StageGeom-based comparison is not used to manufacture any such -/

end DirectedDistances.PaperProofs.Section3
end
