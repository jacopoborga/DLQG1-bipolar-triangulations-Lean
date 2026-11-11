module

public import DirectedDistances.PaperProofs.Section7.CellSDPLowerAssembly
public import DirectedDistances.PaperProofs.Section7.Section7SdpUnconditional
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperUnconditional
public import DirectedDistances.PaperProofs.Section7.CellSDPReversalLaw
import DirectedDistances.KMSW.KMSWMeasurability

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive

/-- Helper (code level, SDP) toward Lemma 7.6 (lem-cell-sdp-lower); not a paper result.
one constant works for every positive size. Source-model identification remains separate. -/
theorem cell_sdp_lower_sdpCode :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
      1 - δ ≤ iidCodeMeasure.real
        {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
              (kmswStage (fun i => ω (i + 1)) n).east e =
                boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)) ∧
          A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
            ((sdp (⟨boundaryVertex (fun i => ω (i + 1)) h 0⟩ :
              StagePresentVertex (fun i => ω (i + 1)) n)
              ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ)} := by
  exact cell_sdp_lower_conditional sdp_hstable_of_window_negative_limit_sdpCode

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
identities, preserving presence and endpoints. -/
private theorem window_arrow_data (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (e : a ⟶ b) :
    EdgePresent w (kmswWindowEdgeMapInf w n e.val) ∧
      edgeWest w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n a.id ∧
      edgeEast w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n b.id := by
  obtain ⟨m, hm, hp⟩ := e.property.1
  have hr := kmswWindowPatchData_rel w n m
  have hg : kmswWindowEdgeMapInf w n e.val < (kmswStage w (n + m)).nextEdge := by
    rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.edge_bound e.val hm
  refine ⟨⟨n + m, hg, ?_⟩, ?_, ?_⟩
  · rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.present e.val hm hp
  · rw [← (edge_endpoints_eq w hg).1,
      kmswWindowEdgeMapInf_west w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).1, e.property.2.1]
  · rw [← (edge_endpoints_eq w hg).2,
      kmswWindowEdgeMapInf_east w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).2, e.property.2.2]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem window_path_forward (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (q : Path a b) :
    ∃ p : Path (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n b.id⟩, p.length = q.length := by
  induction q with
  | nil => exact ⟨Path.nil, rfl⟩
  | cons q e ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.cons ⟨kmswWindowEdgeMapInf w n e.val, window_arrow_data w n e⟩, ?_⟩
    simp only [Path.length_cons, hp]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
OPPOSITE direction to the selected-target confinement obligation. This does not
prove that obligation false: equality may hold under additional geometric arguments.
Infinity is retained throughout. -/
theorem cellSdpUpper_window_sdp_le (w : ℕ → Fin 3) (n : ℕ)
    (a b : PresentVertex (fun i => w (n + i))) :
    sdp (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w)
      ⟨kmswWindowVertexMapInf w n b.id⟩ ≤ sdp a b := by
  change _ ≤ ⨅ q : Path a b, (q.length : ℕ∞)
  refine le_iInf fun q => ?_
  obtain ⟨p, hp⟩ := window_path_forward w n q
  exact (sdp_le_length p).trans_eq (by rw [hp])




theorem cellSdpUpper_confinement_at_seam (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (v : ℕ) :
    (sdp (boundaryPresentVertex (fun i => w (n + i)) hn
        (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) ⟨v⟩).toNat ≤
      (sdp (⟨boundaryVertex w h0 ((kmswStage w n).LR.length : ℤ)⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n v⟩).toNat := by
  exact (congrArg ENat.toNat (presentSdp_rightBoundary_seam_eq w n v h0 hn)).le

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
actual lower endpoints have the asserted lower labels, and upper labels are actual
upper endpoints. This is an explicit obligation, not an established identification. -/
@[expose] def cellSdpUpper_boundaryLabelIdentification : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
      ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)),
        (∀ x : ℕ,
          (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
            (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
          ∃ ℓ : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ ℓ ∧
            ℓ ≤ ((kmswStage w n).LR.length : ℤ) ∧ boundaryVertex w h0 ℓ = x) ∧
        (∀ k : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k →
          k ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
          ∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
            (kmswStage w n).west e = kmswWindowVertexMapInf w n
                (boundaryVertex (fun i => w (n + i)) hn k) ∨
            (kmswStage w n).east e = kmswWindowVertexMapInf w n
                (boundaryVertex (fun i => w (n + i)) hn k))

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
map to reversed lower endpoints, reversed upper endpoints map back to lower
endpoints, and directed distances reverse. No bounded-distance estimate is assumed. -/
@[expose] def cellSdpUpper_reversalBoundaryDistanceTransport : Prop :=
  ∀ n : ℕ, ∀ ω : ℕ → Fin 3,
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal n ω (i + 1)
    ∃ f : ℕ ≃ ℕ,
      (∀ y : ℕ,
        (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
          (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
        ∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
          (kmswStage wr n).west e = f y ∨ (kmswStage wr n).east e = f y) ∧
      (∀ x : ℕ,
        (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
          (kmswStage wr n).west e = x ∨ (kmswStage wr n).east e = x) →
        ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
          (kmswStage w n).west e = f.symm x ∨
            (kmswStage w n).east e = f.symm x) ∧
      (∀ a b : ℕ,
        sdp (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
          sdp (⟨f b⟩ : StagePresentVertex wr n) ⟨f a⟩)

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
including infinity for unreachable pairs. -/
private theorem stage_sdp_congr {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) (a b : ℕ) :
    sdp (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      sdp (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
  let F : Prefunctor (StagePresentVertex w n) (StagePresentVertex w' n) :=
    { obj := fun v => ⟨v.id⟩
      map := fun e => ⟨e.val, by simpa only [h] using e.property⟩ }
  let G : Prefunctor (StagePresentVertex w' n) (StagePresentVertex w n) :=
    { obj := fun v => ⟨v.id⟩
      map := fun e => ⟨e.val, by simpa only [h] using e.property⟩ }
  have hF {u v : StagePresentVertex w n} (p : Path u v) :
      (F.mapPath p).length = p.length := by
    induction p with
    | nil => rfl
    | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
  have hG {u v : StagePresentVertex w' n} (p : Path u v) :
      (G.mapPath p).length = p.length := by
    induction p with
    | nil => rfl
    | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
  apply le_antisymm
  · change _ ≤ ⨅ p : Path (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩, (p.length : ℕ∞)
    exact le_iInf fun p => (sdp_le_length (G.mapPath p)).trans_eq (by rw [hG])
  · change _ ≤ ⨅ p : Path (⟨a⟩ : StagePresentVertex w n) ⟨b⟩, (p.length : ℕ∞)
    exact le_iInf fun p => (sdp_le_length (F.mapPath p)).trans_eq (by rw [hF])

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
measurable event, since it depends only on the first `n` letters. -/
private theorem measurable_first_endpoint_event (n : ℕ) (t : ℕ∞) :
    MeasurableSet {ω : ℕ → Fin 3 |
      let w := fun i => ω (i + 1)
      ∀ x : ℕ,
        (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
          (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
        ∃ y : ℕ,
          (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
            (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
          sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤ t} := by
  refine measurableSet_of_factors_prefix (n + 1) _ ?_
  intro ω ω' h
  have hs := kmswStage_shift_congr (n := n)
    (fun i _ hi => h i (by omega : i < n + 1))
  dsimp only
  simp_rw [stage_sdp_congr hs]
  rw [hs]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
actual lower endpoints, from exactly confinement and boundary-label identification. -/
theorem cellSdpUpper_first_endpoint_prob_sdpRest
    (hconf : cellSdpUpper_selectedTargetConfinement)
    (hlabels : cellSdpUpper_boundaryLabelIdentification) :
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          ∀ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
            ∃ y : ℕ,
              (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
                (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)} := by
  intro δ hδ
  obtain ⟨A₀, hA₀, hprob⟩ := cellSdpUpper_first_bullet_prob_sdpRest hconf δ hδ
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA n hn
  refine (hprob A hA n hn).trans (ENNReal.toReal_mono (by finiteness) (measure_mono_ae ?_))
  filter_upwards [hlabels, iidCodes_ae_boundaryHitWitnesses,
    iidCodes_ae_uibotBoundary_allTimes] with ω hl h0 hf
  intro hfirst
  dsimp only at hl hfirst ⊢
  obtain ⟨⟨_, hn', _⟩, _, _⟩ := hf n
  have hn'' : BoundaryHitWitnesses (fun i => ω (n + i + 1)) := by
    simpa only [Nat.add_assoc] using hn'
  intro x hx
  obtain ⟨ℓ, hℓL, hℓR, hℓx⟩ := (hl n h0 hn'').1 x hx
  obtain ⟨hnw, k, hkL, hkR, hd⟩ := hfirst h0 ℓ hℓL hℓR
  refine ⟨kmswWindowVertexMapInf (fun i => ω (i + 1)) n
    (boundaryVertex (fun i => ω (n + i + 1)) hnw k),
    (hl n h0 hnw).2 k hkL hkR, ?_⟩
  simpa only [hℓx] using hd

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
one constant uniform in every positive `n`, conditional on exactly three named OPEN
obligations: selected-target confinement, boundary labels, and reversal transport.
Code reversal preserves the law unconditionally. The source's final `n → ∞` sentence
at lines 364–366 does not replace the uniform quantifiers in this helper. -/
theorem cell_sdp_upper_both_endpoints_sdpRest
    (hconf : cellSdpUpper_selectedTargetConfinement)
    (hlabels : cellSdpUpper_boundaryLabelIdentification)
    (hreverse : cellSdpUpper_reversalBoundaryDistanceTransport) :
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          (∀ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
            ∃ y : ℕ,
              (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
                (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
          (∀ y : ℕ,
            (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
              (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
            ∃ x : ℕ,
              (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
                (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞))} := by
  intro δ hδ
  obtain ⟨A₀, hA₀, hprob⟩ :=
    cellSdpUpper_first_endpoint_prob_sdpRest hconf hlabels (δ / 2) (by linarith)
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA n hn
  let t : ℕ∞ := (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)
  let E : Set (ℕ → Fin 3) := {ω |
    let w := fun i => ω (i + 1)
    ∀ x : ℕ,
      (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
        (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
      ∃ y : ℕ,
        (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
          (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
        sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤ t}
  let R := codeReversal n ⁻¹' E
  have hE : MeasurableSet E := measurable_first_endpoint_event n t
  have hR : MeasurableSet R := hE.preimage (measurePreserving_codeReversal n).measurable
  have hER : iidCodeMeasure.real R = iidCodeMeasure.real E := by
    change (iidCodeMeasure R).toReal = (iidCodeMeasure E).toReal
    congr 1
    exact (measurePreserving_codeReversal n).measure_preimage hE.nullMeasurableSet
  have hpE : 1 - δ / 2 ≤ iidCodeMeasure.real E := hprob A hA n hn
  have hpR : 1 - δ / 2 ≤ iidCodeMeasure.real R := by rw [hER]; exact hpE
  have hsum := measureReal_union_add_inter (μ := iidCodeMeasure) (s := E) hR
  have hu : iidCodeMeasure.real (E ∪ R) ≤ 1 := measureReal_le_one
  have hp : 1 - δ ≤ iidCodeMeasure.real (E ∩ R) := by
    linarith only [hsum, hu, hpE, hpR]
  refine hp.trans (measureReal_mono ?_)
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro y hy
  obtain ⟨f, hfL, hfU, hdist⟩ := hreverse n ω
  obtain ⟨z, hz, hd⟩ := hω.2 (f y) (hfL y hy)
  refine ⟨f.symm z, hfU z hz, ?_⟩
  rw [hdist, f.apply_symm_apply]
  exact hd

end DirectedDistances.PaperProofs.Section7
