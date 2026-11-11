module

public import DirectedDistances.PaperProofs.SourceResults.CellLDPLower
public import DirectedDistances.PaperProofs.SourceResults.CellLDPUpper
public import DirectedDistances.PaperProofs.SourceResults.CellSDPLower
public import DirectedDistances.PaperProofs.SourceResults.CellSDPUpper
public import DirectedDistances.KMSW.KMSWMeasurability

/-! Supporting lemmas for paper labels `thm-cell-ldp`, `thm-cell-sdp` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Quiver Filter
open Topology
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.SourceResults




private theorem cell_stage_pathLengths_congr {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) (a b : ℕ) :
    pathLengths (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      pathLengths (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
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
  ext k
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(F.mapPath p), hF p⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(G.mapPath p), hG p⟩




private theorem cell_stage_ldpSup_congr {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) (a b : ℕ) :
    ldpSup (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      ldpSup (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
  unfold ldpSup
  rw [cell_stage_pathLengths_congr h a b]




private theorem cell_stage_sdp_congr {w w' : ℕ → Fin 3} {n : ℕ}
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




private theorem measurable_cell_ldp_upper (n : ℕ) (A : ℝ) :
    MeasurableSet {ω : ℕ → Fin 3 |
      ∀ x y : StagePresentVertex (fun i => ω (i + 1)) n,
        x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
        y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
        ldpSup x y ≤ ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)} := by
  refine measurableSet_of_factors_prefix (n + 1) _ ?_
  intro ω ω' h
  have hs := kmswStage_shift_congr (n := n)
    (fun i _ hi => h i (by omega : i < n + 1))
  constructor
  · intro hu x y hx hy
    cases x with
    | mk x =>
      cases y with
      | mk y =>
        rw [← cell_stage_ldpSup_congr hs x y]
        exact hu ⟨x⟩ ⟨y⟩ (by simpa only [← hs] using hx)
          (by simpa only [← hs] using hy)
  · intro hu x y hx hy
    cases x with
    | mk x =>
      cases y with
      | mk y =>
        rw [← cell_stage_ldpSup_congr hs.symm x y]
        exact hu ⟨x⟩ ⟨y⟩ (by simpa only [hs] using hx)
          (by simpa only [hs] using hy)




private theorem measurable_cell_sdp_upper (n : ℕ) (A : ℝ) :
    MeasurableSet {ω : ℕ → Fin 3 |
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
  refine measurableSet_of_factors_prefix (n + 1) _ ?_
  intro ω ω' h
  have hs := kmswStage_shift_congr (n := n)
    (fun i _ hi => h i (by omega : i < n + 1))
  dsimp only
  simp_rw [cell_stage_sdp_congr hs]
  rw [hs]





private theorem cell_inter_probability_lower (E F : Set (ℕ → Fin 3))
    (hF : MeasurableSet F) (p q : ℝ)
    (hp : p ≤ iidCodeMeasure.real E) (hq : q ≤ iidCodeMeasure.real F) :
    p + q - 1 ≤ iidCodeMeasure.real (E ∩ F) := by
  have hsum := measureReal_inter_add_sdiff (μ := iidCodeMeasure)
    (s := E) (t := F) hF
  have hsub : iidCodeMeasure.real (E \ F) ≤ iidCodeMeasure.real Fᶜ :=
    measureReal_mono (Set.sdiff_subset_compl _ _)
  have hcompl := measureReal_compl (μ := iidCodeMeasure) hF
  rw [probReal_univ] at hcompl
  linarith




theorem thm_cell_ldp_code (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
      1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
        (∃ a b : StagePresentVertex (fun i => ω (i + 1)) n, ∃ q : Path a b,
          A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)) ∧
        (∀ x y : StagePresentVertex (fun i => ω (i + 1)) n,
          x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
          y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
          ldpSup x y ≤ ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ))} := by
  have hδ2 : 0 < δ / 2 := by linarith only [hδ, hδ1]
  have hε : 0 < (1 / 3 : ℝ) := by norm_num
  have hεlt : (1 / 3 : ℝ) < 2 / 3 := by norm_num
  obtain ⟨C, c₂, c₃, hc₂, hc₃, hlower⟩ := cell_ldp_lower (1 / 3) hε
  obtain ⟨C', hC', hupper⟩ := cell_ldp_upper (1 / 3) hε hεlt
  have hdecay : Tendsto (fun A : ℝ => (|C| + c₂ + C') * A ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul
        (|C| + c₂ + C')
  have hexp := (isLittleO_exp_neg_mul_rpow_atTop hc₃ (-1)).comp_tendsto
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have hexpBound := hexp.bound (by norm_num : (0 : ℝ) < 1)
  have hsmall : ∀ᶠ A : ℝ in atTop,
      (|C| + c₂ + C') * A ^ (-(1 / 3 : ℝ)) < δ / 2 :=
    hdecay.eventually (Iio_mem_nhds hδ2)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hsmall.and hexpBound)
  let A := max (max T 2) 1
  have hA2 : 2 ≤ A := (le_max_right T 2).trans (le_max_left (max T 2) 1)
  have hA : 1 < A := by dsimp [A]; exact lt_of_lt_of_le (by norm_num) hA2
  have hApos : 0 < A := by linarith
  have hAhi : T ≤ A := (le_max_left T 2).trans (le_max_left (max T 2) 1)
  have hpow : 0 ≤ A ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hApos.le _
  have hTA := hT A hAhi
  have hdecayA := hTA.1
  have hexpA := hTA.2
  have hexpA' : Real.exp (-(c₃ * A ^ (1 / 3 : ℝ))) ≤ A ^ (-(1 / 3 : ℝ)) := by
    have hAeq : (A ^ (1 / 3 : ℝ)) ^ (-1 : ℝ) = A ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_mul hApos.le]
      congr 1
      ring
    simpa only [Function.comp_apply, hAeq, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg hpow, one_mul, neg_mul] using hexpA
  have htotal : (|C| + c₂ + C') * A ^ (-(1 / 3 : ℝ)) < δ / 2 := hdecayA
  refine ⟨A, hA, ?_⟩
  intro n hn
  let E : Set (ℕ → Fin 3) := {ω | ∃ a b : StagePresentVertex
      (fun i => ω (i + 1)) n, ∃ q : Path a b,
        A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)}
  let F : Set (ℕ → Fin 3) := {ω | ∀ x y : StagePresentVertex
      (fun i => ω (i + 1)) n,
      x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
      y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
      ldpSup x y ≤ ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)}
  have hE : 1 - (C * A ^ (-(1 / 3 : ℝ)) +
      c₂ * Real.exp (-(c₃ * A ^ (1 / 3 : ℝ)))) ≤ iidCodeMeasure.real E := by
    simpa only [E, show -(2 / 3 : ℝ) + (1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring] using
      hlower n hn A hA
  have hF : 1 - C' * A ^ (-(1 / 3 : ℝ)) ≤ iidCodeMeasure.real F := by
    simpa only [F, show -(2 / 3 : ℝ) + (1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring] using
      hupper n hn A hA
  have hmeasF : MeasurableSet F := by
    simpa only [F] using measurable_cell_ldp_upper n A
  have hjoin := cell_inter_probability_lower E F hmeasF
    (1 - (C * A ^ (-(1 / 3 : ℝ)) + c₂ *
      Real.exp (-(c₃ * A ^ (1 / 3 : ℝ)))))
    (1 - C' * A ^ (-(1 / 3 : ℝ))) hE hF
  have hbound : C * A ^ (-(1 / 3 : ℝ)) +
      c₂ * Real.exp (-(c₃ * A ^ (1 / 3 : ℝ))) +
      C' * A ^ (-(1 / 3 : ℝ)) ≤ δ := by
    have hC : C ≤ |C| := le_abs_self C
    have hc : 0 ≤ A ^ (-(1 / 3 : ℝ)) := hpow
    have hmain : C * A ^ (-(1 / 3 : ℝ)) ≤
        |C| * A ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hC hc
    have hexpc : c₂ * Real.exp (-(c₃ * A ^ (1 / 3 : ℝ))) ≤
        c₂ * A ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hexpA' hc₂.le
    have hpowtotal : (|C| + c₂ + C') * A ^ (-(1 / 3 : ℝ)) < δ / 2 := htotal
    nlinarith
  change 1 - δ ≤ iidCodeMeasure.real (E ∩ F)
  linarith only [hjoin, hbound]




theorem thm_cell_sdp_code (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
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
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
        (∃ h : BoundaryHitWitnesses w, ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage w n).LR,
            (kmswStage w n).west e = boundaryVertex w h (r : ℤ) ∨
              (kmswStage w n).east e = boundaryVertex w h (r : ℤ)) ∧
          A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
            ((sdp (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
              ⟨boundaryVertex w h (r : ℤ)⟩).toNat : ℝ))} := by
  have hδ2 : 0 < δ / 2 := by linarith only [hδ, hδ1]
  obtain ⟨A₆, hA₆, h6⟩ := cell_sdp_lower (δ / 2) hδ2
  obtain ⟨A₀, hA₀, h8⟩ := cell_sdp_upper (δ / 2) hδ2
  let A := max A₀ A₆
  have hA0 : A₀ ≤ A := le_max_left _ _
  have hA6 : A₆ ≤ A := le_max_right _ _
  have hA : 1 < A := lt_of_lt_of_le hA₀ hA0
  have hApos : 0 < A₆ := by linarith
  refine ⟨A, hA, ?_⟩
  intro n hn
  let E : Set (ℕ → Fin 3) := {ω | ∃ h : BoundaryHitWitnesses
      (fun i => ω (i + 1)), ∃ r : ℕ, 1 ≤ r ∧
      (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
        (kmswStage (fun i => ω (i + 1)) n).west e =
            boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
          (kmswStage (fun i => ω (i + 1)) n).east e =
            boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)) ∧
      A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
        ((sdp (⟨boundaryVertex (fun i => ω (i + 1)) h 0⟩ :
          StagePresentVertex (fun i => ω (i + 1)) n)
          ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ)}
  let F : Set (ℕ → Fin 3) := {ω : ℕ → Fin 3 |
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
            (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞))}
  have hE : 1 - δ / 2 ≤ iidCodeMeasure.real E := by
    have hInv : A⁻¹ ≤ A₆⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hApos hA6
    have hpowN : 0 ≤ (n : ℝ) ^ (3 / 8 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hincl : {ω : ℕ → Fin 3 | ∃ h : BoundaryHitWitnesses
        (fun i => ω (i + 1)), ∃ r : ℕ, 1 ≤ r ∧
        (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LR,
          (kmswStage (fun i => ω (i + 1)) n).west e =
              boundaryVertex (fun i => ω (i + 1)) h (r : ℤ) ∨
            (kmswStage (fun i => ω (i + 1)) n).east e =
              boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)) ∧
        A₆⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
          ((sdp (⟨boundaryVertex (fun i => ω (i + 1)) h 0⟩ :
            StagePresentVertex (fun i => ω (i + 1)) n)
            ⟨boundaryVertex (fun i => ω (i + 1)) h (r : ℤ)⟩).toNat : ℝ)} ⊆ E := by
      intro ω hω
      obtain ⟨h, r, hr, he, hd⟩ := hω
      refine ⟨h, r, hr, he, ?_⟩
      exact (mul_le_mul_of_nonneg_right hInv hpowN).trans hd
    have hp := h6 n hn
    exact hp.trans (measureReal_mono (μ := iidCodeMeasure) hincl (measure_ne_top _ _))
  have hF : 1 - δ / 2 ≤ iidCodeMeasure.real F := by
    simpa only [F] using h8 A hA0 n hn
  have hmeasF : MeasurableSet F := by
    simpa only [F] using measurable_cell_sdp_upper n A
  have hjoin := cell_inter_probability_lower E F hmeasF
    (1 - δ / 2) (1 - δ / 2) hE hF
  have hbound : 1 - δ ≤ iidCodeMeasure.real (E ∩ F) := by
    linarith only [hjoin]
  apply hbound.trans
  refine measureReal_mono (μ := iidCodeMeasure) ?_ (measure_ne_top _ _)
  intro ω hω
  exact ⟨hω.2.1, hω.2.2, hω.1⟩

end DirectedDistances.PaperProofs.Section7
