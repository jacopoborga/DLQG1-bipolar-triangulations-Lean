module

public import DirectedDistances.KMSW.RightStationaryGeometry
public import DirectedDistances.Recursive.RightStationaryLaw
public import DirectedDistances.Recursive.MeasurableVersionPos
import DirectedDistances.KMSW.DirectedContainLaw1

/-! Supporting lemmas for paper labels `lem-directed-contain`, `thm-busemann` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk Quiver
open MeasureTheory ProbabilityTheory Filter

private theorem sdp_eq_of_path_lengths {A B : Type*} [Quiver A] [Quiver B]
    (a b : A) (c d : B)
    (heq : {n | ∃ p : Path a b, p.length = n} =
      {n | ∃ p : Path c d, p.length = n}) : sdp a b = sdp c d := by
  apply le_antisymm
  · refine le_iInf fun p => ?_
    obtain ⟨q, hq⟩ := Set.ext_iff.mp heq p.length |>.mpr ⟨p, rfl⟩
    exact (sdp_le_length q).trans_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hq)
  · refine le_iInf fun p => ?_
    obtain ⟨q, hq⟩ := Set.ext_iff.mp heq p.length |>.mp ⟨p, rfl⟩
    exact (sdp_le_length q).trans_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hq)

/-- Helper: SDP and longest-path suprema to every allocated shifted target
agree at both endpoints of a positive right hit (`lem-directed-contain`,
F1/F4 apply to the source identification. -/
theorem rightShift_distances (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (b : PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h (k : ℤ) + i)) b) :
    (sdp (boundaryPresentVertex w h (k : ℤ))
        (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b) =
      sdp (⟨0⟩ : PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b) ∧
    (sdp (boundaryPresentVertex w h ((k + 1 : ℕ) : ℤ))
        (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b) =
      sdp (⟨1⟩ : PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b) ∧
    (ldpSup (boundaryPresentVertex w h (k : ℤ))
        (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b) =
      ldpSup (⟨0⟩ : PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b) ∧
    (ldpSup (boundaryPresentVertex w h ((k + 1 : ℕ) : ℤ))
        (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b) =
      ldpSup (⟨1⟩ : PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b) := by
  obtain ⟨h0, h1⟩ := rightShift_path_lengths w h k hk hs
  have e0 := h0 b hb
  have e1 := h1 b hb
  refine ⟨sdp_eq_of_path_lengths _ _ _ _ e0,
    sdp_eq_of_path_lengths _ _ _ _ e1, ?_, ?_⟩
  · unfold ldpSup
    exact congrArg (fun s : Set ℕ => sSup ((fun n : ℕ => (n : WithBot ℕ)) '' s)) e0
  · unfold ldpSup
    exact congrArg (fun s : Set ℕ => sSup ((fun n : ℕ => (n : WithBot ℕ)) '' s)) e1

private theorem rightShift_common_sequence (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i))) :
    ∃ y : ℕ → PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)),
      Function.Injective y ∧
      (∀ j, kmswVertexAllocated (fun i => w (boundaryHitTime w h (k : ℤ) + i)) (y j)) ∧
      (∀ j, Reachable (boundaryPresentVertex _ hs 0) (y j) ∧
        Reachable (boundaryPresentVertex _ hs 1) (y j)) ∧
      Function.Injective (fun j => shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) (y j)) ∧
      (∀ j, Reachable (boundaryPresentVertex w h (k : ℤ))
          (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) (y j)) ∧
        Reachable (boundaryPresentVertex w h ((k + 1 : ℕ) : ℤ))
          (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) (y j))) := by
  let t := boundaryHitTime w h (k : ℤ)
  let u := fun i => w (t + i)
  let y : ℕ → PresentVertex u := fun j => boundaryPresentVertex u hs ((j : ℤ) + 1)
  have hy : Function.Injective y := by
    intro i j hij
    have he : (i : ℤ) + 1 = (j : ℤ) + 1 := boundaryVertex_injective u hs
      (show boundaryVertex u hs ((i : ℤ) + 1) = boundaryVertex u hs ((j : ℤ) + 1) from
        congrArg PresentVertex.id hij)
    omega
  have ha : ∀ j, kmswVertexAllocated u (y j) := by
    intro j
    simpa only [kmswVertexAllocated, y, boundaryPresentVertex] using
      boundaryVertex_allocated u hs ((j : ℤ) + 1)
  have hr : ∀ j, Reachable (boundaryPresentVertex u hs 0) (y j) ∧
      Reachable (boundaryPresentVertex u hs 1) (y j) := by
    intro j
    exact ⟨boundaryVertex_nonneg_reachable u hs (by omega) (by omega),
      boundaryVertex_nonneg_reachable u hs (by omega) (by omega)⟩
  refine ⟨y, hy, ha, hr, ?_, ?_⟩
  · intro i j hij
    exact hy (shiftLimitVertex_injective w t (ha i) (ha j) hij)
  · intro j
    have he := rightShift_path_lengths w h k hk hs
    have hrj := hr j
    simp only [boundaryPresentVertex, boundaryVertex_zero, boundaryVertex_one] at hrj
    obtain ⟨p⟩ := hrj.1
    obtain ⟨q⟩ := hrj.2
    obtain ⟨p', _⟩ := (Set.ext_iff.mp (he.1 (y j) (ha j)) p.length).mpr ⟨p, rfl⟩
    obtain ⟨q', _⟩ := (Set.ext_iff.mp (he.2 (y j) (ha j)) q.length).mpr ⟨q, rfl⟩
    exact ⟨⟨p'⟩, ⟨q'⟩⟩

/-- Helper: a normalized shifted SDP Busemann function at one equals the
corresponding global increment for `k ≥ 1` (`thm-busemann`,
identity; the F1/F4 source-identification caveats remain. -/
theorem rightShift_sdp_busemann (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannSDP (boundaryPresentVertex _ hs) Xs) :
    Xs 1 = X ((k : ℤ) + 1) - X (k : ℤ) := by
  obtain ⟨y, hy, ha, hr, hiy, hir⟩ := rightShift_common_sequence w h k hk hs
  obtain ⟨N, hN⟩ := hXs.2 0 1 y hy hr
  obtain ⟨M, hM⟩ := hX.2 (k : ℤ) ((k + 1 : ℕ) : ℤ)
    (fun j => shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) (y j)) hiy hir
  have he := rightShift_distances w h k hk hs (y (max N M)) (ha _)
  have hsval := hN (max N M) (Nat.le_max_left _ _)
  have hgval := hM (max N M) (Nat.le_max_right _ _)
  simp only [boundaryPresentVertex, boundaryVertex_zero, boundaryVertex_one,
    hXs.1, sub_zero] at hsval
  rw [he.1, he.2.1] at hgval
  simpa only [Nat.cast_add, Nat.cast_one] using hsval.trans hgval.symm

private theorem ae_comp_rightHit (a : ℤ) {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂iidCodeMeasure, p (codeShift (codeSndFirstHit a ω).toNat ω) := by
  apply ae_of_ae_map
    (measurable_codeShift_toNat _ (measurableSet_codePast_codeSndFirstHit_eq a)).aemeasurable
  rw [map_codeShift_codeSndFirstHit]
  exact hp

private theorem codeShift_future (ω : ℕ → Fin 3) (t : ℕ) :
    (fun i => codeShift t ω (i + 1)) = (fun i => ω ((t + i) + 1)) := by
  funext i
  change (if i + 1 = 0 then 0 else ω (t + (i + 1))) = ω ((t + i) + 1)
  rw [ite_eq_right (by omega : ¬ i + 1 = 0)]
  rfl

/-- Helper: the measurable SDP representative obeys the shifted/global
identity at every positive right hit, almost surely for each `k ≥ 1`.
This supplies the right-side part of `item-busemann-stationary` -/
theorem busemannSDPMeasurableVersion_right_shift_identity :
    ∀ k : ℕ, 1 ≤ k → ∀ᵐ ω ∂iidCodeMeasure,
      busemannSDPMeasurableVersion
          (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 1 =
        busemannSDPMeasurableVersion ω ((k : ℤ) + 1) -
          busemannSDPMeasurableVersion ω (k : ℤ) := by
  intro k hk
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion,
    ae_comp_rightHit (-(k : ℤ)) iidCodes_ae_busemannSDPMeasurableVersion] with ω hdata hsdata
  obtain ⟨h, hX⟩ := hdata
  have ht : (codeSndFirstHit (-(k : ℤ)) ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h (k : ℤ) := by
    rw [codeSndFirstHit_eq_boundaryHitTime ω h (by exact_mod_cast hk), ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [codeShift_future] at hsdata
  obtain ⟨hs, hXs⟩ := hsdata
  exact rightShift_sdp_busemann (fun i => ω (i + 1)) h k hk hs _ _ hX hXs

/-- Right-side marginal stationarity only, for increments indexed by `k ≥ 1`
This helper makes no independence or nonpositive-index claim; F1/F4 remain. -/
theorem busemannSDPMeasurableVersion_right_stationary :
    ∀ k ≥ 1,
      iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k) =
        iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 1) :=
  busemannSDPMeasurableVersion_right_increment_law_of_shift_identity
    busemannSDPMeasurableVersion_right_shift_identity

private theorem ldpFinite_eq_of_path_lengths
    {w u : ℕ → Fin 3}
    (hw : PresentPathLengthsBounded (w := w))
    (hu : PresentPathLengthsBounded (w := u))
    {a b : PresentVertex w} {c d : PresentVertex u}
    (hr : Reachable a b) (hs : Reachable c d)
    (heq : {n | ∃ p : Path a b, p.length = n} =
      {n | ∃ p : Path c d, p.length = n}) :
    presentLdpFiniteNat hw hr = presentLdpFiniteNat hu hs := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hw a b hr) hr
  obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hu c d hs) hs
  rw [presentLdpFiniteNat_eq_length hw hr hp, presentLdpFiniteNat_eq_length hu hs hq]
  obtain ⟨p', hp'⟩ := (Set.ext_iff.mp heq p.length).mp ⟨p, rfl⟩
  obtain ⟨q', hq'⟩ := (Set.ext_iff.mp heq q.length).mpr ⟨q, rfl⟩
  have hpq := hq p'
  have hqp := hp q'
  omega

/-- Helper: normalized shifted and global LDP Busemann functions have the
same positive right-hit increment (`thm-busemann`,
subtraction finite. This code-graph identity retains the F1/F4 caveats. -/
theorem rightShift_ldp_busemann (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded
      (w := fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannLDP hbs (boundaryPresentVertex _ hs) Xs) :
    Xs 1 = X ((k : ℤ) + 1) - X (k : ℤ) := by
  obtain ⟨y, hy, ha, hr, hiy, hir⟩ := rightShift_common_sequence w h k hk hs
  obtain ⟨N, hN⟩ := hXs.2 0 1 y hy hr
  obtain ⟨M, hM⟩ := hX.2 (k : ℤ) ((k + 1 : ℕ) : ℤ)
    (fun j => shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) (y j)) hiy hir
  let j := max N M
  have hsval := hN j (Nat.le_max_left _ _)
  have hgval := hM j (Nat.le_max_right _ _)
  have e0 := (rightShift_path_lengths w h k hk hs).1 (y j) (ha j)
  have e1 := (rightShift_path_lengths w h k hk hs).2 (y j) (ha j)
  have hr0 := (hr j).1
  have hr1 := (hr j).2
  simp only [boundaryPresentVertex, boundaryVertex_zero, boundaryVertex_one] at hr0 hr1
  have d0 := ldpFinite_eq_of_path_lengths hb hbs (hir j).1 hr0 e0
  have d1 := ldpFinite_eq_of_path_lengths hb hbs (hir j).2 hr1 e1
  simp only [boundaryPresentVertex, boundaryVertex_zero, boundaryVertex_one,
    hXs.1, sub_zero] at hsval
  rw [d0, d1] at hgval
  simpa only [Nat.cast_add, Nat.cast_one] using hsval.trans hgval.symm

private theorem ae_ldp_measurable_data :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)),
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion ω) := by
  filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_eq,
    iidCodes_ae_existsUnique_eq_canonicalBusemannLDP] with ω heq hdata
  obtain ⟨hfin, h, X, hX, -, hcanon⟩ := hdata
  refine ⟨presentPathLengthsBounded_of_hfin _ hfin, h, ?_⟩
  rw [heq, ← hcanon]
  exact hX

/-- Helper: the measurable LDP representative obeys the shifted/global
identity at every positive right hit, almost surely for each `k ≥ 1`.
This supplies the right-side part of `item-busemann-stationary` -/
theorem busemannLDPMeasurableVersion_right_shift_identity :
    ∀ k : ℕ, 1 ≤ k → ∀ᵐ ω ∂iidCodeMeasure,
      busemannLDPMeasurableVersion
          (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 1 =
        busemannLDPMeasurableVersion ω ((k : ℤ) + 1) -
          busemannLDPMeasurableVersion ω (k : ℤ) := by
  intro k hk
  filter_upwards [ae_ldp_measurable_data,
    ae_comp_rightHit (-(k : ℤ)) ae_ldp_measurable_data] with ω hdata hsdata
  obtain ⟨hb, h, hX⟩ := hdata
  have ht : (codeSndFirstHit (-(k : ℤ)) ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h (k : ℤ) := by
    rw [codeSndFirstHit_eq_boundaryHitTime ω h (by exact_mod_cast hk), ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [codeShift_future] at hsdata
  obtain ⟨hbs, hs, hXs⟩ := hsdata
  exact rightShift_ldp_busemann (fun i => ω (i + 1)) h k hk hs hb hbs _ _ hX hXs

/-- Right-side marginal stationarity only, for increments indexed by `k ≥ 1`
This helper makes no independence or nonpositive-index claim; F1/F4 remain. -/
theorem busemannLDPMeasurableVersion_right_stationary :
    ∀ k ≥ 1, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 1) :=
  busemannLDPMeasurableVersion_right_increment_law_of_shift_identity
    busemannLDPMeasurableVersion_right_shift_identity

end DirectedDistances.Recursive
