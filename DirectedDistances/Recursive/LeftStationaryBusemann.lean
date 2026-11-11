module

public import DirectedDistances.KMSW.LeftStationaryGeometry
public import DirectedDistances.Recursive.ShiftProcessLaw
public import DirectedDistances.Recursive.RightStationaryBusemann
import DirectedDistances.KMSW.DirectedContainLaw1
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.Recursive.OneStepTransport

/-! # Left-shift Busemann identities

Helpers for `item-busemann-stationary` at `k ≤ 0`
Common far vertices are chosen deterministically from a right-boundary tail.
The code-graph source-identification obligations F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk Quiver
open MeasureTheory ProbabilityTheory Filter

private theorem sdp_eq_of_path_lengths_Left {A B : Type*} [Quiver A] [Quiver B]
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

/-- Helper: SDP and longest-path suprema from every nonpositive shifted
boundary source agree with their global counterparts (`lem-directed-contain`,
the source-identification caveats F1/F4 remain. -/
theorem leftShift_distances (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    {j : ℤ} (hj : j ≤ 0)
    (b : PresentVertex (fun i => w (boundaryHitTime w h k + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h k + i)) b) :
    (sdp (boundaryPresentVertex w h (k + j))
        (shiftLimitVertex w (boundaryHitTime w h k) b) =
      sdp (boundaryPresentVertex _ hs j) b) ∧
    (ldpSup (boundaryPresentVertex w h (k + j))
        (shiftLimitVertex w (boundaryHitTime w h k) b) =
      ldpSup (boundaryPresentVertex _ hs j) b) := by
  have he := leftShift_path_lengths w h hk hs hj b hb
  refine ⟨sdp_eq_of_path_lengths_Left _ _ _ _ he, ?_⟩
  unfold ldpSup
  exact congrArg (fun s : Set ℕ => sSup ((fun n : ℕ => (n : WithBot ℕ)) '' s)) he

private theorem allocated_reaches_right_tail_Left (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : PresentVertex w)
    (hv : kmswVertexAllocated w v) :
    ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable v (boundaryPresentVertex w h l) := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨q, hqrec, hnq⟩ :=
    (right_record_infinite w h.R_unbounded_below).exists_gt n
  have hqpos : 0 < q := by omega
  have hrec : ∀ i < q, R w q < R w i := hqrec
  have hneg : R w q < 0 := by
    have hh := hrec 0 hqpos
    simpa only [R, Finset.sum_range_zero] using hh
  let b : ℤ := -R w q
  have hb : 1 ≤ b := by dsimp [b]; omega
  have htime : boundaryHitTime w h b = q := by
    have hle : boundaryHitTime w h b ≤ q := by
      rw [boundaryHitTime_right_eq_find w h hb]
      exact Nat.find_min' (h.rightHit b hb) (by dsimp [b]; omega)
    have hge : q ≤ boundaryHitTime w h b := by
      by_contra hnot
      have hh := hrec (boundaryHitTime w h b) (by omega)
      have hh' := boundaryHitTime_right_spec w h hb
      rw [hh'] at hh
      have hRb : R w q = -b := by dsimp [b]; omega
      omega
    omega
  have heq : recordVertex w q = boundaryPresentVertex w h b := by
    apply congrArg PresentVertex.mk
    have he := edge_endpoints_eq w (act_lt_nextEdge w (le_refl q))
    rw [boundaryVertex_eq_edgeWest_hit w h b, htime]
    exact he.1
  have hvq : v.id < (kmswStage w (q - 1)).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono w (by omega : n ≤ q - 1))
  have hr : Reachable v (boundaryPresentVertex w h b) := by
    have hh := allocated_vertex_reaches_strict_record w q
      (fun i hi => by have := hrec i hi; omega) hqpos v.id hvq
    have hvid : (⟨v.id⟩ : PresentVertex w) = v := by cases v; rfl
    rw [hvid, heq] at hh
    exact hh
  refine ⟨b.toNat, fun l hl => hr.trans ?_⟩
  exact boundaryVertex_nonneg_reachable w h (by omega) (by omega)

private theorem leftShift_common_sequence (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    {j : ℤ} (hj : j ≤ 0) :
    ∃ y : ℕ → PresentVertex (fun i => w (boundaryHitTime w h k + i)),
      Function.Injective y ∧
      (∀ m, kmswVertexAllocated (fun i => w (boundaryHitTime w h k + i)) (y m)) ∧
      (∀ m, Reachable (boundaryPresentVertex _ hs 0) (y m) ∧
        Reachable (boundaryPresentVertex _ hs j) (y m)) ∧
      Function.Injective (fun m => shiftLimitVertex w (boundaryHitTime w h k) (y m)) ∧
      (∀ m, Reachable (boundaryPresentVertex w h k)
          (shiftLimitVertex w (boundaryHitTime w h k) (y m)) ∧
        Reachable (boundaryPresentVertex w h (k + j))
          (shiftLimitVertex w (boundaryHitTime w h k) (y m))) := by
  let t := boundaryHitTime w h k
  let u := fun i => w (t + i)
  obtain ⟨B0, hB0⟩ := allocated_reaches_right_tail_Left u hs
    (boundaryPresentVertex u hs 0) (boundaryVertex_left_allocated u hs (by omega))
  obtain ⟨Bj, hBj⟩ := allocated_reaches_right_tail_Left u hs
    (boundaryPresentVertex u hs j) (boundaryVertex_left_allocated u hs hj)
  let y : ℕ → PresentVertex u := fun m =>
    boundaryPresentVertex u hs ((B0 + Bj + m : ℕ) : ℤ)
  have hy : Function.Injective y := by
    intro a b hab
    have he := boundaryVertex_injective u hs (congrArg PresentVertex.id hab)
    change ((B0 + Bj + a : ℕ) : ℤ) = ((B0 + Bj + b : ℕ) : ℤ) at he
    omega
  have ha : ∀ m, kmswVertexAllocated u (y m) := by
    intro m
    exact boundaryVertex_allocated u hs _
  have hr : ∀ m, Reachable (boundaryPresentVertex u hs 0) (y m) ∧
      Reachable (boundaryPresentVertex u hs j) (y m) := by
    intro m
    exact ⟨hB0 _ (by omega), hBj _ (by omega)⟩
  refine ⟨y, hy, ha, hr, ?_, ?_⟩
  · intro a b hab
    exact hy (shiftLimitVertex_injective w t (ha a) (ha b) hab)
  · intro m
    have h0 := (leftShift_reachable_iff w h hk hs (by omega : (0 : ℤ) ≤ 0)
      (y m) (ha m)).mpr (hr m).1
    rw [add_zero] at h0
    exact ⟨h0, (leftShift_reachable_iff w h hk hs hj (y m) (ha m)).mpr (hr m).2⟩

/-- Helper: normalized shifted SDP Busemann values at every `j ≤ 0`
equal the global differences at a negative left hit (`thm-busemann`, -/
theorem leftShift_sdp_busemann (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannSDP (boundaryPresentVertex _ hs) Xs) :
    ∀ j : ℤ, j ≤ 0 → Xs j = X (k + j) - X k := by
  intro j hj
  obtain ⟨y, hy, ha, hr, hiy, hir⟩ := leftShift_common_sequence w h hk hs hj
  obtain ⟨N, hN⟩ := hXs.2 0 j y hy hr
  obtain ⟨M, hM⟩ := hX.2 k (k + j)
    (fun m => shiftLimitVertex w (boundaryHitTime w h k) (y m)) hiy hir
  have he0 := (leftShift_distances w h hk hs (by omega : (0 : ℤ) ≤ 0)
    (y (max N M)) (ha _)).1
  have hej := (leftShift_distances w h hk hs hj (y (max N M)) (ha _)).1
  have hsval := hN (max N M) (Nat.le_max_left _ _)
  have hgval := hM (max N M) (Nat.le_max_right _ _)
  rw [add_zero] at he0
  rw [he0, hej] at hgval
  rw [hXs.1, sub_zero] at hsval
  exact hsval.trans hgval.symm

private theorem ldpFinite_eq_of_path_lengths_Left
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

/-- Helper: normalized shifted LDP Busemann values at every `j ≤ 0`
equal the global differences at a negative left hit (`thm-busemann`,
subtraction finite; F1/F4 remain. -/
theorem leftShift_ldp_busemann (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded (w := fun i => w (boundaryHitTime w h k + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannLDP hbs (boundaryPresentVertex _ hs) Xs) :
    ∀ j : ℤ, j ≤ 0 → Xs j = X (k + j) - X k := by
  intro j hj
  obtain ⟨y, hy, ha, hr, hiy, hir⟩ := leftShift_common_sequence w h hk hs hj
  obtain ⟨N, hN⟩ := hXs.2 0 j y hy hr
  obtain ⟨M, hM⟩ := hX.2 k (k + j)
    (fun m => shiftLimitVertex w (boundaryHitTime w h k) (y m)) hiy hir
  let m := max N M
  have hsval := hN m (Nat.le_max_left _ _)
  have hgval := hM m (Nat.le_max_right _ _)
  have e0 := leftShift_path_lengths w h hk hs (by omega : (0 : ℤ) ≤ 0) (y m) (ha m)
  have ej := leftShift_path_lengths w h hk hs hj (y m) (ha m)
  rw [add_zero] at e0
  have d0 := ldpFinite_eq_of_path_lengths_Left hb hbs (hir m).1 (hr m).1 e0
  have dj := ldpFinite_eq_of_path_lengths_Left hb hbs (hir m).2 (hr m).2 ej
  rw [hXs.1, sub_zero] at hsval
  rw [d0, dj] at hgval
  exact hsval.trans hgval.symm

private theorem ae_comp_leftHit (a : ℤ) {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂iidCodeMeasure, p (codeShift (codeFstFirstHit a ω).toNat ω) := by
  apply ae_of_ae_map
    (measurable_codeShift_toNat _ (measurableSet_codePast_codeFstFirstHit_eq a)).aemeasurable
  rw [map_codeShift_codeFstFirstHit]
  exact hp

private theorem codeShift_future_Left (ω : ℕ → Fin 3) (t : ℕ) :
    (fun i => codeShift t ω (i + 1)) = (fun i => ω ((t + i) + 1)) := by
  funext i
  change (if i + 1 = 0 then 0 else ω (t + (i + 1))) = ω ((t + i) + 1)
  rw [ite_eq_right (by omega : ¬ i + 1 = 0)]
  rfl

private theorem ae_ldp_measurable_data_Left :
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

/-- Helper for `item-busemann-stationary` at `k ≤ 0`
shifted index, the measurable SDP representative equals the global difference.
The route uses strong Markov at left hits and `lem-directed-contain` -/
theorem busemannSDPMeasurableVersion_left_shift_identity :
    ∀ k : ℤ, k ≤ -1 → ∀ᵐ ω ∂iidCodeMeasure, ∀ j : ℕ,
      busemannSDPMeasurableVersion
          (codeShift (codeFstFirstHit k ω).toNat ω) (-(j : ℤ)) =
        busemannSDPMeasurableVersion ω (k - j) -
          busemannSDPMeasurableVersion ω k := by
  intro k hk
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion,
    ae_comp_leftHit k iidCodes_ae_busemannSDPMeasurableVersion] with ω hdata hsdata
  obtain ⟨h, hX⟩ := hdata
  have ht : (codeFstFirstHit k ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h k := by
    rw [codeFstFirstHit_eq_boundaryHitTime ω h hk, ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [codeShift_future_Left] at hsdata
  obtain ⟨hs, hXs⟩ := hsdata
  intro j
  simpa only [sub_eq_add_neg] using
    leftShift_sdp_busemann (fun i => ω (i + 1)) h hk hs _ _ hX hXs
      (-(j : ℤ)) (by omega)

/-- Helper for `item-busemann-stationary` at `k ≤ 0`
shifted index, the measurable LDP representative equals the global difference.
The route uses strong Markov at left hits and `lem-directed-contain` -/
theorem busemannLDPMeasurableVersion_left_shift_identity :
    ∀ k : ℤ, k ≤ -1 → ∀ᵐ ω ∂iidCodeMeasure, ∀ j : ℕ,
      busemannLDPMeasurableVersion
          (codeShift (codeFstFirstHit k ω).toNat ω) (-(j : ℤ)) =
        busemannLDPMeasurableVersion ω (k - j) -
          busemannLDPMeasurableVersion ω k := by
  intro k hk
  filter_upwards [ae_ldp_measurable_data_Left,
    ae_comp_leftHit k ae_ldp_measurable_data_Left] with ω hdata hsdata
  obtain ⟨hb, h, hX⟩ := hdata
  have ht : (codeFstFirstHit k ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h k := by
    rw [codeFstFirstHit_eq_boundaryHitTime ω h hk, ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [codeShift_future_Left] at hsdata
  obtain ⟨hbs, hs, hXs⟩ := hsdata
  intro j
  simpa only [sub_eq_add_neg] using
    leftShift_ldp_busemann (fun i => ω (i + 1)) h hk hs hb hbs _ _ hX hXs
      (-(j : ℤ)) (by omega)

/-- Left-side marginal stationarity for the measurable LDP representative,
for every `k ≤ 0` (`item-busemann-stationary`,
shift identity. This helper retains the F1/F4 source caveats. -/
theorem busemannLDPMeasurableVersion_left_stationary :
    ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) := by
  apply busemannLDPMeasurableVersion_left_increment_law_of_shift_identity
  intro k hk
  filter_upwards [busemannLDPMeasurableVersion_left_shift_identity k hk] with ω hω
  simpa only [Nat.cast_one] using hω 1

/-- Left-side marginal stationarity for the measurable SDP representative,
for every `k ≤ 0` (`item-busemann-stationary`,
shift identity. This helper retains the F1/F4 source caveats. -/
theorem busemannSDPMeasurableVersion_left_stationary :
    ∀ k ≤ 0,
      iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k) =
        iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) := by
  apply busemannSDPMeasurableVersion_left_increment_law_of_shift_identity
  intro k hk
  filter_upwards [busemannSDPMeasurableVersion_left_shift_identity k hk] with ω hω
  simpa only [Nat.cast_one] using hω 1

/-- Left process law for the measurable LDP representative, from the
simultaneous left-hit identity (`item-busemann-stationary`, -/
theorem busemannLDPMeasurableVersion_left_process_law :
    ∀ k : ℤ, k ≤ -1 →
      iidCodeMeasure.map (fun ω (j : ℕ) =>
        busemannLDPMeasurableVersion ω (k - j) - busemannLDPMeasurableVersion ω k) =
      iidCodeMeasure.map (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ))) :=
  left_process_law_of_shift_identity measurable_busemannLDPMeasurableVersion
    busemannLDPMeasurableVersion_zero busemannLDPMeasurableVersion_left_shift_identity

/-- Left process law for the measurable SDP representative, from the
simultaneous left-hit identity (`item-busemann-stationary`, -/
theorem busemannSDPMeasurableVersion_left_process_law :
    ∀ k : ℤ, k ≤ -1 →
      iidCodeMeasure.map (fun ω (j : ℕ) =>
        busemannSDPMeasurableVersion ω (k - j) - busemannSDPMeasurableVersion ω k) =
      iidCodeMeasure.map (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ))) :=
  left_process_law_of_shift_identity measurable_busemannSDPMeasurableVersion
    busemannSDPMeasurableVersion_zero busemannSDPMeasurableVersion_left_shift_identity

end DirectedDistances.Recursive
