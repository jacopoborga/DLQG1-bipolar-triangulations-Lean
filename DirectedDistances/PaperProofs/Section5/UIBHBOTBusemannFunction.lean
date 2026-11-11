module

public import DirectedDistances.RandomWalk.UIBHBOTBusemannIncrement
public import DirectedDistances.RandomWalk.UIBHBOTBusemannIncrementSdp

/-! Normalized LDP and SDP Busemann functions on the UIBHBOT incidence carrier. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory Filter Quiver
open DirectedDistances.KMSW DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5

/-- The normalized LDP Busemann candidate, obtained by summing the successive
future-copy increments along the integer boundary. Helper for Proposition 5.11 -/
@[expose] noncomputable def uibhbotBusemannFn (W : ℤ → Fin 3) (k : ℤ) : ℤ :=
  if 0 < k then
    ∑ i ∈ Finset.Ioc 0 k, uibhbotBusemannIncrement i W
  else if k < 0 then
    -∑ i ∈ Finset.Ioc k 0, uibhbotBusemannIncrement i W
  else 0

/-- The normalized SDP Busemann candidate, obtained by summing the successive
future-copy increments along the integer boundary. Helper for Proposition 5.11 -/
@[expose] noncomputable def uibhbotBusemannFnSdp (W : ℤ → Fin 3) (k : ℤ) : ℤ :=
  if 0 < k then
    ∑ i ∈ Finset.Ioc 0 k, uibhbotBusemannIncrementSdp i W
  else if k < 0 then
    -∑ i ∈ Finset.Ioc k 0, uibhbotBusemannIncrementSdp i W
  else 0

/-- The LDP candidate is normalized at the root. Helper for Proposition 5.11 -/
@[simp] theorem uibhbotBusemannFn_zero (W : ℤ → Fin 3) :
    uibhbotBusemannFn W 0 = 0 := by
  simp [uibhbotBusemannFn]

/-- The SDP candidate is normalized at the root. Helper for Proposition 5.11 -/
@[simp] theorem uibhbotBusemannFnSdp_zero (W : ℤ → Fin 3) :
    uibhbotBusemannFnSdp W 0 = 0 := by
  simp [uibhbotBusemannFnSdp]

/-- Successive LDP values differ by the corresponding future-copy increment. -/
theorem uibhbotBusemannFn_sub_prev (W : ℤ → Fin 3) (k : ℤ) :
    uibhbotBusemannFn W k - uibhbotBusemannFn W (k - 1) =
      uibhbotBusemannIncrement k W := by
  by_cases hk : 0 < k
  · by_cases hk1 : k = 1
    · subst k
      have hIoc : Finset.Ioc 0 (1 : ℤ) = {1} := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_singleton]
        omega
      simp [uibhbotBusemannFn, hIoc]
    · have hk' : 0 < k - 1 := by omega
      have hIoc : Finset.Ioc 0 k = insert k (Finset.Ioc 0 (k - 1)) := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnot : k ∉ Finset.Ioc 0 (k - 1) := by
        simp only [Finset.mem_Ioc]
        omega
      simp only [uibhbotBusemannFn, if_pos hk,
        if_neg (show ¬ k < 0 by omega), if_pos hk']
      rw [hIoc, Finset.sum_insert hnot]
      ring
  · by_cases hk0 : k = 0
    · subst k
      have hIoc : Finset.Ioc (-1 : ℤ) 0 = {0} := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_singleton]
        omega
      simp [uibhbotBusemannFn, hIoc]
    · have hk' : k < 0 := by omega
      have hsub : k - 1 = -1 + k := by omega
      rw [hsub]
      have hIoc : Finset.Ioc (-1 + k) 0 = insert k (Finset.Ioc k 0) := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnot : k ∉ Finset.Ioc k 0 := by simp [Finset.mem_Ioc]
      have hprev : -1 + k < 0 := by omega
      simp only [uibhbotBusemannFn,
        if_neg (show ¬ 0 < k by omega), if_pos hk']
      simp only [if_neg (show ¬ 0 < -1 + k by omega), if_pos hprev]
      rw [hIoc, Finset.sum_insert hnot]
      ring

/-- Successive SDP values differ by the corresponding future-copy increment. -/
theorem uibhbotBusemannFnSdp_sub_prev (W : ℤ → Fin 3) (k : ℤ) :
    uibhbotBusemannFnSdp W k - uibhbotBusemannFnSdp W (k - 1) =
      uibhbotBusemannIncrementSdp k W := by
  by_cases hk : 0 < k
  · by_cases hk1 : k = 1
    · subst k
      have hIoc : Finset.Ioc 0 (1 : ℤ) = {1} := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_singleton]
        omega
      simp [uibhbotBusemannFnSdp, hIoc]
    · have hk' : 0 < k - 1 := by omega
      have hIoc : Finset.Ioc 0 k = insert k (Finset.Ioc 0 (k - 1)) := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnot : k ∉ Finset.Ioc 0 (k - 1) := by
        simp only [Finset.mem_Ioc]
        omega
      simp only [uibhbotBusemannFnSdp, if_pos hk,
        if_neg (show ¬ k < 0 by omega), if_pos hk']
      rw [hIoc, Finset.sum_insert hnot]
      ring
  · by_cases hk0 : k = 0
    · subst k
      have hIoc : Finset.Ioc (-1 : ℤ) 0 = {0} := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_singleton]
        omega
      simp [uibhbotBusemannFnSdp, hIoc]
    · have hk' : k < 0 := by omega
      have hsub : k - 1 = -1 + k := by omega
      rw [hsub]
      have hIoc : Finset.Ioc (-1 + k) 0 = insert k (Finset.Ioc k 0) := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnot : k ∉ Finset.Ioc k 0 := by simp [Finset.mem_Ioc]
      have hprev : -1 + k < 0 := by omega
      simp only [uibhbotBusemannFnSdp,
        if_neg (show ¬ 0 < k by omega), if_pos hk']
      simp only [if_neg (show ¬ 0 < -1 + k by omega), if_pos hprev]
      rw [hIoc, Finset.sum_insert hnot]
      ring

/-- The LDP candidate has the stationary increment law of the future-copy code. -/
theorem uibhbotBusemannFn_increment_law (k : ℤ) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun W => uibhbotBusemannFn W k - uibhbotBusemannFn W (k - 1)) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) := by
  rw [show (fun W => uibhbotBusemannFn W k - uibhbotBusemannFn W (k - 1)) =
      uibhbotBusemannIncrement k by
        funext W
        exact uibhbotBusemannFn_sub_prev W k]
  exact uibhbotBusemannIncrement_law k

/-- The LDP candidate's increments are independent. Their common marginal is
`uibhbotBusemannFn_increment_law`. Helper for Proposition 5.11 -/
theorem uibhbotBusemannFn_iIndep :
    iIndepFun (fun k W => uibhbotBusemannFn W k - uibhbotBusemannFn W (k - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) := by
  apply uibhbotBusemannIncrement_iIndep.congr
  intro k
  filter_upwards [] with W
  exact (uibhbotBusemannFn_sub_prev W k).symm

/-- The SDP candidate has the stationary increment law of the future-copy code. -/
theorem uibhbotBusemannFnSdp_increment_law (k : ℤ) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun W => uibhbotBusemannFnSdp W k - uibhbotBusemannFnSdp W (k - 1)) =
      iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) := by
  rw [show (fun W => uibhbotBusemannFnSdp W k - uibhbotBusemannFnSdp W (k - 1)) =
      uibhbotBusemannIncrementSdp k by
        funext W
        exact uibhbotBusemannFnSdp_sub_prev W k]
  exact uibhbotBusemannIncrementSdp_law k

/-- The SDP candidate's increments are independent. Their common marginal is
`uibhbotBusemannFnSdp_increment_law`. Helper for Proposition 5.11 -/
theorem uibhbotBusemannFnSdp_iIndep :
    iIndepFun (fun k W => uibhbotBusemannFnSdp W k - uibhbotBusemannFnSdp W (k - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) := by
  apply uibhbotBusemannIncrementSdp_iIndep.congr
  intro k
  filter_upwards [] with W
  exact (uibhbotBusemannFnSdp_sub_prev W k).symm

/-- Future-copy boundary data for the LDP Busemann characterization. -/
private theorem ae_uibhbotFn_boundary_busemann_data :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∃ hb : PresentPathLengthsBounded
          (w := fun i => uibhbotFutureCode k W (i + 1)),
        ∃ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h)
            (busemannLDPMeasurableVersion (uibhbotFutureCode k W)) := by
  apply ae_all_iff.mpr
  intro k
  have h : ∀ᵐ ω ∂iidCodeMeasure,
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
  rw [← uibhbotFutureCode_law k] at h
  exact ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h

/-- Reachability and boundedness identify a finite extended LDP with its natural value. -/
private theorem uibhbotFn_presentLdp_eq_finiteNat {w : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) :
    presentLdp a b = ((presentLdpFiniteNat hb hr : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  rw [presentLdp_eq_length hp, presentLdpFiniteNat_eq_length hb hr hp]

/-- Telescoping the successive future-copy increments recovers the difference of its
measurable Busemann representative. Helper for Proposition 5.11 -/
private theorem uibhbotBusemannFn_future_difference_of_le
    (W : ℤ → Fin 3) (K k : ℤ) (n : ℕ)
    (hn : k + (n : ℤ) ≤ K)
    (hinc : ∀ i : ℤ, ∀ hi : i ≤ K,
      uibhbotBusemannIncrement i W =
        ldpIncrement busemannLDPMeasurableVersion (i - K) (uibhbotFutureCode K W)) :
    uibhbotBusemannFn W (k + (n : ℤ)) - uibhbotBusemannFn W k =
      busemannLDPMeasurableVersion (uibhbotFutureCode K W) (k + (n : ℤ) - K) -
        busemannLDPMeasurableVersion (uibhbotFutureCode K W) (k - K) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnk : k + (n : ℤ) ≤ K := by omega
      have hnext : k + ((n + 1 : ℕ) : ℤ) ≤ K := hn
      have hindex : k + ((n + 1 : ℕ) : ℤ) - 1 = k + (n : ℤ) := by omega
      have hrec := uibhbotBusemannFn_sub_prev W (k + ((n + 1 : ℕ) : ℤ))
      rw [hindex] at hrec
      have hi : k + ((n + 1 : ℕ) : ℤ) ≤ K := hnext
      rw [hinc _ hi, ldpIncrement] at hrec
      have harg : k + ((n + 1 : ℕ) : ℤ) - K - 1 = k + (n : ℤ) - K := by omega
      rw [harg] at hrec
      calc
        uibhbotBusemannFn W (k + ((n + 1 : ℕ) : ℤ)) - uibhbotBusemannFn W k =
            (uibhbotBusemannFn W (k + ((n + 1 : ℕ) : ℤ)) -
              uibhbotBusemannFn W (k + (n : ℤ))) +
                (uibhbotBusemannFn W (k + (n : ℤ)) - uibhbotBusemannFn W k) := by ring
        _ = (busemannLDPMeasurableVersion (uibhbotFutureCode K W)
              (k + ((n + 1 : ℕ) : ℤ) - K) -
              busemannLDPMeasurableVersion (uibhbotFutureCode K W)
                (k + (n : ℤ) - K)) +
                (busemannLDPMeasurableVersion (uibhbotFutureCode K W)
                  (k + (n : ℤ) - K) -
                  busemannLDPMeasurableVersion (uibhbotFutureCode K W) (k - K)) := by
              rw [hrec, ih hnk]
        _ = busemannLDPMeasurableVersion (uibhbotFutureCode K W)
              (k + ((n + 1 : ℕ) : ℤ) - K) -
              busemannLDPMeasurableVersion (uibhbotFutureCode K W) (k - K) := by ring

/-- For every injective sequence of common reachable present vertices, the normalized LDP
function has the eventual distance-difference characterization in Proposition 5.11.
The finite distances are stated as natural numbers only after reachability is established. -/
theorem ae_uibhbotBusemannFn_distance_characterization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k k' : ℤ,
      ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSource k W) (z m) ∧
        Reachable (uibhbotBusemannSource k' W) (z m)) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
        uibhbotLdp (uibhbotBusemannSource k' W) (z m) =
          ((a : ℕ∞) : WithBot ℕ∞) ∧
        uibhbotLdp (uibhbotBusemannSource k W) (z m) =
          ((b : ℕ∞) : WithBot ℕ∞) ∧
        uibhbotBusemannFn W k' - uibhbotBusemannFn W k = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [ae_uibhbotFn_boundary_busemann_data,
    ae_uibhbotFutureBoundary_index, ae_uibhbotFuture_boundary_ldp,
    ae_uibhbotFuture_boundary_path_lift,
    ae_uibhbotBusemannIncrement_future_identity] with W hdata hi hd hl hinc
  intro k k' z hz hr
  let K := max k k'
  have hk : k ≤ K := le_max_left _ _
  have hk' : k' ≤ K := le_max_right _ _
  obtain ⟨hb, h, hX⟩ := hdata K
  let w := fun i => uibhbotFutureCode K W (i + 1)
  let x := boundaryPresentVertex w h
  let F := uibhbotFutureToGlobal K W
  let j := k - K
  let j' := k' - K
  have hj : j ≤ 0 := by dsimp [j]; omega
  have hj' : j' ≤ 0 := by dsimp [j']; omega
  have hs (i : ℤ) (hi' : i ≤ 0) : F.obj (x i) = uibhbotBusemannSource (K + i) W := by
    apply congrArg UIBHBOTPresentVertex.mk
    exact hi K h i hi'
  have hs0 : F.obj (x j) = uibhbotBusemannSource k W := by
    simpa only [j, add_sub_cancel] using hs j hj
  have hs1 : F.obj (x j') = uibhbotBusemannSource k' W := by
    simpa only [j', add_sub_cancel] using hs j' hj'
  have hp : ∀ m, ∃ c : PresentVertex w, F.obj c = z m ∧ Reachable (x j) c := by
    intro m
    have hrm := (hr m).1
    rw [← hs0] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h j hj (z m) p
    exact ⟨c, hc, ⟨q⟩⟩
  choose y hy hy0 using hp
  have hy1 : ∀ m, Reachable (x j') (y m) := by
    intro m
    have hrm := (hr m).2
    rw [← hs1] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h j' hj' (z m) p
    have he : c = y m := uibhbotFutureToGlobal_obj_injective K W
      (hc.trans (hy m).symm)
    subst c
    exact ⟨q⟩
  have hiy : Function.Injective y := by
    intro a b hab
    apply hz
    rw [← hy a, ← hy b, hab]
  obtain ⟨N, hN⟩ := hX.2 j j' y hiy (fun m => ⟨hy0 m, hy1 m⟩)
  have htel : uibhbotBusemannFn W k' - uibhbotBusemannFn W k =
      busemannLDPMeasurableVersion (uibhbotFutureCode K W) j' -
        busemannLDPMeasurableVersion (uibhbotFutureCode K W) j := by
    by_cases hkk : k ≤ k'
    · have hn : (k' - k).toNat = (k' - k) := Int.toNat_of_nonneg (by omega)
      have hsum := uibhbotBusemannFn_future_difference_of_le W K k
        (k' - k).toNat (by omega) (fun i hi' => hinc K i hi')
      have harg : k + ((k' - k).toNat : ℤ) = k' := by omega
      rw [harg] at hsum
      simpa only [j, j'] using hsum
    · have hn : (k - k').toNat = (k - k') := Int.toNat_of_nonneg (by omega)
      have hsum := uibhbotBusemannFn_future_difference_of_le W K k'
        (k - k').toNat (by omega) (fun i hi' => hinc K i hi')
      have harg : k' + ((k - k').toNat : ℤ) = k := by omega
      rw [harg] at hsum
      have hsum' := congrArg Neg.neg hsum
      calc
        uibhbotBusemannFn W k' - uibhbotBusemannFn W k =
            -(uibhbotBusemannFn W k - uibhbotBusemannFn W k') := by ring
        _ = -(busemannLDPMeasurableVersion (uibhbotFutureCode K W) (k - K) -
              busemannLDPMeasurableVersion (uibhbotFutureCode K W) (k' - K)) := by
            rw [hsum']
        _ = busemannLDPMeasurableVersion (uibhbotFutureCode K W) j' -
              busemannLDPMeasurableVersion (uibhbotFutureCode K W) j := by
            dsimp [j, j']
            ring
  refine ⟨N, fun m hm => ?_⟩
  let a := presentLdpFiniteNat hb (hy1 m)
  let b := presentLdpFiniteNat hb (hy0 m)
  have hd0 : uibhbotLdp (uibhbotBusemannSource k W) (z m) =
      ((b : ℕ∞) : WithBot ℕ∞) := by
    rw [← hs0, ← hy m]
    exact (hd K h j hj (y m)).trans (uibhbotFn_presentLdp_eq_finiteNat hb (hy0 m))
  have hd1 : uibhbotLdp (uibhbotBusemannSource k' W) (z m) =
      ((a : ℕ∞) : WithBot ℕ∞) := by
    rw [← hs1, ← hy m]
    exact (hd K h j' hj' (y m)).trans (uibhbotFn_presentLdp_eq_finiteNat hb (hy1 m))
  refine ⟨a, b, hd1, hd0, ?_⟩
  rw [htel]
  exact hN m hm

/-- The normalized LDP characterization determines the candidate uniquely. For each adjacent
pair of boundary sources, the common-target sequence is supplied by the future-copy distance -/
theorem ae_uibhbotBusemannFn_unique :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ X' : ℤ → ℤ,
      X' 0 = 0 →
      (∀ k k' : ℤ, ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
        (∀ m, Reachable (uibhbotBusemannSource k W) (z m) ∧
          Reachable (uibhbotBusemannSource k' W) (z m)) →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
          uibhbotLdp (uibhbotBusemannSource k' W) (z m) =
            ((a : ℕ∞) : WithBot ℕ∞) ∧
          uibhbotLdp (uibhbotBusemannSource k W) (z m) =
            ((b : ℕ∞) : WithBot ℕ∞) ∧
          X' k' - X' k = (a : ℤ) - (b : ℤ)) →
      X' = uibhbotBusemannFn W := by
  filter_upwards [ae_uibhbotBusemannIncrement_distance_realization] with W hreal
  intro X' hzero hprop
  have hstep (k : ℤ) : X' k - X' (k - 1) = uibhbotBusemannIncrement k W := by
    obtain ⟨hinj, B, hB⟩ := hreal k
    let z := fun m : ℕ => uibhbotBusemannTarget k W (B + m)
    have hr : ∀ m, Reachable (uibhbotBusemannSource (k - 1) W) (z m) ∧
        Reachable (uibhbotBusemannSource k W) (z m) := by
      intro m
      exact ⟨(hB (B + m) (by omega)).2.1, (hB (B + m) (by omega)).1⟩
    obtain ⟨N, hN⟩ := hprop (k - 1) k z (by
      intro a b hab
      have he := hinj hab
      omega) hr
    obtain ⟨a, b, ha, hb, he⟩ := hN N le_rfl
    obtain ⟨c, d, hc, hd, hi⟩ := (hB (B + N) (by omega)).2.2
    have hac : a = c := by exact_mod_cast ha.symm.trans hc
    have hbd : b = d := by exact_mod_cast hb.symm.trans hd
    rw [hac, hbd] at he
    exact he.trans hi.symm
  have hpos : ∀ n : ℕ, X' (n : ℤ) = uibhbotBusemannFn W (n : ℤ) := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        have hs := hstep ((n + 1 : ℕ) : ℤ)
        have hfn := uibhbotBusemannFn_sub_prev W ((n + 1 : ℕ) : ℤ)
        have hidx : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
        rw [hidx] at hs
        rw [hidx] at hfn
        omega
  have hneg : ∀ n : ℕ, X' (-(n : ℤ)) = uibhbotBusemannFn W (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        have hs := hstep (-(n : ℤ))
        have hfn := uibhbotBusemannFn_sub_prev W (-(n : ℤ))
        have hidx : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
        rw [hidx] at hs
        rw [hidx] at hfn
        omega
  funext k
  by_cases hk : 0 ≤ k
  · have hc : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    rw [← hc]
    exact hpos k.toNat
  · have hc : -(((-k).toNat : ℕ) : ℤ) = k := by
      have hn : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      omega
    rw [← hc]
    exact hneg (-k).toNat

/-- The normalized SDP characterization determines the SDP candidate uniquely, using the
future-copy realization for adjacent boundary sources. Helper for Proposition 5.11 -/
theorem ae_uibhbotBusemannFnSdp_unique :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ X' : ℤ → ℤ,
      X' 0 = 0 →
      (∀ k k' : ℤ, ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
        (∀ m, Reachable (uibhbotBusemannSourceSdp k W) (z m) ∧
          Reachable (uibhbotBusemannSourceSdp k' W) (z m)) →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
          DirectedDistances.sdp (uibhbotBusemannSourceSdp k' W) (z m) = (a : ℕ∞) ∧
          DirectedDistances.sdp (uibhbotBusemannSourceSdp k W) (z m) = (b : ℕ∞) ∧
          X' k' - X' k = (a : ℤ) - (b : ℤ)) →
      X' = uibhbotBusemannFnSdp W := by
  filter_upwards [ae_uibhbotBusemannIncrementSdp_distance_realization] with W hreal
  intro X' hzero hprop
  have hstep (k : ℤ) : X' k - X' (k - 1) = uibhbotBusemannIncrementSdp k W := by
    obtain ⟨hinj, B, hB⟩ := hreal k
    let z := fun m : ℕ => uibhbotBusemannTargetSdp k W (B + m)
    have hr : ∀ m, Reachable (uibhbotBusemannSourceSdp (k - 1) W) (z m) ∧
        Reachable (uibhbotBusemannSourceSdp k W) (z m) := by
      intro m
      exact ⟨(hB (B + m) (by omega)).2.1, (hB (B + m) (by omega)).1⟩
    obtain ⟨N, hN⟩ := hprop (k - 1) k z (by
      intro a b hab
      have he := hinj hab
      omega) hr
    obtain ⟨a, b, ha, hb, he⟩ := hN N le_rfl
    obtain ⟨c, d, hc, hd, hi⟩ := (hB (B + N) (by omega)).2.2
    have hac : a = c := by exact_mod_cast ha.symm.trans hc
    have hbd : b = d := by exact_mod_cast hb.symm.trans hd
    rw [hac, hbd] at he
    exact he.trans hi.symm
  have hpos : ∀ n : ℕ, X' (n : ℤ) = uibhbotBusemannFnSdp W (n : ℤ) := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        have hs := hstep ((n + 1 : ℕ) : ℤ)
        have hfn := uibhbotBusemannFnSdp_sub_prev W ((n + 1 : ℕ) : ℤ)
        have hidx : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
        rw [hidx] at hs hfn
        omega
  have hneg : ∀ n : ℕ, X' (-(n : ℤ)) = uibhbotBusemannFnSdp W (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        have hs := hstep (-(n : ℤ))
        have hfn := uibhbotBusemannFnSdp_sub_prev W (-(n : ℤ))
        have hidx : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
        rw [hidx] at hs hfn
        omega
  funext k
  by_cases hk : 0 ≤ k
  · have hc : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    rw [← hc]
    exact hpos k.toNat
  · have hc : -(((-k).toNat : ℕ) : ℤ) = k := by
      have hn : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      omega
    rw [← hc]
    exact hneg (-k).toNat

end DirectedDistances.RandomWalk
