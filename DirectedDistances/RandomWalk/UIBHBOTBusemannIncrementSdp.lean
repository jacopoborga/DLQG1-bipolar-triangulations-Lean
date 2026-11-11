module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmap
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.Recursive.SDPMasterFromLaw
import DirectedDistances.Recursive.HLRSdpFinal
import DirectedDistances.Recursive.OneStepTransport

/-! SDP Busemann increments on the UIBHBOT future-code carrier. The source is -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory Filter Quiver
open DirectedDistances.KMSW DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The copy rooted at `x_k` aligns the two source indices with `0` and `-1`. -/
@[expose] noncomputable def uibhbotBusemannIncrementSdp
    (k : ℤ) (W : ℤ → Fin 3) : ℤ :=
  SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 (uibhbotFutureCode k W)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Measurability of the actual future-code representative. -/
theorem measurable_uibhbotBusemannIncrementSdp (k : ℤ) :
    Measurable (uibhbotBusemannIncrementSdp k) := by
  exact ((measurable_busemannSDPMeasurableVersion 0).sub
    (measurable_busemannSDPMeasurableVersion (0 - 1))).comp
      (measurable_uibhbotFutureCode k)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The marginal identity holds at every integer boundary index. -/
theorem uibhbotBusemannIncrementSdp_law (k : ℤ) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (uibhbotBusemannIncrementSdp k) =
      iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) := by
  exact uibhbotFutureCode_map k
    ((measurable_busemannSDPMeasurableVersion 0).sub
      (measurable_busemannSDPMeasurableVersion (0 - 1)))

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The boundary source `x_k` in the existing incidence carrier. -/
@[expose] noncomputable def uibhbotBusemannSourceSdp
    (k : ℤ) (W : ℤ → Fin 3) : UIBHBOTPresentVertex W :=
  ⟨uibhbotFutureVertex k W 0⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Image of the future copy's nonnegative boundary vertex. -/
@[expose] noncomputable def uibhbotBusemannTargetSdp
    (k : ℤ) (W : ℤ → Fin 3) (m : ℕ) : UIBHBOTPresentVertex W :=
  (uibhbotFutureToGlobal k W).obj
    ⟨busemannBoundaryIdTotal (uibhbotFutureCode k W) (m : ℤ)⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Identification of the total boundary ID on the hit-witness event. -/
private theorem incrementSdp_boundaryId_eq (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (j : ℤ) :
    busemannBoundaryIdTotal ω j = boundaryVertex (fun i => ω (i + 1)) h j := by
  unfold busemannBoundaryIdTotal
  rw [boundaryHitTimeTotal_eq_boundaryHitTime ω h j, ENat.toNat_natCast]
  rw [boundaryVertex_eq_edgeWest_hit]
  exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The measurable representative retains the full SDP Busemann characterization. -/
private theorem ae_incrementSdp_busemann_data :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        IsBoundaryBusemannSDP (boundaryPresentVertex _ h)
          (busemannSDPMeasurableVersion ω) := by
  exact iidCodes_ae_busemannSDPMeasurableVersion

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
All future copies simultaneously inherit the characterization. -/
private theorem ae_uibhbot_incrementSdp_busemann_data :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∃ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        IsBoundaryBusemannSDP (boundaryPresentVertex _ h)
          (busemannSDPMeasurableVersion (uibhbotFutureCode k W)) := by
  apply ae_all_iff.mpr
  intro k
  have h := ae_incrementSdp_busemann_data
  rw [← uibhbotFutureCode_law k] at h
  exact ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Every allocated vertex reaches a tail of the future right boundary. -/
private theorem incrementSdp_reaches_boundary_tail (w : ℕ → Fin 3)
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

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Path-length set equality identifies the shortest distances in the two carriers. -/
private theorem incrementSdp_eq_of_pathLengths
    {α β : Type*} [Quiver α] [Quiver β] {a b : α}
    (F : Prefunctor α β)
    (h : pathLengths (F.obj a) (F.obj b) = pathLengths a b) :
    DirectedDistances.sdp (F.obj a) (F.obj b) = DirectedDistances.sdp a b := by
  change (⨅ p : Quiver.Path (F.obj a) (F.obj b), (p.length : ℕ∞)) = _
  apply le_antisymm
  · apply le_iInf
    intro p
    have hp : p.length ∈ pathLengths a b := ⟨p, rfl⟩
    rw [← h] at hp
    obtain ⟨q, hq⟩ := hp
    have hq' : q.length = p.length := hq
    exact (iInf_le _ q).trans (by exact_mod_cast hq'.le)
  · apply le_iInf
    intro q
    have hq : q.length ∈ pathLengths (F.obj a) (F.obj b) := ⟨q, rfl⟩
    rw [h] at hq
    obtain ⟨p, hp⟩ := hq
    have hp' : p.length = q.length := hp
    exact (iInf_le _ p).trans (by exact_mod_cast hp'.le)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
The targets are distinct and eventually reachable from both sources. Reachability proves
both shortest distances finite before their integer difference is taken. -/
theorem ae_uibhbotBusemannIncrementSdp_distance_realization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      Function.Injective (uibhbotBusemannTargetSdp k W) ∧
      ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
        Reachable (uibhbotBusemannSourceSdp k W) (uibhbotBusemannTargetSdp k W m) ∧
        Reachable (uibhbotBusemannSourceSdp (k - 1) W)
          (uibhbotBusemannTargetSdp k W m) ∧
        ∃ a b : ℕ,
          DirectedDistances.sdp (uibhbotBusemannSourceSdp k W)
              (uibhbotBusemannTargetSdp k W m) = (a : ℕ∞) ∧
          DirectedDistances.sdp (uibhbotBusemannSourceSdp (k - 1) W)
              (uibhbotBusemannTargetSdp k W m) = (b : ℕ∞) ∧
          uibhbotBusemannIncrementSdp k W = (a : ℤ) - (b : ℤ) := by
  filter_upwards [ae_uibhbot_incrementSdp_busemann_data,
    ae_uibhbotFutureBoundary_index, ae_uibhbotFuture_boundary_pathLengths]
      with W hdata hi hpaths k
  obtain ⟨h, hX⟩ := hdata k
  let ω := uibhbotFutureCode k W
  let w := fun i => ω (i + 1)
  let x := boundaryPresentVertex w h
  let F := uibhbotFutureToGlobal k W
  have hs (j : ℤ) (hj : j ≤ 0) :
      F.obj (x j) = uibhbotBusemannSourceSdp (k + j) W := by
    apply congrArg UIBHBOTPresentVertex.mk
    exact hi k h j hj
  have ht (m : ℕ) :
      uibhbotBusemannTargetSdp k W m = F.obj (x (m : ℤ)) := by
    unfold uibhbotBusemannTargetSdp
    rw [incrementSdp_boundaryId_eq ω h]
    rfl
  constructor
  · intro a b hab
    rw [ht a, ht b] at hab
    have he := uibhbotFutureToGlobal_obj_injective k W hab
    have hj := boundaryVertex_injective w h (congrArg PresentVertex.id he)
    exact_mod_cast hj
  · obtain ⟨B0, hB0⟩ := incrementSdp_reaches_boundary_tail w h (x 0)
      (boundaryVertex_allocated w h 0)
    obtain ⟨B1, hB1⟩ := incrementSdp_reaches_boundary_tail w h (x (-1))
      (by
        change ∃ n, boundaryVertex w h (-1) < (kmswStage w n).nextVertex
        exact boundaryVertex_allocated w h (-1))
    let B := max B0 B1
    let y : ℕ → PresentVertex w := fun n => x ((B + n : ℕ) : ℤ)
    have hy : Function.Injective y := by
      intro a b hab
      have he := boundaryVertex_injective w h (congrArg PresentVertex.id hab)
      change ((B + a : ℕ) : ℤ) = ((B + b : ℕ) : ℤ) at he
      omega
    have hr : ∀ n, Reachable (x (-1)) (y n) ∧ Reachable (x 0) (y n) := by
      intro n
      exact ⟨hB1 _ (by dsimp [B]; omega), hB0 _ (by dsimp [B]; omega)⟩
    obtain ⟨N, hN⟩ := hX.2 (-1) 0 y hy hr
    refine ⟨B + N, fun m hm => ?_⟩
    have hsum : B + (m - B) = m := by omega
    have hr0 : Reachable (x 0) (x (m : ℤ)) :=
      hB0 _ (by dsimp [B] at *; omega)
    have hr1 : Reachable (x (-1)) (x (m : ℤ)) :=
      hB1 _ (by dsimp [B] at *; omega)
    have hg0 : Reachable (F.obj (x 0)) (F.obj (x (m : ℤ))) := by
      obtain ⟨p⟩ := hr0
      exact ⟨F.mapPath p⟩
    have hg1 : Reachable (F.obj (x (-1))) (F.obj (x (m : ℤ))) := by
      obtain ⟨p⟩ := hr1
      exact ⟨F.mapPath p⟩
    have hs0 : F.obj (x 0) = uibhbotBusemannSourceSdp k W := by
      simpa only [add_zero] using hs 0 (by omega)
    have hs1 : F.obj (x (-1)) = uibhbotBusemannSourceSdp (k - 1) W := by
      simpa only [sub_eq_add_neg] using hs (-1) (by omega)
    rw [hs0, ← ht m] at hg0
    rw [hs1, ← ht m] at hg1
    let a := (DirectedDistances.sdp (x 0) (x (m : ℤ))).toNat
    let b := (DirectedDistances.sdp (x (-1)) (x (m : ℤ))).toNat
    have hp0 := hpaths k h 0 (by omega) (x (m : ℤ))
    have hp1 := hpaths k h (-1) (by omega) (x (m : ℤ))
    have hd0 : DirectedDistances.sdp (uibhbotBusemannSourceSdp k W)
        (uibhbotBusemannTargetSdp k W m) = (a : ℕ∞) := by
      have he := incrementSdp_eq_of_pathLengths F hp0
      change DirectedDistances.sdp (F.obj (x 0)) (F.obj (x (m : ℤ))) =
        DirectedDistances.sdp (x 0) (x (m : ℤ)) at he
      rw [hs0, ← ht m] at he
      have hne : DirectedDistances.sdp (x 0) (x (m : ℤ)) ≠ ⊤ :=
        fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) hr0
      simpa [a] using he.trans (ENat.natCast_toNat hne).symm
    have hd1 : DirectedDistances.sdp (uibhbotBusemannSourceSdp (k - 1) W)
        (uibhbotBusemannTargetSdp k W m) = (b : ℕ∞) := by
      have he := incrementSdp_eq_of_pathLengths F hp1
      change DirectedDistances.sdp (F.obj (x (-1))) (F.obj (x (m : ℤ))) =
        DirectedDistances.sdp (x (-1)) (x (m : ℤ)) at he
      rw [hs1, ← ht m] at he
      have hne : DirectedDistances.sdp (x (-1)) (x (m : ℤ)) ≠ ⊤ :=
        fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) hr1
      simpa [b] using he.trans (ENat.natCast_toNat hne).symm
    refine ⟨hg0, hg1, a, b, hd0, hd1, ?_⟩
    have he := hN (m - B) (by omega)
    change busemannSDPMeasurableVersion (uibhbotFutureCode k W) 0 -
      busemannSDPMeasurableVersion (uibhbotFutureCode k W) (-1) =
        (a : ℤ) - (b : ℤ)
    simpa only [a, b, y, hsum] using he

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
A fixed future copy characterizes increments along every distinct common reachable sequence. -/
private theorem ae_uibhbotFuture_incrementSdp_characterization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ K k : ℤ, k ≤ K →
      ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSourceSdp k W) (z m) ∧
        Reachable (uibhbotBusemannSourceSdp (k - 1) W) (z m)) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
        DirectedDistances.sdp (uibhbotBusemannSourceSdp k W) (z m) = (a : ℕ∞) ∧
        DirectedDistances.sdp (uibhbotBusemannSourceSdp (k - 1) W) (z m) =
          (b : ℕ∞) ∧
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion (k - K)
          (uibhbotFutureCode K W) = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [ae_uibhbot_incrementSdp_busemann_data,
    ae_uibhbotFutureBoundary_index, ae_uibhbotFuture_boundary_pathLengths,
    ae_uibhbotFuture_boundary_path_lift]
      with W hdata hi hpaths hl K k hk z hz hr
  obtain ⟨h, hX⟩ := hdata K
  let w := fun i => uibhbotFutureCode K W (i + 1)
  let x := boundaryPresentVertex w h
  let F := uibhbotFutureToGlobal K W
  let j := k - K
  have hj : j ≤ 0 := by dsimp [j]; omega
  have hj1 : j - 1 ≤ 0 := by omega
  have hs (i : ℤ) (hi' : i ≤ 0) : F.obj (x i) =
      uibhbotBusemannSourceSdp (K + i) W := by
    apply congrArg UIBHBOTPresentVertex.mk
    exact hi K h i hi'
  have hs0 : F.obj (x j) = uibhbotBusemannSourceSdp k W := by
    simpa only [j, add_sub_cancel] using hs j hj
  have hs1 : F.obj (x (j - 1)) = uibhbotBusemannSourceSdp (k - 1) W := by
    have he : K + (j - 1) = k - 1 := by dsimp [j]; omega
    simpa only [he] using hs (j - 1) hj1
  have hp : ∀ m, ∃ c : PresentVertex w, F.obj c = z m ∧ Reachable (x j) c := by
    intro m
    have hrm := (hr m).1
    rw [← hs0] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h j hj (z m) p
    exact ⟨c, hc, ⟨q⟩⟩
  choose y hy hy0 using hp
  have hy1 : ∀ m, Reachable (x (j - 1)) (y m) := by
    intro m
    have hrm := (hr m).2
    rw [← hs1] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h (j - 1) hj1 (z m) p
    have he : c = y m := uibhbotFutureToGlobal_obj_injective K W (hc.trans (hy m).symm)
    subst c
    exact ⟨q⟩
  have hiy : Function.Injective y := by
    intro a b hab
    apply hz
    rw [← hy a, ← hy b, hab]
  obtain ⟨N, hN⟩ := hX.2 (j - 1) j y hiy (fun m => ⟨hy1 m, hy0 m⟩)
  refine ⟨N, fun m hm => ?_⟩
  let a := (DirectedDistances.sdp (x j) (y m)).toNat
  let b := (DirectedDistances.sdp (x (j - 1)) (y m)).toNat
  have hp0 := hpaths K h j hj (y m)
  have hp1 := hpaths K h (j - 1) hj1 (y m)
  have hd0 : DirectedDistances.sdp (uibhbotBusemannSourceSdp k W) (z m) =
      (a : ℕ∞) := by
    have he := incrementSdp_eq_of_pathLengths F hp0
    change DirectedDistances.sdp (F.obj (x j)) (F.obj (y m)) =
      DirectedDistances.sdp (x j) (y m) at he
    rw [hs0, hy m] at he
    have hne : DirectedDistances.sdp (x j) (y m) ≠ ⊤ :=
      fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) (hy0 m)
    simpa [a] using he.trans (ENat.natCast_toNat hne).symm
  have hd1 : DirectedDistances.sdp (uibhbotBusemannSourceSdp (k - 1) W) (z m) =
      (b : ℕ∞) := by
    have he := incrementSdp_eq_of_pathLengths F hp1
    change DirectedDistances.sdp (F.obj (x (j - 1))) (F.obj (y m)) =
      DirectedDistances.sdp (x (j - 1)) (y m) at he
    rw [hs1, hy m] at he
    have hne : DirectedDistances.sdp (x (j - 1)) (y m) ≠ ⊤ :=
      fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) (hy1 m)
    simpa [b] using he.trans (ENat.natCast_toNat hne).symm
  exact ⟨a, b, hd0, hd1, hN m hm⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Compatibility of increments defined using different future copies, simultaneously at all
integer cutoffs. -/
theorem ae_uibhbotBusemannIncrementSdp_future_identity :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ K k : ℤ, k ≤ K →
      uibhbotBusemannIncrementSdp k W =
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion (k - K)
          (uibhbotFutureCode K W) := by
  filter_upwards [ae_uibhbotBusemannIncrementSdp_distance_realization,
    ae_uibhbotFuture_incrementSdp_characterization] with W hreal hchar K k hk
  obtain ⟨hi, B, hB⟩ := hreal k
  let z := fun m : ℕ => uibhbotBusemannTargetSdp k W (B + m)
  have hz : Function.Injective z := by
    intro a b hab
    have he := hi hab
    omega
  have hr : ∀ m, Reachable (uibhbotBusemannSourceSdp k W) (z m) ∧
      Reachable (uibhbotBusemannSourceSdp (k - 1) W) (z m) := by
    intro m
    exact ⟨(hB (B + m) (by omega)).1, (hB (B + m) (by omega)).2.1⟩
  obtain ⟨N, hN⟩ := hchar K k hk z hz hr
  obtain ⟨a, b, ha, hb, hi'⟩ := hN N le_rfl
  obtain ⟨c, d, hc, hd, hi''⟩ := (hB (B + N) (by omega)).2.2
  have hac : a = c := by exact_mod_cast ha.symm.trans hc
  have hbd : b = d := by exact_mod_cast hb.symm.trans hd
  rw [hac, hbd] at hi'
  exact hi''.trans hi'.symm

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Every finite family is transported through one common future copy. -/
theorem uibhbotBusemannIncrementSdp_iIndep :
    iIndepFun uibhbotBusemannIncrementSdp
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) := by
  classical
  apply iIndepFun_iff_finset.mpr
  intro s
  let K : ℤ := (s.sup (fun i : ℤ => i.toNat) : ℕ)
  have hK (i : s) : (i : ℤ) ≤ K := by
    have h := Finset.le_sup (f := fun i : ℤ => i.toNat) i.property
    have hi : (i : ℤ) ≤ ((i : ℤ).toNat : ℤ) := by omega
    dsimp [K]
    omega
  let f : s → (ℕ → Fin 3) → ℤ := fun i =>
    SDPMasterFromLaw.increment busemannSDPMeasurableVersion ((i : ℤ) - K)
  have hf (i : s) : Measurable (f i) :=
    (measurable_busemannSDPMeasurableVersion ((i : ℤ) - K)).sub
      (measurable_busemannSDPMeasurableVersion (((i : ℤ) - K) - 1))
  have hinj : Function.Injective (fun i : s => (i : ℤ) - K) := by
    intro a b hab
    apply Subtype.ext
    exact sub_left_injective hab
  have hind : iIndepFun f iidCodeMeasure :=
    sdpIncrements_iIndep_proved.precomp hinj
  have hcomp : iIndepFun
      (fun i : s => fun W => f i (uibhbotFutureCode K W))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) := by
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => ((hf i).comp (measurable_uibhbotFutureCode K)).aemeasurable)).mpr
    change (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
      (fun W => (fun (ω : ℕ → Fin 3) (i : s) => f i ω)
        (uibhbotFutureCode K W)) =
        Measure.pi (fun i : s =>
          (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
            (fun W => f i (uibhbotFutureCode K W)))
    rw [uibhbotFutureCode_map K (measurable_pi_iff.mpr hf)]
    have hmarg (i : s) := uibhbotFutureCode_map K (hf i)
    simp_rw [hmarg]
    exact hind.map_fun_eq_pi_map (fun i => (hf i).aemeasurable)
  apply hcomp.congr
  intro i
  filter_upwards [ae_uibhbotBusemannIncrementSdp_future_identity] with W hW
  exact (hW K i (hK i)).symm

end DirectedDistances.RandomWalk
