module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperRecordTargets
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperGeodesicExit
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperSeparatorTargets
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperGeodesicTargets
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperSeam
import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix
import DirectedDistances.PaperProofs.Section7.LongPathStageVertices

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open scoped Classical








theorem cellSdpUpper_first_bullet_conditional (w : ℕ → Fin 3) (n : ℕ)
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
    (hTargetsConf : ∀ k : ℤ,
      ∃ y : ℕ → PresentVertex (fun i => w (n + i)), Function.Injective y ∧
        (∀ j, Reachable
          (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
          Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
            (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
        (∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)) ∧
      ∃ J : ℕ, ∀ j, J ≤ j →
        (sdp (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j)).toNat ≤
          (sdp
            (⟨kmswWindowVertexMapInf w n
              (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)
            (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)).toNat) :
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
  obtain ⟨y, hy, hreach, havoid, J, hconfJ⟩ := hTargetsConf k
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
  have hVfuture : ∀ r, Reachable (boundaryPresentVertex u hn σn) (Y r) ∧
      Reachable (boundaryPresentVertex u hn k) (Y r) := by
    intro r
    exact ⟨(hYfuture r).2, (hYfuture r).1⟩
  obtain ⟨N0, hN0⟩ := hX.2 ℓ σ0 V hVinj hVbase
  obtain ⟨Nn, hNn⟩ := hXn.2 σn k Y hYinj hVfuture
  let r : ℕ := max T (max N0 Nn)
  have hrT : T ≤ r := by dsimp [r]; exact Nat.le_max_left _ _
  have hr0 : N0 ≤ r := by
    dsimp [r]
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrn : Nn ≤ r := by
    dsimp [r]
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
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
  have hXnid :
      ((sdp (boundaryPresentVertex u hn k) (Y r)).toNat : ℤ) -
        ((sdp (boundaryPresentVertex u hn σn) (Y r)).toNat : ℤ) =
        Xn k - Xn σn := by
    have h := hNn r hrn
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
  have hconfNat :
      (sdp (boundaryPresentVertex u hn k) (Y r)).toNat ≤
        (sdp (img (boundaryPresentVertex u hn k)) (img (Y r))).toNat := by
    simpa [Y, ytail, img, u, boundaryPresentVertex] using hconfR
  have hconfInt :
      ((sdp (boundaryPresentVertex u hn k) (Y r)).toNat : ℤ) ≤
        ((sdp (img (boundaryPresentVertex u hn k)) (img (Y r))).toNat : ℤ) :=
    Int.ofNat_le.mpr hconfNat
  have hchain := sdp_cell_upper_chain
    ((sdp x W).toNat : ℤ) ((sdp (img (boundaryPresentVertex u hn k))
      (img (Y r))).toNat : ℤ)
    ((sdp (boundaryPresentVertex u hn k) (Y r)).toNat : ℤ)
    ((sdp (boundaryPresentVertex u hn σn) (Y r)).toNat : ℤ)
    ((sdp xs W).toNat : ℤ) (X ℓ) (X σ0) (Xn k) (Xn σn) ((sdp x z).toNat : ℤ)
    hgeoChain hXid hXnid hseamInt hconfInt
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

/-- Corollary composing the target output of `cell_sdp_separator_targets`, after
instantiating its almost-sure event at the fixed code stream and boundary data,
with confinement only along the sequence selected from that output for each `k`.
The confinement issue remains a root concern; see -/
theorem cellSdpUpper_first_bullet_of_targets (w : ℕ → Fin 3) (n : ℕ)
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
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)))
    (hconf : ∀ k : ℤ, ∃ J : ℕ, ∀ j, J ≤ j →
      (sdp (boundaryPresentVertex (fun i => w (n + i)) hn k)
        ((Classical.choose (hTargets k)) j)).toNat ≤
      (sdp
        (⟨kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)
        (⟨kmswWindowVertexMapInf w n
          ((Classical.choose (hTargets k)) j).id⟩ : PresentVertex w)).toNat) :
    ∃ k : ℤ,
      -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
      k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
      sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
        ⟨kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
        (((2 * M0 + 2 * Mn).toNat : ℕ) : ℕ∞) := by
  have hTargetsConf : ∀ k : ℤ,
      ∃ y : ℕ → PresentVertex (fun i => w (n + i)), Function.Injective y ∧
        (∀ j, Reachable
          (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
          Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
            (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
        (∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)) ∧
        ∃ J : ℕ, ∀ j, J ≤ j →
          (sdp (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j)).toNat ≤
            (sdp
              (⟨kmswWindowVertexMapInf w n
                (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)
              (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)).toNat := by
    intro k
    let y : ℕ → PresentVertex (fun i => w (n + i)) := Classical.choose (hTargets k)
    have hy := Classical.choose_spec (hTargets k)
    obtain ⟨J, hconfJ⟩ := hconf k
    exact ⟨y, hy.1, hy.2.1, hy.2.2, J, by simpa [y] using hconfJ⟩
  exact cellSdpUpper_first_bullet_conditional w n h0 hn X Xn M0 Mn hX hXn
    hM0 hMn ℓ hℓ hℓStage P hP hTargetsConf

end DirectedDistances.PaperProofs.Section7
