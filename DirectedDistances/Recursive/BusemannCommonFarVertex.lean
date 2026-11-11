module

public import DirectedDistances.KMSW.BusemannM0Unconditional
public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.Recursive.OneStepTransport
import DirectedDistances.Recursive.LDPRelatingLeft
import DirectedDistances.Recursive.LDPRelatingDown
import Mathlib.Order.Filter.Finite

/-! # A common far vertex for the two LDP Busemann functions

Helpers for `lem:LDP-relating-X1-X`, specifically `eqn-LDP-relating-w`
`thm-busemann` is synchronized over the finite window in both maps. A tail
of the shifted right boundary supplies the common injective sequence.

These are helpers on the hit-indexed exploration carrier, subject to the
same F1/F4 identification qualifications as `BusemannM0Unconditional`.
Only proved finite LDP values on reachable pairs are subtracted. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory Filter

private theorem window_ldp_eventually {w : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w))
    (x : ℤ → PresentVertex w) (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb x X)
    (s : Finset ℤ) (y : ℕ → PresentVertex w) (hy : Function.Injective y)
    (hr : ∀ k ∈ s, ∀ j, Reachable (x k) (y j)) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ k (hk : k ∈ s) k' (hk' : k' ∈ s),
      (presentLdpFiniteNat hb (hr k' hk' j) : ℤ) -
        (presentLdpFiniteNat hb (hr k hk j) : ℤ) = X k' - X k := by
  have hh : ∀ᶠ j : ℕ in atTop,
      ∀ k k' : {k : ℤ // k ∈ s},
        (presentLdpFiniteNat hb (hr k'.val k'.property j) : ℤ) -
          (presentLdpFiniteNat hb (hr k.val k.property j) : ℤ) = X k'.val - X k.val := by
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro k'
    obtain ⟨N, hN⟩ := hX.2 k.val k'.val y hy
      (fun j => ⟨hr k.val k.property j, hr k'.val k'.property j⟩)
    exact eventually_atTop.mpr ⟨N, fun j hj => (hN j hj).symm⟩
  exact eventually_atTop.mp (hh.mono fun j hj k hk k' hk' => hj ⟨k, hk⟩ ⟨k', hk'⟩)

private theorem reachable_target_allocated {w : ℕ → Fin 3}
    {a b : PresentVertex w} (ha : kmswVertexAllocated w a)
    (hr : Reachable a b) : kmswVertexAllocated w b := by
  obtain ⟨p⟩ := hr
  cases p with
  | nil => exact ha
  | cons p e =>
    obtain ⟨n, hn, _⟩ := e.property.1
    have hb := (kmswStage_endpoints_lt_nextVertex w n e.val hn).2
    rw [(edge_endpoints_eq w hn).2, e.property.2.2] at hb
    exact ⟨n, hb⟩

/-- Finite synchronization of the LDP characterization of `thm-busemann`:
along a common reachable injective sequence, both maps satisfy all the
identities of `eqn-LDP-relating-w` eventually, with a single threshold.
Helper for `lem:LDP-relating-X1-X` -/
theorem boundaryBusemannLDP_commonFarVertex_eventually
    (w : ℕ → Fin 3)
    (hb0 : PresentPathLengthsBounded (w := w))
    (hb1 : PresentPathLengthsBounded (w := fun i => w (1 + i)))
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (1 + i)))
    (X0 X1 : ℤ → ℤ)
    (hX0 : IsBoundaryBusemannLDP hb0 (boundaryPresentVertex w h0) X0)
    (hX1 : IsBoundaryBusemannLDP hb1
      (boundaryPresentVertex (fun i => w (1 + i)) h1) X1)
    (y : ℕ → PresentVertex (fun i => w (1 + i)))
    (hy : Function.Injective y)
    (hr0 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2, ∀ j,
      Reachable (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 (y j)))
    (hr1 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2, ∀ j,
      Reachable (boundaryPresentVertex (fun i => w (1 + i)) h1 k) (y j)) :
    ∃ N : ℕ, ∀ j, N ≤ j →
      (∀ k (hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        (presentLdpFiniteNat hb0 (hr0 k' hk' j) : ℤ) -
          (presentLdpFiniteNat hb0 (hr0 k hk j) : ℤ) = X0 k' - X0 k) ∧
      (∀ k (hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        (presentLdpFiniteNat hb1 (hr1 k' hk' j) : ℤ) -
          (presentLdpFiniteNat hb1 (hr1 k hk j) : ℤ) = X1 k' - X1 k) := by
  have ha : ∀ j, kmswVertexAllocated (fun i => w (1 + i)) (y j) := by
    intro j
    exact reachable_target_allocated (boundaryVertex_allocated _ h1 0)
      (hr1 0 (by decide) j)
  have hy0 : Function.Injective (fun j => shiftLimitVertex w 1 (y j)) := by
    intro i j hij
    exact hy (shiftLimitVertex_injective w 1 (ha i) (ha j) hij)
  obtain ⟨N0, hN0⟩ := window_ldp_eventually hb0 _ X0 hX0 _ _ hy0 hr0
  obtain ⟨N1, hN1⟩ := window_ldp_eventually hb1 _ X1 hX1 _ _ hy hr1
  exact ⟨max N0 N1, fun j hj =>
    ⟨hN0 j ((Nat.le_max_left _ _).trans hj),
      hN1 j ((Nat.le_max_right _ _).trans hj)⟩⟩

private theorem allocated_reaches_right_tail (w : ℕ → Fin 3)
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

private theorem window_reaches_right_tail (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    ∃ B : ℕ, ∀ k ∈ Finset.Icc (-2 : ℤ) 2, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable (boundaryPresentVertex w h k) (boundaryPresentVertex w h l) := by
  classical
  have hh : ∀ k : ℤ, ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable (boundaryPresentVertex w h k) (boundaryPresentVertex w h l) :=
    fun k => allocated_reaches_right_tail w h _ (boundaryVertex_allocated w h k)
  choose B hB using hh
  refine ⟨(Finset.Icc (-2 : ℤ) 2).sup B, ?_⟩
  intro k hk l hl
  apply hB k l
  have hle : B k ≤ (Finset.Icc (-2 : ℤ) 2).sup B := Finset.le_sup hk
  exact (Int.ofNat_le.mpr hle).trans hl

private theorem boundary_allocated_at_hit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    boundaryVertex w h k < (kmswStage w (boundaryHitTime w h k)).nextVertex := by
  have hh := kmswStage_endpoints_lt_nextVertex w (boundaryHitTime w h k)
    (act w (boundaryHitTime w h k)) (act_lt_nextEdge w le_rfl)
  have he := edge_endpoints_eq w
    (act_lt_nextEdge w (le_refl (boundaryHitTime w h k)))
  rw [he.1, ← boundaryVertex_eq_edgeWest_hit w h k] at hh
  exact hh.1

private theorem shift_right_boundary_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (1 + i)))
    (l : ℤ) (hl : 2 ≤ l) :
    shiftLimitVertex w 1 (boundaryPresentVertex (fun i => w (1 + i)) h1 l) =
      boundaryPresentVertex w h0 (l - R w 1) := by
  change shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (1 + i)) h1 l⟩ =
    ⟨boundaryVertex w h0 (l - R w 1)⟩
  refine (shiftLimitVertex_eq w 1 (boundaryHitTime _ h1 l)
    ⟨boundaryVertex (fun i => w (1 + i)) h1 l⟩
    (boundary_allocated_at_hit _ h1 l)).trans ?_
  apply congrArg PresentVertex.mk
  have h1' : BoundaryHitWitnesses (fun i => w (i + 1)) := by
    simpa only [Nat.add_comm] using h1
  have hcases : w 0 = 0 ∨ w 0 = 1 ∨ w 0 = 2 := by omega
  rcases hcases with hw | hw | hw
  · have hmap := leftShift_boundaryVertex_right w h0 h1' hw l (by omega)
    have hR : R w 1 = 0 := by simp [R, hw]
    simpa only [Nat.add_comm, hR, sub_zero] using hmap
  · have hmap := upShift_boundaryVertex_right w h0 h1' hw l hl
    have hR : R w 1 = 1 := by simp [R, hw]
    simpa only [Nat.add_comm, hR] using hmap
  · have hmap := downShift_boundaryVertex_right w h0 h1' hw l (by omega)
    have hR : R w 1 = -1 := by simp [R, hw]
    simpa only [Nat.add_comm, hR, sub_neg_eq_add] using hmap

/-- A concrete common sequence: a tail of the shifted right boundary is
injective and reachable from every boundary index in `[-2,2]` in both maps.
This supplies the sequence used with `thm-busemann` in
`eqn-LDP-relating-w`, a helper for `lem:LDP-relating-X1-X` -/
theorem boundary_rightTail_common_shift (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (1 + i))) :
    ∃ B : ℕ,
      let y := fun j : ℕ =>
        boundaryPresentVertex (fun i => w (1 + i)) h1 ((B + j : ℕ) : ℤ)
      Function.Injective y ∧
      (∀ j, kmswVertexAllocated (fun i => w (1 + i)) (y j)) ∧
      (∀ k ∈ Finset.Icc (-2 : ℤ) 2, ∀ j,
        Reachable (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 (y j))) ∧
      (∀ k ∈ Finset.Icc (-2 : ℤ) 2, ∀ j,
        Reachable (boundaryPresentVertex (fun i => w (1 + i)) h1 k) (y j)) := by
  obtain ⟨B0, hB0⟩ := window_reaches_right_tail w h0
  obtain ⟨B1, hB1⟩ := window_reaches_right_tail (fun i => w (1 + i)) h1
  let B := B0 + B1 + (R w 1).toNat + 2
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hh := boundaryVertex_injective (fun i => w (1 + i)) h1
      (congrArg PresentVertex.id hij)
    dsimp [boundaryPresentVertex] at hh
    omega
  · intro j
    exact boundaryVertex_allocated _ h1 _
  · intro k hk j
    rw [shift_right_boundary_image w h0 h1 _ (by dsimp [B]; omega)]
    exact hB0 k hk _ (by dsimp [B]; omega)
  · intro k hk j
    exact hB1 k hk _ (by dsimp [B]; omega)

/-- A common shifted vertex realizes both finite families of LDP Busemann
differences. This is the deterministic `eqn-LDP-relating-w` helper for
`lem:LDP-relating-X1-X`, obtained from `thm-busemann`'s characterization -/
theorem boundaryBusemannLDP_commonFarVertex (w : ℕ → Fin 3)
    (hb0 : PresentPathLengthsBounded (w := w))
    (hb1 : PresentPathLengthsBounded (w := fun i => w (1 + i)))
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (1 + i)))
    (X0 X1 : ℤ → ℤ)
    (hX0 : IsBoundaryBusemannLDP hb0 (boundaryPresentVertex w h0) X0)
    (hX1 : IsBoundaryBusemannLDP hb1
      (boundaryPresentVertex (fun i => w (1 + i)) h1) X1) :
    ∃ z : PresentVertex (fun i => w (1 + i)),
      kmswVertexAllocated (fun i => w (1 + i)) z ∧
      ∃ (hr0 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
          Reachable (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 z))
        (hr1 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
          Reachable (boundaryPresentVertex (fun i => w (1 + i)) h1 k) z),
      (∀ k (hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        (presentLdpFiniteNat hb0 (hr0 k' hk') : ℤ) -
          (presentLdpFiniteNat hb0 (hr0 k hk) : ℤ) = X0 k' - X0 k) ∧
      (∀ k (hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        (presentLdpFiniteNat hb1 (hr1 k' hk') : ℤ) -
          (presentLdpFiniteNat hb1 (hr1 k hk) : ℤ) = X1 k' - X1 k) := by
  obtain ⟨B, hy, ha, hr0, hr1⟩ := boundary_rightTail_common_shift w h0 h1
  obtain ⟨N, hN⟩ := boundaryBusemannLDP_commonFarVertex_eventually
    w hb0 hb1 h0 h1 X0 X1 hX0 hX1 _ hy hr0 hr1
  exact ⟨_, ha N, (fun k hk => hr0 k hk N), (fun k hk => hr1 k hk N), hN N le_rfl⟩

private theorem ae_comp_one_codeShift {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p (RandomWalk.codeShift 1 ω) := by
  have hp' : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure.map (RandomWalk.codeShift 1), p ω := by
    simpa only [RandomWalk.map_codeShift] using hp
  exact (Measure.tendsto_ae_map
    (RandomWalk.measurable_codeShift 1).aemeasurable).eventually hp'

/-- Almost surely, the LDP Busemann functions for `ω(i+1)` and `ω(i+2)`
have a common shifted vertex realizing all differences in `[-2,2]`.
The second code below is written `w(1+i)` to match the limit embedding;
for `w i = ω(i+1)` it is exactly `ω(i+2)` by associativity and commutativity.
This uses shift invariance to apply the unconditional `thm-busemann` helper
twice, and proves the `eqn-LDP-relating-w` helper for -/
theorem iidCodes_ae_boundaryBusemannLDP_commonFarVertex :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin0 : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ hfin1 : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => w (1 + i)) n).nextEdge ∧
          ((kmswStage (fun i => w (1 + i)) n).west e = v ∨
            (kmswStage (fun i => w (1 + i)) n).east e = v)}.Finite,
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
      ∃ X0 X1 : ℤ → ℤ,
        IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
          (boundaryPresentVertex w h0) X0 ∧
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
          (boundaryPresentVertex (fun i => w (1 + i)) h1) X1 ∧
        ∃ z : PresentVertex (fun i => w (1 + i)),
          kmswVertexAllocated (fun i => w (1 + i)) z ∧
          ∃ (hr0 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
              Reachable (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 z))
            (hr1 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
              Reachable (boundaryPresentVertex (fun i => w (1 + i)) h1 k) z),
          (∀ k (hk : k ∈ Finset.Icc (-2 : ℤ) 2)
              k' (hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
            (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin0)
                (hr0 k' hk') : ℤ) -
              (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin0)
                (hr0 k hk) : ℤ) = X0 k' - X0 k) ∧
          (∀ k (hk : k ∈ Finset.Icc (-2 : ℤ) 2)
              k' (hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
            (presentLdpFiniteNat
                (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
                (hr1 k' hk') : ℤ) -
              (presentLdpFiniteNat
                (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
                (hr1 k hk) : ℤ) = X1 k' - X1 k) := by
  have hs := ae_comp_one_codeShift iidCodes_ae_boundaryBusemannLDP_existsUnique
  filter_upwards [iidCodes_ae_boundaryBusemannLDP_existsUnique, hs] with ω hω hsω
  have heq : (fun i => RandomWalk.codeShift 1 ω (i + 1)) =
      (fun i => ω ((1 + i) + 1)) := by
    funext i
    change (if i + 1 = 0 then 0 else ω (1 + (i + 1))) = ω ((1 + i) + 1)
    rw [ite_eq_right (by omega : ¬ i + 1 = 0)]
    rfl
  rw [heq] at hsω
  obtain ⟨hfin0, h0, X0, hX0, -⟩ := hω
  obtain ⟨hfin1, h1, X1, hX1, -⟩ := hsω
  refine ⟨hfin0, hfin1, h0, h1, X0, X1, hX0, hX1, ?_⟩
  exact boundaryBusemannLDP_commonFarVertex (fun i => ω (i + 1))
    (presentPathLengthsBounded_of_hfin _ hfin0)
    (presentPathLengthsBounded_of_hfin _ hfin1) h0 h1 X0 X1 hX0 hX1

end DirectedDistances.Recursive
