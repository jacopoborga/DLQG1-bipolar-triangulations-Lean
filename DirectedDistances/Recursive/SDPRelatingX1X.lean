module

public import DirectedDistances.Recursive.SDPRelatingRootCases
public import DirectedDistances.Recursive.SDPRelatingDown
public import DirectedDistances.Recursive.SDPRelatingLeft
public import DirectedDistances.Recursive.SDPRelatingUp
public import DirectedDistances.Recursive.SDPCommonFarVertex
import DirectedDistances.KMSW.WalkRecordCounts

/-! # First-step relations for the SDP boundary Busemann functions

Helper forms of `lem:SDP-relating-X1-X`, `eqn-sdp-relating1-3`
pairs are subtracted; the distance identities preserve `+∞` on unreachable pairs.

labelling, the almost-sure interpretation, and identification of the exploration
graph with the paper's map. -/

public section
namespace DirectedDistances.Recursive
open DirectedDistances.KMSW Quiver MeasureTheory

private theorem root_ends (w : ℕ → Fin 3) :
    edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 :=
  edge_endpoints_eq w (j := 0) (e := 0) (by change 0 < 1; omega)

private def rootArrow (w : ℕ → Fin 3) :
    (⟨0⟩ : PresentVertex w) ⟶ ⟨1⟩ :=
  ⟨0, ⟨0, by change 0 < 1; omega, rfl⟩,
    (root_ends w).1, (root_ends w).2⟩

private theorem boundary_allocated (u : ℕ → Fin 3)
    (h : BoundaryHitWitnesses u) (k : ℤ) :
    boundaryVertex u h k < (kmswStage u (boundaryHitTime u h k)).nextVertex := by
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryVertex_zero, boundaryHitTime_zero, kmswStage, kmswInit]
  · by_cases hk1 : k = 1
    · subst k
      have hm := CutConverse.nextVertex_mono u
        (Nat.zero_le (boundaryHitTime u h 1))
      simpa [boundaryVertex_one, kmswStage, kmswInit] using
        (show 1 < (kmswStage u (boundaryHitTime u h 1)).nextVertex by
          change 2 ≤ _ at hm
          omega)
    · have hb := kmswStage_endpoints_lt_nextVertex u
        (boundaryHitTime u h k) (act u (boundaryHitTime u h k))
        (act_lt_nextEdge u le_rfl)
      rw [(edge_endpoints_eq u (act_lt_nextEdge u le_rfl)).1] at hb
      simpa [boundaryVertex, hk0, hk1, activeInitial] using hb.1

private theorem shifted_boundary_allocated (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => w (i + 1))) (k : ℤ) :
    kmswVertexAllocated (fun i => w (1 + i))
      ⟨boundaryVertex (fun i => w (i + 1)) h k⟩ := by
  have hs : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
    funext i
    rw [Nat.add_comm]
  exact ⟨boundaryHitTime _ h k,
    by simpa only [hs] using boundary_allocated _ h k⟩

private theorem boundary_image_of_stage (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => w (i + 1))) (k : ℤ) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h k⟩ =
      (⟨kmswShiftVertexMapAll w 1
        (boundaryHitTime (fun i => w (i + 1)) h k)
        (boundaryVertex (fun i => w (i + 1)) h k)⟩ : PresentVertex w) := by
  apply shiftLimitVertex_eq
  have hs : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
    funext i
    rw [Nat.add_comm]
  simpa only [hs] using boundary_allocated _ h k

private theorem boundary_ne_zero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≠ 0) :
    boundaryVertex w h k ≠ 0 := by
  intro he
  have hh := boundaryVertex_injective w h
    (he.trans (boundaryVertex_zero w h).symm)
  exact hk hh

private theorem down_minus_one_image (w : ℕ → Fin 3)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1))) (hw : w 0 = 2) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 (-1)⟩ =
      (⟨0⟩ : PresentVertex w) := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  let t := boundaryHitTime u h1 (-1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i; simp only [u, Nat.add_comm]
  have hstep : ∀ i, |L u (i + 1) - L u i| ≤ 1 := by
    intro i
    have hs : L u (i + 1) = L u i +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (u i)).1 :=
      Finset.sum_range_succ _ _
    rw [hs, add_sub_cancel_left]
    change |((u i).val : ℤ) - 1| ≤ 1
    have hh := (u i).isLt
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hspec : L u t = -1 := boundaryHitTime_left_spec u h1 (by omega)
  have hfind : t = Nat.find (h1.leftHit (-1) (by omega)) := by
    simp [t, boundaryHitTime]
  have hrecord := (strict_running_minimum_iff_first_hit (L u) rfl hstep t t (-1)
    (by omega) (h1.leftHit (-1) (by omega))).mpr ⟨le_rfl, hspec, hfind⟩
  have hbefore : ∀ r, r ≤ t → -1 ≤ L u r := by
    intro r hr
    rcases hr.eq_or_lt with he | he
    · rw [he, hspec]
    · have hh := (Finset.mem_filter.mp hrecord.1).2 r he
      rw [hspec] at hh
      omega
  have hL1 : L w 1 = 1 := by simp [L, hw]
  have hfinish : L w (1 + t) = 0 := by
    have hh := shiftedL_eq_translated w t
    change L u t = _ at hh
    rw [hspec, hL1] at hh
    rw [Nat.add_comm]
    omega
  have habove : ∀ j, 0 ≤ j → j ≤ 1 + t → L w 0 ≤ L w j := by
    intro j _ hj
    by_cases hj0 : j = 0
    · subst j; exact le_rfl
    · have hidx : j - 1 + 1 = j := by omega
      have hh := shiftedL_eq_translated w (j - 1)
      change L u (j - 1) = _ at hh
      rw [hidx, hL1] at hh
      have hb := hbefore (j - 1) (by omega)
      have hz : L w 0 = 0 := rfl
      omega
  have hwest := kmsw_west_act_eq_of_level w (Nat.zero_le (1 + t))
    (by simpa only [hfinish] using (show L w 0 = 0 from rfl)) habove
  have hwzero : edgeWest w (act w (1 + t)) = 0 := by
    rw [← (edge_endpoints_eq w (act_lt_nextEdge w le_rfl)).1]
    have hr := (initial_edge_endpoints w (1 + t)).1
    change (kmswStage w (1 + t)).west 0 = _ at hwest
    exact hwest.symm.trans hr
  rw [boundary_image_of_stage]
  apply congrArg PresentVertex.mk
  have ha := boundaryVertex_eq_edgeWest_hit u h1 (-1)
  have hp := kmswShift_active_present w 1 t
  have hm := (kmswShift_present_edge_maps w 1 t
    (act (fun i => w (1 + i)) t) hp.1 hp.2).2.1
  have hact : boundaryVertex u h1 (-1) =
      edgeWest (fun i => w (1 + i)) (act (fun i => w (1 + i)) t) := by
    simpa only [hseq] using ha
  change kmswShiftVertexMapAll w 1 t (boundaryVertex u h1 (-1)) = 0
  rw [hact, ← hm, kmswShift_active_edge_map, hwzero]

private theorem down_boundary_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) {j k : ℤ}
    (hpair : (j = -1 ∧ k = -2) ∨ (j = 0 ∧ k = -1) ∨ (j = 1 ∧ k = 0)) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ =
      (⟨boundaryVertex w h0 j⟩ : PresentVertex w) := by
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [boundary_image_of_stage]
    exact congrArg PresentVertex.mk (downShift_boundaryVertex_left w h0 h1 hw (-2) (by omega))
  · simpa only [boundaryVertex_zero] using down_minus_one_image w h1 hw
  · rw [boundary_image_of_stage]
    apply congrArg PresentVertex.mk
    simpa only [boundaryVertex_zero, boundaryHitTime_zero] using
      (downShift_rootVertices_and_firstStageImage w h0 hw).1


private theorem down_outer_sdp (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) (j k : ℤ)
    (hpair : (j = -1 ∧ k = -2) ∨ (j = 1 ∧ k = 0))
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    sdp (⟨boundaryVertex w h0 j⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
  have hp : (j = -1 ∧ k = -2) ∨ (j = 0 ∧ k = -1) ∨ (j = 1 ∧ k = 0) := by
    rcases hpair with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inr hh)
  have hi := down_boundary_image w h0 h1 hw hp
  rw [← hi]
  apply downShift_sdp_image_eq w (shifted_boundary_allocated w h1 k) hb
  rw [hi]
  apply boundary_ne_zero w h0
  rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

private theorem down_root_sdp_min (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2)
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    sdp (⟨boundaryVertex w h0 0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      min (sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 (-1)⟩ :
        PresentVertex (fun i => w (1 + i))) b)
        (1 + sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ :
          PresentVertex (fun i => w (1 + i))) b) := by
  let a : PresentVertex (fun i => w (1 + i)) :=
    ⟨boundaryVertex (fun i => w (i + 1)) h1 (-1)⟩
  let d : PresentVertex (fun i => w (1 + i)) := ⟨0⟩
  have ha := shifted_boundary_allocated w h1 (-1)
  have hroot : shiftLimitVertex w 1 a = (⟨0⟩ : PresentVertex w) :=
    down_minus_one_image w h1 hw
  have hone : shiftLimitVertex w 1 d = (⟨1⟩ : PresentVertex w) := by
    simpa only [d, boundaryVertex_zero, boundaryVertex_one] using
      down_boundary_image w h0 h1 hw (j := 1) (k := 0)
        (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have hle0 : sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤ sdp a b := by
    simpa only [hroot] using upShift_sdp_le w a b
  have hle1 : sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤
      1 + sdp d b := by
    have hshift : sdp (⟨1⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤ sdp d b := by
      simpa only [hone] using upShift_sdp_le w d b
    calc
      sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤
          sdp (⟨0⟩ : PresentVertex w) (⟨1⟩ : PresentVertex w) +
            sdp (⟨1⟩ : PresentVertex w) (shiftLimitVertex w 1 b) := sdp_triangle _ _ _
      _ ≤ ((rootArrow w).toPath.length : ℕ∞) + sdp d b :=
        add_le_add (sdp_le_length (rootArrow w).toPath) hshift
      _ = 1 + sdp d b := by simp only [Path.length_toPath, Nat.cast_one]
  have hlate : sdp a b ≤
      (⨅ p : {p : Path (⟨boundaryVertex w h0 0⟩ : PresentVertex w)
          (shiftLimitVertex w 1 b) // 0 ∉ pathEdgeList p}, (p.val.length : ℕ∞)) := by
    apply le_iInf
    intro p
    obtain ⟨c, hc, q, hq, hlen, _⟩ := upShift_path_lift_avoiding_root
      w h0 0 a ha (by simpa only [boundaryVertex_zero] using hroot) p.val (by
        intro e he heq
        have he0 : e = 0 := by simpa only [act, kmswStage, kmswInit] using heq
        exact p.property (he0 ▸ he))
    have hcb : c = b := shiftLimitVertex_injective w 1 hc hb hq
    subst c
    calc
      sdp a b ≤ q.length := sdp_le_length q
      _ = p.val.length := by exact_mod_cast hlen
  apply le_antisymm
  · simpa only [boundaryVertex_zero] using le_min hle0 hle1
  · rw [downShift_root_sdp_decompose w h0 hw hb]
    simpa only [boundaryVertex_zero, a, d] using min_le_min hlate (le_refl (1 + sdp d b))

private theorem enat_min_cast (a b : ℕ) :
    ((min a b : ℕ) : ℕ∞) = min (a : ℕ∞) (b : ℕ∞) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (ENat.natCast_le_natCast.mpr h)]
  · rw [min_eq_right h, min_eq_right (ENat.natCast_le_natCast.mpr h)]

/-- Deterministic renormalization for `lem:SDP-relating-X1-X`,
vertex identities are `eqn-SDP-relating-w` (lines 560–562). Reachability
makes every `toNat` finite. Helper form only, subject to F1/F4. -/
theorem firstStep_boundary_pair_of_common_vertex_sdp (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (z : PresentVertex (fun i => w (1 + i)))
    (hz : kmswVertexAllocated (fun i => w (1 + i)) z)
    (hr0 : ∀ k : ℤ, k ∈ Set.Icc (-2 : ℤ) 2 →
      Reachable (⟨boundaryVertex w h0 k⟩ : PresentVertex w) (shiftLimitVertex w 1 z))
    (hr1 : ∀ k : ℤ, k ∈ Set.Icc (-2 : ℤ) 2 →
      Reachable (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) z)
    (X0 X1 : ℤ → ℤ) (hzero0 : X0 0 = 0) (hzero1 : X1 0 = 0)
    (hcommon :
      (∀ k k' : ℤ, ∀ (_hk : k ∈ Set.Icc (-2 : ℤ) 2)
        (_hk' : k' ∈ Set.Icc (-2 : ℤ) 2),
        ((sdp (⟨boundaryVertex w h0 k'⟩ : PresentVertex w)
            (shiftLimitVertex w 1 z)).toNat : ℤ) -
          ((sdp (⟨boundaryVertex w h0 k⟩ : PresentVertex w)
            (shiftLimitVertex w 1 z)).toNat : ℤ) = X0 k' - X0 k) ∧
      (∀ k k' : ℤ, ∀ (_hk : k ∈ Set.Icc (-2 : ℤ) 2)
        (_hk' : k' ∈ Set.Icc (-2 : ℤ) 2),
        ((sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 k'⟩ :
            PresentVertex (fun i => w (1 + i))) z).toNat : ℤ) -
          ((sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
            PresentVertex (fun i => w (1 + i))) z).toNat : ℤ) = X1 k' - X1 k)) :
    (w 0 = 2 → (X0 (-1), X0 1) =
      (X1 (-2) - min (X1 (-1)) 1, -min (X1 (-1)) 1)) ∧
    (w 0 = 0 → (X0 (-1), X0 1) = (-X1 1 - 1, -1)) ∧
    (w 0 = 1 → (X0 (-1), X0 1) =
      (X1 (-1) - min 0 (X1 2 + 1), X1 2 - min 0 (X1 2 + 1))) := by
  let i0 : Set.Icc (-2 : ℤ) 2 := ⟨0, by constructor <;> omega⟩
  let im1 : Set.Icc (-2 : ℤ) 2 := ⟨-1, by constructor <;> omega⟩
  let im2 : Set.Icc (-2 : ℤ) 2 := ⟨-2, by constructor <;> omega⟩
  let i1 : Set.Icc (-2 : ℤ) 2 := ⟨1, by constructor <;> omega⟩
  let i2 : Set.Icc (-2 : ℤ) 2 := ⟨2, by constructor <;> omega⟩
  let D0 (k : Set.Icc (-2 : ℤ) 2) := (sdp (⟨boundaryVertex w h0 k.val⟩ : PresentVertex w) (shiftLimitVertex w 1 z)).toNat
  let D1 (k : Set.Icc (-2 : ℤ) 2) := (sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 k.val⟩ : PresentVertex (fun i => w (1 + i))) z).toNat
  have diff0 (k : Set.Icc (-2 : ℤ) 2) : (D0 k : ℤ) - (D0 i0 : ℤ) = X0 k := by
    simpa only [D0, i0, hzero0, sub_zero] using hcommon.1 0 k i0.property k.property
  have diff1 (k : Set.Icc (-2 : ℤ) 2) : (D1 k : ℤ) - (D1 i0 : ℤ) = X1 k := by
    simpa only [D1, i0, hzero1, sub_zero] using hcommon.2 0 k i0.property k.property
  have b0 (k : Set.Icc (-2 : ℤ) 2) :
      sdp (⟨boundaryVertex w h0 k⟩ : PresentVertex w) (shiftLimitVertex w 1 z) =
        (D0 k : ℕ∞) := (ENat.natCast_toNat (fun ht => sdp_eq_top_iff_not_reachable.mp ht (hr0 k k.property))).symm
  have b1 (k : Set.Icc (-2 : ℤ) 2) :
      sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) z = (D1 k : ℕ∞) :=
    (ENat.natCast_toNat (fun ht => sdp_eq_top_iff_not_reachable.mp ht (hr1 k k.property))).symm
  have d0m := diff0 im1
  have d0p := diff0 i1
  have d1m := diff1 im1
  have d1mm := diff1 im2
  have d1p := diff1 i1
  have d1pp := diff1 i2
  change (D0 im1 : ℤ) - (D0 i0 : ℤ) = X0 (-1) at d0m
  change (D0 i1 : ℤ) - (D0 i0 : ℤ) = X0 1 at d0p
  change (D1 im1 : ℤ) - (D1 i0 : ℤ) = X1 (-1) at d1m
  change (D1 im2 : ℤ) - (D1 i0 : ℤ) = X1 (-2) at d1mm
  change (D1 i1 : ℤ) - (D1 i0 : ℤ) = X1 1 at d1p
  change (D1 i2 : ℤ) - (D1 i0 : ℤ) = X1 2 at d1pp
  refine ⟨?_, ?_, ?_⟩
  · intro hw
    have hm := down_outer_sdp w h0 h1 hw (-1) (-2) (Or.inl ⟨rfl, rfl⟩) z hz
    have hp := down_outer_sdp w h0 h1 hw 1 0 (Or.inr ⟨rfl, rfl⟩) z hz
    have hc := down_root_sdp_min w h0 h1 hw z hz
    rw [b0 im1, b1 im2] at hm
    rw [b0 i1, b1 i0] at hp
    rw [b0 i0, b1 im1, b1 i0] at hc
    have hmN : D0 im1 = D1 im2 := ENat.natCast_inj.mp hm
    have hpN : D0 i1 = D1 i0 := ENat.natCast_inj.mp hp
    have hcN : D0 i0 = min (D1 im1) (1 + D1 i0) := by
      rw [← ENat.natCast_one, ← ENat.natCast_add, ← enat_min_cast] at hc
      exact ENat.natCast_inj.mp hc
    have hcZ : (D0 i0 : ℤ) = min (D1 im1 : ℤ) (1 + (D1 i0 : ℤ)) := by
      exact_mod_cast hcN
    apply Prod.ext <;> dsimp only <;> omega
  · intro hw
    have hm := leftStep_sdp_leftBoundary w h0 h1 hw z hz
      (by simpa only [boundaryVertex_zero] using hr1 0 i0.property)
    have hp := leftStep_sdp_rightBoundary w h0 h1 hw z hz
      (by simpa only [boundaryVertex_one] using hr1 1 i1.property)
    have hc := leftStep_sdp_rootBoundary w h0 h1 hw z hz
    have hm' : sdp (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w)
        (shiftLimitVertex w 1 z) =
        sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ : PresentVertex _) z := by
      simpa only [boundaryVertex_zero] using hm
    have hp' : sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w)
        (shiftLimitVertex w 1 z) =
        sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 1⟩ : PresentVertex _) z := by
      simpa only [boundaryVertex_one] using hp
    rw [b0 im1, b1 i0] at hm'
    rw [b0 i1, b1 i1] at hp'
    rw [b0 i0, b1 i1] at hc
    have hmN : D0 im1 = D1 i0 := ENat.natCast_inj.mp hm'
    have hpN : D0 i1 = D1 i1 := ENat.natCast_inj.mp hp'
    have hcN : D0 i0 = 1 + D1 i1 := by exact_mod_cast hc
    apply Prod.ext <;> dsimp only <;> omega
  · intro hw
    obtain ⟨hm, hc, hp⟩ := upStep_sdp_boundary w h0 h1 hw z hz
    rw [b0 im1, b1 im1] at hm
    rw [b0 i1, b1 i2] at hp
    rw [b0 i0, b1 i0, b1 i2] at hc
    have hmN : D0 im1 = D1 im1 := ENat.natCast_inj.mp hm
    have hpN : D0 i1 = D1 i2 := ENat.natCast_inj.mp hp
    have hcN : D0 i0 = min (D1 i0) (1 + D1 i2) := by
      rw [← ENat.natCast_one, ← ENat.natCast_add, ← enat_min_cast] at hc
      exact ENat.natCast_inj.mp hc
    have hcZ : (D0 i0 : ℤ) = min (D1 i0 : ℤ) (1 + (D1 i2 : ℤ)) := by
      exact_mod_cast hcN
    apply Prod.ext <;> dsimp only <;> omega

private theorem sdp_busemann_unique (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {X Y : ℤ → ℤ}
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hY : IsBoundaryBusemannSDP (boundaryPresentVertex w h) Y) : X = Y := by
  funext k
  obtain ⟨y, hy, hr⟩ := boundaryEnumeration_commonSequence w h 0 k
  obtain ⟨N, hN⟩ := hX.2 0 k y hy hr
  obtain ⟨M, hM⟩ := hY.2 0 k y hy hr
  have hx := hN (max N M) (Nat.le_max_left _ _)
  have hy' := hM (max N M) (Nat.le_max_right _ _)
  rw [hX.1, sub_zero] at hx
  rw [hY.1, sub_zero] at hy'
  exact hx.trans hy'.symm

/-- Almost-sure iid-code helper for `lem:SDP-relating-X1-X` and
`w i = ω (i + 1)` represents the first map, and `w (1 + i)` the second.
The first step is `ω 1`: codes `0`, `1`, `2` mean `(-1,0)`, `(0,1)`,
`(1,-1)`. Both normalized SDP Busemann functions exist uniquely. -/
theorem iidCodes_ae_sdp_relating_X1_X :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
      ∃ X0 X1 : ℤ → ℤ,
        IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0 ∧
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => w (1 + i)) h1) X1 ∧
        (∀ X0' : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0' → X0' = X0) ∧
        (∀ X1' : ℤ → ℤ,
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1' → X1' = X1) ∧
        (ω 1 = 2 → (X0 (-1), X0 1) =
          (X1 (-2) - min (X1 (-1)) 1, -min (X1 (-1)) 1)) ∧
        (ω 1 = 0 → (X0 (-1), X0 1) = (-X1 1 - 1, -1)) ∧
        (ω 1 = 1 → (X0 (-1), X0 1) =
          (X1 (-1) - min 0 (X1 2 + 1), X1 2 - min 0 (X1 2 + 1))) := by
  filter_upwards [iidCodes_ae_boundaryBusemannSDP_commonFarVertex] with ω hω
  obtain ⟨h0, h1, X0, X1, hX0, hX1, z, hz, hr0, hr1, hc0, hc1⟩ := hω
  refine ⟨h0, h1, X0, X1, hX0, hX1,
    (fun X0' hX0' => sdp_busemann_unique _ h0 hX0' hX0),
    (fun X1' hX1' => sdp_busemann_unique _ h1 hX1' hX1), ?_⟩
  have h1' : BoundaryHitWitnesses (fun i => ω ((i + 1) + 1)) := by
    simpa only [Nat.add_comm] using h1
  have hr1' : ∀ k : ℤ, k ∈ Set.Icc (-2 : ℤ) 2 →
      Reachable (⟨boundaryVertex (fun i => ω ((i + 1) + 1)) h1' k⟩ :
        PresentVertex (fun i => ω ((1 + i) + 1))) z := by
    intro k hk
    simpa only [boundaryPresentVertex, Nat.add_comm] using
      hr1 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk)
  apply firstStep_boundary_pair_of_common_vertex_sdp (fun i => ω (i + 1)) h0 h1'
    z hz (fun k hk => hr0 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk))
    hr1' X0 X1 hX0.1 hX1.1
  constructor
  · intro k k' hk hk'
    exact hc0 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk)
      k' (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk')
  · intro k k' hk hk'
    simpa only [Nat.add_comm, boundaryPresentVertex] using
      hc1 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk)
        k' (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk')

/-- Simultaneous iid-code helper for `lem:SDP-relating-X1-X`,
almost-sure event supports both functions and the formulas for every pair
satisfying the SDP characterizations. Uniqueness identifies the pairs. -/
theorem iidCodes_ae_sdp_relating_X1_X_all :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
        (∃ X0 : ℤ → ℤ, IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0) ∧
        (∃ X1 : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => w (1 + i)) h1) X1) ∧
        ∀ X0' X1' : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0' →
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1' →
          (ω 1 = 2 → (X0' (-1), X0' 1) =
            (X1' (-2) - min (X1' (-1)) 1, -min (X1' (-1)) 1)) ∧
          (ω 1 = 0 → (X0' (-1), X0' 1) = (-X1' 1 - 1, -1)) ∧
          (ω 1 = 1 → (X0' (-1), X0' 1) =
            (X1' (-1) - min 0 (X1' 2 + 1), X1' 2 - min 0 (X1' 2 + 1))) := by
  filter_upwards [iidCodes_ae_sdp_relating_X1_X] with ω hω
  obtain ⟨h0, h1, X0, X1, hX0, hX1, hu0, hu1, hp⟩ := hω
  refine ⟨h0, h1, ⟨X0, hX0⟩, ⟨X1, hX1⟩, ?_⟩
  intro X0' X1' hX0' hX1'
  obtain rfl := hu0 X0' hX0'
  obtain rfl := hu1 X1' hX1'
  exact hp

end DirectedDistances.Recursive
