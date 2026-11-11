module

public import DirectedDistances.KMSW.KMSWWindowActiveRoot
public import DirectedDistances.KMSW.KMSWWindowGlobalSeamFresh
public import DirectedDistances.KMSW.KMSWWindowRelaxedCapture
public import DirectedDistances.KMSW.KMSWWindowSeamLevel
public import DirectedDistances.RandomWalk.DiskPrefixDipBound

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
identification on the bounded-seam window event without prefix dip; not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
identification on the bounded-seam window event without prefix dip; not the paper result.
The disk prefix-dip event at the first hit time. -/
@[expose] def DiskDip (N K0 : ℕ) (p : (ℕ → Fin 3) × ℕ) : Prop :=
  ∃ j, j + N < (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
    (codeWalk p.1 j).1 ≤
      (codeWalk p.1 (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat).1 + (K0 : ℤ)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
identification on the bounded-seam window event without prefix dip; not the paper result.
This identifies `DiskDip` with the first-hit event bounded in `diskPrefixDip_small`. -/
theorem DiskDip_iff_diskPrefixDip (N K0 : ℕ) (p : (ℕ → Fin 3) × ℕ) :
    DiskDip N K0 p ↔
      ∃ T : ℕ, codeFstFirstHit (-(p.2 : ℤ)) p.1 = T ∧
        ∃ j : ℕ, j + N < T ∧
          (codeWalk p.1 j).1 ≤ (codeWalk p.1 T).1 + (K0 : ℤ) := by
  unfold DiskDip
  constructor
  · rintro ⟨j, hj, hlevel⟩
    cases ht : codeFstFirstHit (-(p.2 : ℤ)) p.1 with
    | top => simp [ht] at hj
    | coe T =>
      refine ⟨T, ?_, j, ?_, ?_⟩
      · rfl
      · simpa [ht] using hj
      · simpa [ht] using hlevel
  · rintro ⟨T, hT, j, hj, hlevel⟩
    have htoNat : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat = T := by
      rw [hT]
      rfl
    refine ⟨j, ?_, ?_⟩
    · simpa [htoNat] using hj
    · simpa [htoNat] using hlevel

private theorem disk_window_valid {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

private theorem disk_window_code {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    ∀ i < 2 * N,
      (fun j => p.1 (j + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + i) =
        windowCodeDecode N x i := by
  intro i hi
  exact (windowCodeDecode_bridge h i hi).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
identification on the bounded-seam window event without prefix dip; not the paper result.
Every left seam in the window is a global record in the disk code. -/
theorem kmswDiskSeam_hglob_of_noDip {n N : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) (r c K0 : ℕ)
    (hK : kmswBallLeftSeamKmax (windowCodeDecode N x) (2 * N) r c N ≤ K0)
    (hnd : ¬ DiskDip N K0 p) :
    ∀ k ∈ kmswBallLeftSeamSet (windowCodeDecode N x) (2 * N) r c,
      minL (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + k) =
        L (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + k) := by
  classical
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  have hvalid := disk_window_valid h
  have hcode : ∀ i < 2 * N, w (s + i) = u i := by
    intro i hi
    exact disk_window_code h i hi
  have hK' := (kmswBallLeftSeamKmax_le_iff u (2 * N) r c N K0).mp hK
  have hnot : ¬ (∃ j, j + N < T ∧
      (codeWalk p.1 j).1 ≤ (codeWalk p.1 T).1 + (K0 : ℤ)) := by
    simpa [DiskDip, T] using hnd
  intro k hk
  have hkrange : k < 2 * N := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  unfold kmswBallLeftSeamSet at hk
  rcases Finset.mem_filter.mp hk with ⟨_, ⟨_, _, hrecord⟩⟩
  change (kmswStage u k).UL.dropLast.reverse = [] at hrecord
  have hwindow : minL u k = L u k := by
    have hlen := kmswStage_UL_length u k
    have hpos := List.length_pos_of_ne_nil
      (kmswStage_UL_nonempty_active_last u k).1
    have hz := congrArg List.length hrecord
    simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hz
    omega
  have hmin := runningMin_le (L u) k 0 (by omega)
  change minL u k ≤ L u 0 at hmin
  have hLzero : L u 0 = 0 := by simp [L]
  have hminzero : L u k ≤ 0 := by
    calc
      L u k = minL u k := hwindow.symm
      _ ≤ L u 0 := hmin
      _ = 0 := hLzero
  have hseam := hK' k hk
  have hfloor : ∀ j ≤ s, L w (s + k) ≤ L w j := by
    intro j hjs
    by_cases hjs' : j = s
    · subst j
      have hadd := L_window_additivity u w s (2 * N) k
        hkrange.le hcode
      have hadd' : L w (s + k) = L w s + L u k := by omega
      rw [hadd']
      omega
    · have hlt : j < s := by omega
      have hjsN : j + N < T := by
        dsimp [s] at hlt
        omega
      have hstrict : (codeWalk p.1 j).1 > (codeWalk p.1 T).1 + (K0 : ℤ) := by
        by_contra hle
        apply hnot
        exact ⟨j, hjsN, le_of_not_gt hle⟩
      have hjcode : L w j = (codeWalk p.1 j).1 := by
        simpa [w] using L_shift_eq_codeWalk_fst p.1 j
      have hTcode : L w T = (codeWalk p.1 T).1 := by
        simpa [w] using L_shift_eq_codeWalk_fst p.1 T
      have haddk := L_window_additivity u w s (2 * N) k
        hkrange.le hcode
      have haddN := L_window_additivity u w s (2 * N) N (by omega) hcode
      have hsN : s + N = T := by dsimp [s, T]; omega
      rw [hsN] at haddN
      have hcalc : L w (s + k) = L w T + (L u k - L u N) := by omega
      calc
        L w (s + k) = L w T + (L u k - L u N) := hcalc
        _ ≤ L w T + (K0 : ℤ) := by omega
        _ ≤ L w j := le_of_lt (by rw [hTcode, hjcode]; omega)
  have hcodek : ∀ i < k, w (s + i) = u i := fun i hi => hcode i (hi.trans hkrange)
  exact kmswWindow_global_record_of_prefix_floor u w s k hcodek hrecord hfloor

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
identification on the bounded-seam window event without prefix dip; not the paper result.
The disk ball at the first-hit root is the image of the decoded window ball. -/
theorem diskBall_eq_image_of_eventK_noDip {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) (n' : ℕ)
    (hn' : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n') :
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let w := fun i => p.1 (i + 1)
    kmswStageBallVertices (fun _ _ => True) (kmswStage w n') r (activeInitial w T) =
      (kmswStageBallVertices (fun _ _ => True)
        (kmswStage (windowCodeDecode N x) (2 * N)) r
        (activeInitial (windowCodeDecode N x) N)).image
          (kmswWindowPatchVertexMap w (T - N) (2 * N)) := by
  dsimp only
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  have hvalid := disk_window_valid h
  have hcode : ∀ i < 2 * N, w (s + i) = u i := by
    intro i hi
    exact disk_window_code h i hi
  have hglob := kmswDiskSeam_hglob_of_noDip h r (activeInitial u N) K0 hev.2 hnd
  have hroot : kmswWindowPatchVertexMap w s (2 * N) (activeInitial u N) =
      activeInitial w T := by
    have hcodeN : ∀ i < N, w (s + i) = u i := fun i hi => hcode i (by omega)
    have hstage : kmswStage (fun i => w (s + i)) N = kmswStage u N := by
      apply kmswStage_congr
      exact hcodeN
    have hbound : activeInitial u N <
        (kmswStage (fun i => w (s + i)) N).nextVertex := by
      rw [CutConverse.activeInitial_eq, hstage]
      exact (kmswStage_endpoints_lt_nextVertex u N (kmswStage u N).active
        (kmswStage_boundary_ids_lt_nextEdge u N).1).1
    calc
      kmswWindowPatchVertexMap w s (2 * N) (activeInitial u N) =
          kmswWindowPatchVertexMap w s N (activeInitial u N) :=
            kmswWindowPatchVertexMap_extends_le w s N (2 * N) (by omega)
              (activeInitial u N) hbound
      _ = activeInitial w (s + N) :=
            kmswWindowPatchVertexMap_activeInitial u w s N hcodeN
      _ = activeInitial w T := by
            congr 1
            dsimp [s, T]
            omega
  change kmswStageBallVertices (fun _ _ => True) (kmswStage w n') r
      (activeInitial w T) =
    (kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
      (activeInitial u N)).image (kmswWindowPatchVertexMap w s (2 * N))
  rw [← hroot]
  exact kmswDiskBallVertices_eq_image_future_rel h hev.1.1 hglob n' hn'

end DirectedDistances.KMSW
