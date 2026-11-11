module

public import DirectedDistances.KMSW.WholePlaneFreshness

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
L-records are fresh in the extension; not the paper result.

The record predicate is the closed-prefix minimum used by D6: it allows ties at the
current time. A left step from this level creates a strict new minimum at the next time.
The prefix-floor certificate below therefore uses a weak inequality, including at `s`. -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
L-records are fresh in the extension; not the paper result.
Extracts D6's residual-stack argument for an arbitrary extension word. -/
theorem kmswWindowPatchData_A_eq_nil_of_global_record
    (w : ℕ → Fin 3) (s k : ℕ)
    (hrecord : minL w (s + k) = L w (s + k)) :
    (kmswWindowPatchData w s k).A = [] := by
  have hlen := kmswStage_UL_length w (s + k)
  rw [hrecord] at hlen
  have hrel := kmswWindowPatchData_rel w s k
  have hlength := congrArg List.length hrel.ul
  have hpos := List.length_pos_of_ne_nil
    (kmswStage_UL_nonempty_active_last (fun i => w (s + i)) k).1
  simp only [List.length_append, List.length_map] at hlength
  exact List.length_eq_zero_iff.mp (by omega)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
L-records are fresh in the extension; not the paper result.
The left-record certificate concerns the extension, while the down-step condition
remains a condition on the window. -/
theorem kmswWindowPatchVertexMap_fresh_of_global_seams
    (u : ℕ → Fin 3) (m v : ℕ)
    (hv : v < (kmswStage u m).nextVertex) (hbase : 2 ≤ v)
    (w : ℕ → Fin 3) (s : ℕ) (hcode : ∀ i < m, w (s + i) = u i)
    (hseam : ∀ k < m, v = (kmswStage u k).nextVertex →
      (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ []) ∧
      (kmswCodeStep (u k) = .left →
        (kmswStage u k).UL.dropLast.reverse ≠ [] ∨
          minL w (s + k) = L w (s + k))) :
    (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
  have hstage (k : ℕ) (hk : k ≤ m) :
      kmswStage (fun i => w (s + i)) k = kmswStage u k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        change kmswStep (kmswStage (fun i => w (s + i)) k) (w (s + k)) =
          kmswStep (kmswStage u k) (u k)
        rw [ih (by omega), hcode k (by omega)]
  have hv' : v < (kmswStage (fun i => w (s + i)) m).nextVertex := by
    rw [hstage m le_rfl]
    exact hv
  by_contra hfresh
  have hseam' := (kmswWindowPatchVertexMap_lt_start_iff_seam w s m v hv').mp
    (Nat.lt_of_not_ge hfresh)
  rcases hseam' with hsmall | ⟨k, hk, hcreate, hdown | hleft⟩
  · omega
  · rw [hstage k (by omega)] at hcreate hdown
    rw [hcode k hk] at hdown
    exact ((hseam k hk hcreate).1 hdown.1) hdown.2.1
  · rw [hstage k (by omega)] at hcreate hleft
    rw [hcode k hk] at hleft
    rcases (hseam k hk hcreate).2 hleft.1 with hnonseam | hglobal
    · exact hnonseam hleft.2.1
    · exact hleft.2.2 (by
        rw [kmswWindowPatchData_A_eq_nil_of_global_record w s k hglobal]
        rfl)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
L-records are fresh in the extension; not the paper result.
A window closed-prefix record and a weak floor on the prefix through `s` give
the exact global record predicate used above. The window letters before `k`
cover all coordinate indices from `s` through `s + k`, including both endpoints. -/
theorem kmswWindow_global_record_of_prefix_floor
    (u w : ℕ → Fin 3) (s k : ℕ)
    (hcode : ∀ i < k, w (s + i) = u i)
    (hrecord : (kmswStage u k).UL.dropLast.reverse = [])
    (hfloor : ∀ j ≤ s, L w (s + k) ≤ L w j) :
    minL w (s + k) = L w (s + k) := by
  have hwindow : minL u k = L u k := by
    have hlen := kmswStage_UL_length u k
    have hpos := List.length_pos_of_ne_nil (kmswStage_UL_nonempty_active_last u k).1
    have hz := congrArg List.length hrecord
    simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hz
    omega
  have hL (n : ℕ) (hn : n ≤ k) : L w (s + n) = L w s + L u n := by
    unfold L
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcode i (by have := Finset.mem_range.mp hi; omega)]
  apply le_antisymm (runningMin_le _ _ _ le_rfl)
  obtain ⟨j, hj, heq⟩ := runningMin_attained (L w) (s + k)
  change minL w (s + k) = L w j at heq
  change L w (s + k) ≤ minL w (s + k)
  rw [heq]
  by_cases hjs : j ≤ s
  · exact hfloor j hjs
  · have hjshift : j = s + (j - s) := by omega
    have hmin := runningMin_le (L u) k (j - s) (by omega)
    change minL u k ≤ L u (j - s) at hmin
    rw [hwindow] at hmin
    rw [hjshift, hL k le_rfl, hL (j - s) (by omega)]
    omega

end DirectedDistances.KMSW
