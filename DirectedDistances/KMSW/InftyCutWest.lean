module

public import DirectedDistances.KMSW.LLBoundaryPersistent

/-! # The west boundary at a first left-coordinate hit

Helpers for the west side of P3 in the proof strategy for `lem-infty-cut`
finite-stage UL list is the singleton active edge, whose west endpoint
is `x_{-K}`. The finite-stage missing LL edges include those indexed by
`-K ≤ j ≤ -1`; further west edges, indexed by `j < -K`, are created at later
first hits. All these missing edges join `x_j` to `x_{j+1}`. This file proves only this P3
ingredient, not P3 and not `lem-infty-cut`. An earlier proposed claim that every UL edge at the hit time
is a missing LL edge is false: at a first left hit, UL is the single active
frontier edge, while the missing west boundary edges identified here lie in the
LL list. The boundary indexing is
left-boundary/source facts are from `lem-uibot-bdy` -/

public section
namespace DirectedDistances.KMSW

open Quiver

private theorem leftHit_strict_record_local (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k, k < L w j := by
  let τ := boundaryHitTime w h k
  have hfind : τ = Nat.find (h.leftHit k hk) := by
    dsimp [τ, boundaryHitTime]
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  have hzero : L w 0 = 0 := by simp [L]
  have hstep : ∀ n, L w n - 1 ≤ L w (n + 1) := by
    intro n
    have hsum : L w (n + 1) = L w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
    have hlow : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
      change -1 ≤ ((w n).val : ℤ) - 1
      have hv := (w n).isLt
      omega
    rw [hsum]
    omega
  intro j hj
  induction j with
  | zero => rw [hzero]; omega
  | succ j ih =>
    have hjτ : j < τ := by omega
    have hprev := ih hjτ
    have hnot : L w (j + 1) ≠ k := by
      intro heq
      have hjfind : j + 1 < Nat.find (h.leftHit k hk) := by
        have hjτ : j + 1 < τ := by omega
        rw [← hfind]
        exact hjτ
      exact (Nat.find_min (h.leftHit k hk) hjfind) heq
    have hnext := hstep j
    omega

/-- At the first left-coordinate hit, the UL list contains only the active
edge, and that edge starts at `x_k` (`eqn-bdy-vertex-hit`,
frontier exactly; the missing west boundary is the LL chain. P3 ingredient -/
theorem leftHit_UL_singleton_and_west_endpoint (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    let τ := boundaryHitTime w h k
    (kmswStage w τ).UL = [act w τ] ∧
      (kmswStage w τ).west (act w τ) = boundaryVertex w h k := by
  let τ := boundaryHitTime w h k
  have hhit : L w τ = k := by
    exact boundaryHitTime_left_spec w h hk
  have hmin_le : minL w τ ≤ k := by
    have hle := runningMin_le (L w) τ τ le_rfl
    change minL w τ ≤ L w τ at hle
    omega
  have hmin_ge : k ≤ minL w τ := by
    obtain ⟨i, hi, hmin⟩ := runningMin_attained (L w) τ
    change minL w τ = L w i at hmin
    have hik : k ≤ L w i := by
      by_cases hiτ : i = τ
      · subst i
        omega
      · exact le_of_lt (leftHit_strict_record_local w h hk i (by omega))
    rw [hmin]
    exact hik
  have hmin : minL w τ = k := by omega
  have hlenZ : ((kmswStage w τ).UL.length : ℤ) = 1 := by
    rw [kmswStage_UL_length, hhit, hmin]
    ring
  have hlen : (kmswStage w τ).UL.length = 1 := by exact_mod_cast hlenZ
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w τ
  have hxsLen : xs.length = 0 := by
    rw [hxs] at hlen
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  have hxsNil : xs = [] := List.length_eq_zero_iff.mp hxsLen
  have hUL : (kmswStage w τ).UL = [act w τ] := by
    rw [hxs, hxsNil]
    rfl
  have hwest : (kmswStage w τ).west (act w τ) = boundaryVertex w h k := by
    calc
      (kmswStage w τ).west (act w τ) = activeInitial w τ :=
        (CutConverse.activeInitial_eq w τ).symm
      _ = boundaryVertex w h k := (boundaryVertex_left_hit_eq w h hk).symm
  exact ⟨hUL, hwest⟩




theorem leftBoundary_edge_missing_at_leftHit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k j : ℤ} (hk : k ≤ -1)
    (hkj : k ≤ j) (hj : j ≤ -1) :
    let τ := boundaryHitTime w h k
    let e := kmswLLCreatedEdge w (boundaryHitTime w h j)
    e ∈ (kmswStage w τ).LL ∧
      (kmswStage w τ).present e = false ∧
      (kmswStage w τ).west e = boundaryVertex w h j ∧
      (kmswStage w τ).east e = boundaryVertex w h (j + 1) := by
  let τk := boundaryHitTime w h k
  let τj := boundaryHitTime w h j
  have htime : τj ≤ τk := by
    by_contra hnot
    have hlt : τk < τj := by omega
    have hrecord := leftHit_strict_record_local w h hj τk hlt
    change j < L w (boundaryHitTime w h k) at hrecord
    have hhit := boundaryHitTime_left_spec w h hk
    omega
  have hpersist := boundary_left_edge_persistent w h hj
  change kmswLLCreatedEdge w τj < (kmswStage w τj).nextEdge ∧
    ∀ n, τj ≤ n → kmswLLCreatedEdge w τj ∈ (kmswStage w n).LL ∧
      (kmswStage w n).present (kmswLLCreatedEdge w τj) = false ∧
      (kmswStage w n).west (kmswLLCreatedEdge w τj) = boundaryVertex w h j ∧
      (kmswStage w n).east (kmswLLCreatedEdge w τj) = boundaryVertex w h (j + 1) at hpersist
  rcases hpersist with ⟨_, hpersist⟩
  simpa [τk, τj] using hpersist τk htime

private theorem path_source_vertex_eq_start {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) (x : PresentVertex w)
    (hxsource : ¬ ∃ e, EdgePresent w e ∧ edgeEast w e = x.id)
    (hx : x ∈ p.vertices) : x = a := by
  induction p with
  | nil =>
    simpa only [Quiver.Path.vertices_nil, List.mem_singleton] using hx
  | @cons a' b' p e ih =>
    rcases (Quiver.Path.mem_vertices_cons p e).mp hx with hx | hxend
    · exact ih hx
    · have hid : x.id = edgeEast w e.val := by
        rw [hxend]
        exact e.property.2.2.symm
      exact (hxsource ⟨e.val, e.property.1, hid.symm⟩).elim

/-- A path from `x_ell`, where `ell ≥ -K`, can contain a west-boundary
source `x_j` with `j ≤ -K` only when `j = ell`. This uses the source clause of
`lem-uibot-bdy` and injectivity of the `eqn-bdy-vertex-hit` indexing -/
theorem leftBoundary_path_vertex_index_eq_start (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) {ell j : ℤ}
    (hjk : j ≤ -(K : ℤ))
    {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h ell⟩ : PresentVertex w) v)
    (hmem : (⟨boundaryVertex w h j⟩ : PresentVertex w) ∈ p.vertices) :
    j = ell := by
  have hj0 : j ≤ 0 := by omega
  have hno : ¬ ∃ e, EdgePresent w e ∧
      edgeEast w e = (boundaryVertex w h j) := by
    rintro ⟨e, he, hend⟩
    exact (boundaryVertex_nonpos_no_incoming w h hj0 e he hend).elim
  have hstart := path_source_vertex_eq_start p
    (⟨boundaryVertex w h j⟩ : PresentVertex w) hno hmem
  have hids := congrArg PresentVertex.id hstart
  exact boundaryVertex_injective w h hids

/-- If `ell > -K`, no vertex `x_j` with `j ≤ -K` occurs on a path from
`x_ell`; if `ell = -K`, the only such boundary vertex that can occur is its
initial vertex `x_{-K}`, which does occur. This is the exact endpoint case
split in the west-source obstruction (`lem-uibot-bdy`, -/
theorem leftBoundary_path_vertex_cases (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) {ell : ℤ}
    (hell : -(K : ℤ) ≤ ell) {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h ell⟩ : PresentVertex w) v) :
    (-(K : ℤ) < ell → ∀ j ≤ -(K : ℤ),
      (⟨boundaryVertex w h j⟩ : PresentVertex w) ∉ p.vertices) ∧
    (ell = -(K : ℤ) → ∀ j : ℤ, j ≤ -(K : ℤ) →
      ((⟨boundaryVertex w h j⟩ : PresentVertex w) ∈ p.vertices ↔
        j = -(K : ℤ))) := by
  constructor
  · intro hstrict j hj hmem
    have hidx := leftBoundary_path_vertex_index_eq_start w h K hj p hmem
    omega
  · intro heq j hj
    constructor
    · intro hmem
      have hidx := leftBoundary_path_vertex_index_eq_start w h K hj p hmem
      omega
    · intro hidx
      subst j
      subst ell
      exact Quiver.Path.start_mem_vertices p

/-- Almost surely under the iid one-sided code law, all finite-stage west LL
edges with index `-K ≤ j ≤ -1` are missing at the first hit of `L=-K`,
simultaneously for all positive `K`. The witness convention is `w i = ω (i+1)`, as in
ingredient only, not P3 or `lem-infty-cut` -/
theorem iidCodes_ae_leftBoundary_edges_at_leftHit :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ K : ℕ, 0 < K → ∀ j : ℤ, -(K : ℤ) ≤ j → j ≤ -1 →
          let τ := boundaryHitTime (fun i => ω (i + 1)) h (-(K : ℤ))
          let e := kmswLLCreatedEdge
            (fun i => ω (i + 1))
            (boundaryHitTime (fun i => ω (i + 1)) h j)
          e ∈ (kmswStage (fun i => ω (i + 1)) τ).LL ∧
            (kmswStage (fun i => ω (i + 1)) τ).present e = false ∧
            (kmswStage (fun i => ω (i + 1)) τ).west e =
              boundaryVertex (fun i => ω (i + 1)) h j ∧
            (kmswStage (fun i => ω (i + 1)) τ).east e =
              boundaryVertex (fun i => ω (i + 1)) h (j + 1) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  refine ⟨h, ?_⟩
  intro K hK j hkj hj
  exact leftBoundary_edge_missing_at_leftHit (fun i => ω (i + 1)) h
    (k := -(K : ℤ)) (j := j) (by omega) hkj hj

end DirectedDistances.KMSW
