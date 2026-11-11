module

public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.CutSeparationAnyStart
public import DirectedDistances.KMSW.NoMissingEdgesAE

/-! # Source and sink properties of present KMSW edges

Reachability is proved from finite-stage births. Only present edge IDs are arrows;
vertex assertions are restricted to allocated IDs. -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory
open DirectedDistances.RandomWalk

private theorem left_not_fresh (w : ℕ → Fin 3) (hL : ∀ j, 0 ≤ L w j)
    (n : ℕ) (hw : w n = 0) : (kmswStage w n).UL.dropLast.reverse ≠ [] := by
  intro hf
  have hlen := congrArg List.length hf
  simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hlen
  have hcount := kmswStage_UL_length w n
  obtain ⟨j, _, hj⟩ := runningMin_attained (L w) n
  have hm : 0 ≤ minL w n := by change 0 ≤ runningMin (L w) n; rw [hj]; exact hL j
  have hm0 := runningMin_le (L w) n 0 (Nat.zero_le n)
  change minL w n ≤ L w 0 at hm0
  have hz : L w 0 = 0 := rfl
  have hnext := hL (n + 1)
  have hstep : L w (n + 1) = L w n +
      (lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  rw [hw, lazyTwoDimensionalStep_zero] at hstep
  omega

private theorem reach_via_stage_edge (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present e = true)
    (hr : Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).west e⟩) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).east e⟩ := by
  obtain ⟨p⟩ := hr
  have hends := edge_endpoints_eq w he
  exact ⟨p.cons ⟨e, ⟨n, he, hp⟩, hends.1.symm, hends.2.symm⟩⟩

/-- Every finite-stage allocated vertex is reachable from the initial root -/
theorem allocated_stage_reachable_from_zero (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (n v : ℕ) (hv : v < (kmswStage w n).nextVertex) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩ := by
  induction n generalizing v with
  | zero =>
    have hv' : v < 2 := hv
    have hr : Reachable (⟨0⟩ : PresentVertex w) ⟨1⟩ :=
      reach_via_stage_edge w 0 0 (by change 0 < 1; omega) rfl (Reachable.refl _)
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · exact Reachable.refl _
    · exact hr
  | succ n ih =>
    have hb := kmswStage_endpoints_lt_nextVertex w n (act w n)
      (act_lt_nextEdge w le_rfl)
    by_cases hold : v < (kmswStage w n).nextVertex
    · exact ih v hold
    · by_cases h0 : w n = 0
      · have hf := left_not_fresh w hL n h0
        cases hs : (kmswStage w n).UL.dropLast.reverse with
        | nil => exact (hf hs).elim
        | cons e es =>
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
            kmswStepOfStep, hs, State.addEdge] at hv
          exact (hold hv).elim
      · by_cases h1 : w n = 1
        · have hvnew : v = (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
              State.addEdge] at hv
            omega
          subst v
          have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
          have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
          have hr := reach_via_stage_edge w (n + 1) (kmswStage w n).nextEdge he hp
          have hw : (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
              (kmswStage w n).west (act w n) := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge, act]
          have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
              (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
          rw [hw, ht] at hr
          exact hr (ih _ hb.1)
        · cases hs : (kmswStage w n).UR with
          | cons e es =>
            simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ite_false,
              kmswStepOfStep, hs] at hv
            exact (hold hv).elim
          | nil =>
            have hvnew : v = (kmswStage w n).nextVertex := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
                hs, State.addEdge] at hv
              omega
            subst v
            have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep, hs,
                State.addEdge]
            have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep, hs,
                State.addEdge]
            have hr := reach_via_stage_edge w (n + 1) (kmswStage w n).nextEdge he hp
            have hw : (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
                (kmswStage w n).east (act w n) := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep, hs,
                State.addEdge, act]
            have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
                (kmswStage w n).nextVertex := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep, hs,
                State.addEdge]
            rw [hw, ht] at hr
            exact hr (ih _ hb.2)

/-- Every allocated vertex is reachable from the initial root vertex by -/
theorem allocated_vertex_reachable_from_zero (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩ := by
  obtain ⟨n, hn⟩ := hv
  exact allocated_stage_reachable_from_zero w hL n v hn

/-- The initial root vertex has no incoming present edge -/
theorem zero_no_incoming_present_edge (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (e : ℕ) (he : EdgePresent w e) :
    edgeEast w e ≠ 0 := by
  intro hend
  obtain ⟨n, hn, hp⟩ := he
  have hb := (kmswStage_endpoints_lt_nextVertex w n e hn).1
  rw [(edge_endpoints_eq w hn).1] at hb
  obtain ⟨p⟩ := allocated_vertex_reachable_from_zero w hL (edgeWest w e) ⟨n, hb⟩
  let a : (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨0⟩ :=
    ⟨e, ⟨n, hn, hp⟩, rfl, hend⟩
  have hz := presentVertex_acyclic w (⟨0⟩ : PresentVertex w) (p.cons a)
  simp only [Path.length_cons] at hz
  omega

/-- Every allocated vertex other than the initial root vertex has an incoming -/
theorem allocated_vertex_has_incoming_present_edge (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) (hne : v ≠ 0) :
    ∃ e, EdgePresent w e ∧ edgeEast w e = v := by
  obtain ⟨p⟩ := allocated_vertex_reachable_from_zero w hL v hv
  cases p with
  | nil => exact (hne rfl).elim
  | cons p e => exact ⟨e.val, e.property.1, e.property.2.2⟩

/-- Among allocated vertices, the unique source is the initial root vertex.
Missing geometric edges have no role in this criterion -/
theorem allocated_vertex_source_iff_zero (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    (¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔ v = 0 := by
  constructor
  · intro hs
    by_contra hne
    exact hs (allocated_vertex_has_incoming_present_edge w hL v hv hne)
  · rintro rfl ⟨e, he, hend⟩
    exact zero_no_incoming_present_edge w hL e he hend

/-- Under an unbounded-below right coordinate, every allocated vertex has an
producer explicitly supplies presence, including for its first edge. -/
theorem allocated_vertex_outgoing_present_edge (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    ∃ e, EdgePresent w e ∧ edgeWest w e = v := by
  obtain ⟨e, _, _, hstart, hp⟩ :=
    allocated_vertex_has_infinite_path_of_R_unbounded w hR v hv
  exact ⟨e 0, hp 0, hstart⟩

/-- Almost surely the present-edge orientation is acyclic, has unique source
zero among allocated vertices, and has no allocated sink -/
theorem pitmanCodes_ae_source_and_no_sink :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      acyclic (PresentVertex w) ∧
      (∀ v : ℕ, (∃ n, v < (kmswStage w n).nextVertex) →
        ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔ v = 0)) ∧
      (∀ v : ℕ, (∃ n, v < (kmswStage w n).nextVertex) →
        ∃ e, EdgePresent w e ∧ edgeWest w e = v) := by
  filter_upwards [pitmanCodes_ae_R_unbounded_below] with ω hR
  let w := pitmanCode (fun i => ω (i + 1))
  have hL : ∀ j, 0 ≤ L w j := by
    intro j
    rw [kmsw_L_eq]
    exact integrateCodes_pitmanCode_fst_nonneg _ j
  have hR' : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hR a
    exact ⟨n, by rw [kmsw_R_eq]; exact hn⟩
  exact ⟨presentVertex_acyclic w,
    fun v hv => allocated_vertex_source_iff_zero w hL v hv,
    fun v hv => allocated_vertex_outgoing_present_edge w hR' v hv⟩

end DirectedDistances.KMSW
