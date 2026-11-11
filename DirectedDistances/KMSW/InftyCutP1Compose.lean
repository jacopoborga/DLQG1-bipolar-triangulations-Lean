module

public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.KMSW.InftyCutCore
import DirectedDistances.KMSW.InftyCutWest

/-! Supporting lemmas for paper labels `def-kmsw`, `lem-directed-contain`, `lem-infty-cut`, `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Composition of a hatted-model map with the shifted-limit embedding

using the containment setup of `lem-directed-contain` (87–120). H1 (allocated
injectivity and allocation preservation), H2 (path lifting), and H3 (rooted
range and root identification) are explicit open M-hat premises from
`lem-quad-kmsw` (525–537). This file does not discharge those premises or
prove either numbered lemma. The edge region retains present edge identities. -/

public section
namespace DirectedDistances.KMSW
open Quiver

private theorem step_vertex_growth_bound (s : State) (c : Fin 3) (n : ℕ)
    (h : n + s.UL.length + 2 * s.UR.length ≤ 4 * s.nextVertex) :
    n + 1 + (kmswStep s c).UL.length + 2 * (kmswStep s c).UR.length ≤
      4 * (kmswStep s c).nextVertex := by
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
    cases hUR : s.UR with
    | nil =>
      have hlen := congrArg List.length hUR
      simp only [List.length_nil] at hlen
      simp only [kmswStepOfStep, hUR, State.addEdge, List.length_append,
        List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUR
      simp only [List.length_cons] at hlen
      simp only [kmswStepOfStep, hUR, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | left =>
    cases hUL : s.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hUL, State.addEdge,
        List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUL
      simp only [List.length_reverse, List.length_dropLast, List.length_cons] at hlen
      simp only [kmswStepOfStep, hUL, State.addEdge, List.length_append,
        List.length_reverse, List.length_cons, List.length_nil]
      omega
  | up =>
    simp only [kmswStepOfStep, State.addEdge, List.length_append,
      List.length_dropLast, List.length_cons, List.length_nil]
    omega

private theorem stage_vertex_growth_bound (u : ℕ → Fin 3) (n : ℕ) :
    n + (kmswStage u n).UL.length + 2 * (kmswStage u n).UR.length ≤
      4 * (kmswStage u n).nextVertex := by
  induction n with
  | zero =>
    change 1 ≤ 8
    decide
  | succ n ih => exact step_vertex_growth_bound (kmswStage u n) (u n) n ih




theorem kmswVertexAllocated_all (u : ℕ → Fin 3) (a : PresentVertex u) :
    kmswVertexAllocated u a := by
  refine ⟨4 * a.id + 1, ?_⟩
  have h := stage_vertex_growth_bound u (4 * a.id + 1)
  omega

/-- Present edges whose activation time is at least the cutoff, for the second
containment setup of `lem-directed-contain` (87–120). -/
@[expose] def cutLateRegion (w : ℕ → Fin 3) (t : ℕ) : Set ℕ :=
  {e | ∃ he : EdgePresent w e, t ≤ actTime w e he}

/-- The existential and universal activation-time formulations agree on a -/
theorem mem_cutLateRegion_iff (w : ℕ → Fin 3) (t e : ℕ)
    (he : EdgePresent w e) :
    e ∈ cutLateRegion w t ↔ ∀ hf : EdgePresent w e, t ≤ actTime w e hf := by
  constructor
  · rintro ⟨_, ht⟩ _
    exact ht
  · intro ht
    exact ⟨he, ht he⟩

/-- C1: allocated injectivity of the composite. H1 is the open M-hat
injectivity/allocation obligation of `lem-quad-kmsw` -/
theorem shiftCompose_injective (u w : ℕ → Fin 3) (t : ℕ)
    (f₀ : PresentVertex u → PresentVertex (fun i => w (t + i)))
    (H1inj : ∀ {a b}, kmswVertexAllocated u a → kmswVertexAllocated u b →
      f₀ a = f₀ b → a = b)
    (H1alloc : ∀ a, kmswVertexAllocated u a →
      kmswVertexAllocated (fun i => w (t + i)) (f₀ a))
    {a b : PresentVertex u} (ha : kmswVertexAllocated u a)
    (hb : kmswVertexAllocated u b)
    (hab : shiftLimitVertex w t (f₀ a) = shiftLimitVertex w t (f₀ b)) : a = b := by
  exact H1inj ha hb (shiftLimitVertex_injective w t (H1alloc a ha) (H1alloc b hb) hab)

/-- C2: compose the late-path lift with the open H2 M-hat lift from
vertex-visit reflection used for P1 of `lem-infty-cut` (127–143), in the
containment setup of `lem-directed-contain` (87–120). H1alloc is also open. -/
theorem shiftCompose_late_path_lift (u w : ℕ → Fin 3) (t : ℕ)
    (f₀ : PresentVertex u → PresentVertex (fun i => w (t + i)))
    (H1alloc : ∀ a, kmswVertexAllocated u a →
      kmswVertexAllocated (fun i => w (t + i)) (f₀ a))
    (H2 : ∀ a, kmswVertexAllocated u a →
      ∀ {v} (q : Path (f₀ a) v),
        ∃ b : PresentVertex u, kmswVertexAllocated u b ∧
          ∃ r : Path a b, f₀ b = v ∧ ∀ y ∈ r.vertices, f₀ y ∈ q.vertices)
    (a : PresentVertex u) (ha : kmswVertexAllocated u a)
    {v : PresentVertex w} (q : Path (shiftLimitVertex w t (f₀ a)) v)
    (hlate : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e, t ≤ actTime w e he) :
    ∃ b : PresentVertex u, kmswVertexAllocated u b ∧
      ∃ r : Path a b, shiftLimitVertex w t (f₀ b) = v ∧
        ∀ y ∈ r.vertices, shiftLimitVertex w t (f₀ y) ∈ q.vertices := by
  obtain ⟨c, _, p, hc, _, hp⟩ :=
    shiftLimitVertex_late_path_lift w t (f₀ a) (H1alloc a ha) q hlate
  obtain ⟨b, hb, r, hbc, hr⟩ := H2 a ha p
  refine ⟨b, hb, r, (congrArg (shiftLimitVertex w t) hbc).trans hc, ?_⟩
  intro y hy
  exact hp (f₀ y) (hr y hy)

/-- C3: the rooted range of the composite on all late reachable vertices.
H3 is the open M-hat range obligation of `lem-quad-kmsw`
of `lem-infty-cut` (127–143) using `lem-directed-contain` (87–120). -/
theorem shiftCompose_late_range (u w : ℕ → Fin 3) (t : ℕ)
    (f₀ : PresentVertex u → PresentVertex (fun i => w (t + i)))
    (H3 : ∀ {v : PresentVertex (fun i => w (t + i))},
      Path (⟨0⟩ : PresentVertex (fun i => w (t + i))) v →
        ∃ b : PresentVertex u, kmswVertexAllocated u b ∧ f₀ b = v) :
    ∀ {v : PresentVertex w}
      (q : Path (⟨(kmswStage w t).west (act w t)⟩ : PresentVertex w) v),
      (∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e, t ≤ actTime w e he) →
        ∃ b : PresentVertex u, kmswVertexAllocated u b ∧
          shiftLimitVertex w t (f₀ b) = v := by
  rw [← shiftLimitVertex_root w t]
  intro v q hlate
  obtain ⟨c, _, p, hc, _, _⟩ := shiftLimitVertex_late_path_lift w t ⟨0⟩
    (kmswVertexAllocated_all _ _) q hlate
  obtain ⟨b, hb, hbc⟩ := H3 p
  exact ⟨b, hb, (congrArg (shiftLimitVertex w t) hbc).trans hc⟩

/-- C4: the total composite embedding. All vertex IDs are allocated by
`kmswVertexAllocated_all`; H1 remains the open M-hat obligation of
composition needed for `lem-infty-cut` (127–143). -/
@[expose] noncomputable def shiftComposeEmbedding (u w : ℕ → Fin 3) (t : ℕ)
    (f₀ : PresentVertex u → PresentVertex (fun i => w (t + i)))
    (H1inj : ∀ {a b}, kmswVertexAllocated u a → kmswVertexAllocated u b →
      f₀ a = f₀ b → a = b)
    (H1alloc : ∀ a, kmswVertexAllocated u a →
      kmswVertexAllocated (fun i => w (t + i)) (f₀ a)) :
    PresentVertex u ↪ PresentVertex w where
  toFun a := shiftLimitVertex w t (f₀ a)
  inj' _ _ hab := shiftCompose_injective u w t f₀ H1inj H1alloc
    (kmswVertexAllocated_all _ _) (kmswVertexAllocated_all _ _) hab

private theorem cut_window_west_endpoint (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) :
    (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).west
      (act w (boundaryHitTime w h (-(K : ℤ)))) = boundaryVertex w h (-(K : ℤ)) := by
  by_cases hK : K = 0
  · subst K
    simp only [Nat.cast_zero, neg_zero, boundaryHitTime_zero, boundaryVertex_zero]
    rfl
  · exact (leftHit_UL_singleton_and_west_endpoint w h (by omega : -(K : ℤ) ≤ -1)).2

section Window
variable (ω : ℕ → Fin 3) (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (K : ℕ)
local notation "w" => (fun i => ω (i + 1))
local notation "τ" => boundaryHitTime w h (-(K : ℤ))
local notation "u" => cutWindowRPhaseCodes ω h K

/-- C5: the exact P1 path-lifting form consumed by `InftyCutCore`, together
with the allocated range from `x_{-K}` consumed by the regional geometry.
The region is precisely the present edges activated at or after `τ_{-K}`.
H1–H3 and H3root are explicit open M-hat obligations from `lem-quad-kmsw`
This composes those obligations for `lem-infty-cut` (127–143), using the
containment setup of `lem-directed-contain` (87–120). -/
theorem cutWindow_shiftCompose
    (f₀ : PresentVertex u → PresentVertex (fun i => w (τ + i)))
    (H1inj : ∀ {a b}, kmswVertexAllocated u a → kmswVertexAllocated u b →
      f₀ a = f₀ b → a = b)
    (H1alloc : ∀ a, kmswVertexAllocated u a →
      kmswVertexAllocated (fun i => w (τ + i)) (f₀ a))
    (H2 : ∀ a, kmswVertexAllocated u a →
      ∀ {v} (q : Path (f₀ a) v),
        ∃ b : PresentVertex u, kmswVertexAllocated u b ∧
          ∃ r : Path a b, f₀ b = v ∧ ∀ y ∈ r.vertices, f₀ y ∈ q.vertices)
    (H3 : ∀ {v : PresentVertex (fun i => w (τ + i))},
      Path (⟨0⟩ : PresentVertex (fun i => w (τ + i))) v →
        ∃ b : PresentVertex u, kmswVertexAllocated u b ∧ f₀ b = v)
    (H3root : f₀ ⟨0⟩ = ⟨0⟩) (A : Finset ℕ) :
    let f := shiftComposeEmbedding u w τ f₀ H1inj H1alloc
    (∀ i ∈ A, ∀ {v} (q : Path (f (⟨i⟩ : PresentVertex u)) v),
      (∀ e ∈ pathEdgeList q, e ∈ cutLateRegion w τ) →
        ∃ b : PresentVertex u, ∃ r : Path (⟨i⟩ : PresentVertex u) b,
          f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices) ∧
    (∀ {v : PresentVertex w}
      (q : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) v),
      (∀ e ∈ pathEdgeList q, e ∈ cutLateRegion w τ) →
        ∃ b : PresentVertex u, kmswVertexAllocated u b ∧ f b = v) ∧
    f ⟨0⟩ = ⟨boundaryVertex w h (-(K : ℤ))⟩ := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i _ v q hq
    have hlate : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
        τ ≤ actTime w e he := by
      intro e he hep
      exact (mem_cutLateRegion_iff w τ e hep).1 (hq e he) hep
    obtain ⟨b, _, r, hb, hr⟩ := shiftCompose_late_path_lift u w τ f₀ H1alloc H2
      ⟨i⟩ (kmswVertexAllocated_all _ _) q hlate
    exact ⟨b, r, hb, hr⟩
  · rw [← cut_window_west_endpoint w h K]
    intro v q hq
    apply shiftCompose_late_range u w τ f₀ H3 q
    intro e he hep
    exact (mem_cutLateRegion_iff w τ e hep).1 (hq e he) hep
  · change shiftLimitVertex w τ (f₀ ⟨0⟩) = _
    rw [H3root, shiftLimitVertex_root w τ, cut_window_west_endpoint w h K]

end Window
end DirectedDistances.KMSW
