module

public import DirectedDistances.KMSW.FiniteAvoidance
public import DirectedDistances.KMSW.ActiveTimeMonotone
public import DirectedDistances.KMSW.RPhaseLawTransfer

/-! # Deterministic finite-avoidance glue for boundary windows

Finite exploration is proved here. Identification with an R-phase KMSW image
(P1, `lem-quad-kmsw`), its common finite-avoidance witnesses (P2,
`RPhaseLawTransfer`), and the common-region geometry (P3, the common right
boundary and noncrossing argument at lines 136–139) remain explicit premises.
In particular, this module does not prove the source lemma unconditionally. -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Present edge IDs activated during a finite time interval; missing edges -/
@[expose] def cutActivatedBetween (w : ℕ → Fin 3) (s t : ℕ) : Set ℕ :=
  act w '' Set.Ico s t

/-- Finite exploration between two times, including reversed or equal -/
theorem cutActivatedBetween_finite (w : ℕ → Fin 3) (s t : ℕ) :
    (cutActivatedBetween w s t).Finite :=
  (Set.finite_Ico s t).image (act w)

/-- Both endpoints of the finitely many explored present edges form a finite
assumption, boundary identification, or ordering of `s,t` is needed. -/
theorem cutActivatedBetween_endpoints_finite (w : ℕ → Fin 3) (s t : ℕ) :
    ((fun e => (⟨edgeWest w e⟩ : PresentVertex w)) '' cutActivatedBetween w s t ∪
      (fun e => (⟨edgeEast w e⟩ : PresentVertex w)) '' cutActivatedBetween w s t).Finite :=
  ((cutActivatedBetween_finite w s t).image _).union
    ((cutActivatedBetween_finite w s t).image _)

/-- An edge on a boundary-started path either belongs to the finite interval
between its hit and `T`, or activates at or after `T`. This is the direct
activation-order part of `lem-infty-cut`
or concluded. In particular, this does not order hit times by boundary index. -/
theorem boundary_path_edge_before_or_after (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) (T : ℕ)
    {b : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) b)
    {e : ℕ} (he : e ∈ pathEdgeList p) :
    e ∈ cutActivatedBetween w (boundaryHitTime w h k) T ∨
      ∃ n, T ≤ n ∧ e = act w n := by
  obtain ⟨n, hn, hen⟩ := boundary_path_future_edges w h k p e he
  by_cases hnT : n < T
  · exact Or.inl ⟨n, ⟨hn, hnT⟩, hen.symm⟩
  · exact Or.inr ⟨n, Nat.le_of_not_gt hnT, hen⟩

/-- Finite avoidance transfers under inclusion of avoiding-reachable endpoint
sets, even after adding a finite exceptional set. This is the finite-error
is a premise; ordinary reachability inclusion alone does not suffice. -/
theorem finiteAvoidance_of_subset_union_finite {w : ℕ → Fin 3}
    {a b z : PresentVertex w} (E : Set (PresentVertex w)) (hE : E.Finite)
    (hb : FiniteAvoidance b z)
    (hsub : {v | ∃ p : Path a v, z ∉ p.vertices} ⊆
      E ∪ {v | ∃ p : Path b v, z ∉ p.vertices}) :
    FiniteAvoidance a z :=
  (hE.union hb).subset hsub

/-- Avoiding reachability from `a` to `b` makes the avoiding-reachable set
from `b` a subset of the one from `a`. Thus finite avoidance descends along
The connecting path must itself avoid `z`. -/
theorem finiteAvoidance_of_avoiding_path {w : ℕ → Fin 3}
    {a b z : PresentVertex w} (p : Path a b) (hp : z ∉ p.vertices)
    (ha : FiniteAvoidance a z) : FiniteAvoidance b z := by
  apply ha.subset
  rintro v ⟨q, hq⟩
  refine ⟨p.comp q, ?_⟩
  intro hz
  rw [Path.vertices_comp] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp (List.dropLast_subset _ hz)
  · exact hq hz

/-- Paths using only a finite set of edge IDs have finitely many possible
endpoints: the start or the terminal endpoint of one of those edges.
This justifies the finite-exploration error in `lem-infty-cut` -/
theorem finite_endpoints_of_paths_using_finite_edges {w : ℕ → Fin 3}
    (a : PresentVertex w) (E : Set ℕ) (hE : E.Finite) :
    {b : PresentVertex w | ∃ p : Path a b,
      ∀ e ∈ pathEdgeList p, e ∈ E}.Finite := by
  have hbound := (Set.finite_singleton a).union
    (hE.image (fun e => (⟨edgeEast w e⟩ : PresentVertex w)))
  apply hbound.subset
  rintro b ⟨p, hp⟩
  cases p with
  | nil => exact Or.inl rfl
  | cons q e =>
    refine Or.inr ⟨e.val, hp e.val ?_, ?_⟩
    · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · have hb : (⟨b.id⟩ : PresentVertex w) = b := by cases b; rfl
      exact (congrArg (fun n => (⟨n⟩ : PresentVertex w)) e.property.2.2).trans hb

/-- A boundary-started path whose edges all activate before a fixed time has
only finitely many possible endpoints. Together with
`boundary_path_edge_before_or_after`, this proves the finite-exploration part
activation times. The common right boundary still requires geometric input. -/
theorem boundary_endpoints_before_cutoff_finite (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) (T : ℕ) :
    {b : PresentVertex w | ∃ p : Path
      (⟨boundaryVertex w h k⟩ : PresentVertex w) b,
        ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, actTime w e he < T}.Finite := by
  apply (finite_endpoints_of_paths_using_finite_edges
    (⟨boundaryVertex w h k⟩ : PresentVertex w)
    (cutActivatedBetween w (boundaryHitTime w h k) T)
    (cutActivatedBetween_finite w _ T)).subset
  rintro b ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro e he
  obtain ⟨hePresent, htime⟩ := boundary_path_actTime_ge w h k p e he
  exact ⟨actTime w e hePresent, ⟨htime, hp e he hePresent⟩,
    (actTime_spec w e hePresent).symm⟩

/-- When all starts in a finite window share the same finite-avoidance
vertex, a single eventual bound works simultaneously for all starts along
any injective endpoint sequence (`lem-infty-cut`,
the conclusion quantifies over paths, whenever such paths exist. The shared
cut is a premise, and its existence is not inferred from separate witnesses. -/
theorem finiteAvoidance_window_eventually {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (K : ℕ) (z : PresentVertex w)
    (havoid : ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K → FiniteAvoidance (x k) z)
    (y : ℕ → PresentVertex w) (hy : Function.Injective y) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      ∀ p : Path (x k) (y j), z ∈ p.vertices := by
  let S : Set (PresentVertex w) := ⋃ k ∈ Set.Icc (-(K : ℤ)) (K : ℤ),
    {v | ∃ p : Path (x k) v, z ∉ p.vertices}
  have hS : S.Finite := (Set.finite_Icc _ _).biUnion
    (fun k hk => havoid k hk.1 hk.2)
  have hindices : (y ⁻¹' S).Finite :=
    hS.preimage (fun _ _ _ _ hij => hy hij)
  obtain ⟨N, hN⟩ := hindices.bddAbove
  refine ⟨N + 1, ?_⟩
  intro j hj k hk₁ hk₂ p
  by_contra hp
  have hjavoid : j ∈ y ⁻¹' S :=
    Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨⟨hk₁, hk₂⟩, ⟨p, hp⟩⟩⟩
  have hjle : j ≤ N := hN hjavoid
  omega

/-- Finite avoidance transfers from a finite family in a second KMSW graph
when every avoiding endpoint lifts to that family or belongs to a finite
The path-lifting premise is explicit; no geometric identification is proved. -/
theorem finiteAvoidance_of_finite_family_lift {u w : ℕ → Fin 3}
    (a : PresentVertex w) (f : PresentVertex u → PresentVertex w)
    (A : Finset ℕ) (E : Set (PresentVertex w)) (hE : E.Finite)
    (c : PresentVertex u)
    (hc : ∀ i ∈ A, FiniteAvoidance (⟨i⟩ : PresentVertex u) c)
    (hlift : ∀ {v} (p : Path a v), f c ∉ p.vertices →
      v ∈ E ∨ ∃ i ∈ A, ∃ b : PresentVertex u,
        f b = v ∧ ∃ q : Path (⟨i⟩ : PresentVertex u) b, c ∉ q.vertices) :
    FiniteAvoidance a (f c) := by
  let S : Set (PresentVertex u) :=
    ⋃ i ∈ (A : Set ℕ), {b | ∃ q : Path (⟨i⟩ : PresentVertex u) b, c ∉ q.vertices}
  have hS : S.Finite := A.finite_toSet.biUnion (fun i hi => hc i hi)
  apply (hE.union (hS.image f)).subset
  rintro v ⟨p, hp⟩
  rcases hlift p hp with hv | ⟨i, hi, b, hb, q, hq⟩
  · exact Or.inl hv
  · exact Or.inr ⟨b,
      Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ⟨q, hq⟩⟩⟩, hb⟩

/-- Conditional common-region glue for one boundary window in `lem-infty-cut`

* P1: avoidance-reflecting path identification of the common hatted region
  with the model `u`, from `lem-quad-kmsw` (lines 525–537).
* P2: infinitely many common finite-avoidance witnesses for the finite entry
  family `A`, supplied for allocated IDs by `RPhaseLawTransfer`.
* P3: every window-started path can be replaced, outside the finite endpoint
  exception `E`, by a regional path from `A`, with added vertex visits only
  in `E`. This is an outstanding geometric obligation for the common right
  boundary/noncrossing producer (lines 136–139), not a consequence of finite
  exploration alone.

The proof chooses a model cut whose image avoids `E` and proves the transfer
simultaneously for every start. It does not assume per-start cut witnesses
have a common image. Edge IDs, including multiedge identity, are retained. -/
theorem boundary_windowFiniteAvoidance_of_commonRegion
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (K : ℕ)
    (u : ℕ → Fin 3) (f : PresentVertex u ↪ PresentVertex w)
    (A : Finset ℕ) (region : Set ℕ) (E : Set (PresentVertex w)) (hE : E.Finite)
    (hP1 : ∀ i ∈ A, ∀ {v} (q : Path (f (⟨i⟩ : PresentVertex u)) v),
      (∀ e ∈ pathEdgeList q, e ∈ region) →
        ∃ b : PresentVertex u, ∃ r : Path (⟨i⟩ : PresentVertex u) b,
          f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices)
    (hP2 : {c : PresentVertex u | ∀ i ∈ A,
      FiniteAvoidance (⟨i⟩ : PresentVertex u) c}.Infinite)
    (hP3 : ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      ∀ {v} (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
        v ∈ E ∨ ∃ i ∈ A, ∃ q : Path (f (⟨i⟩ : PresentVertex u)) v,
          (∀ e ∈ pathEdgeList q, e ∈ region) ∧
          ∀ y ∈ q.vertices, y ∈ p.vertices ∨ y ∈ E) :
    ∃ z : PresentVertex w, ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      FiniteAvoidance (⟨boundaryVertex w h k⟩ : PresentVertex w) z := by
  obtain ⟨c, hc, hcE⟩ := hP2.exists_notMem_finite (hE.preimage_embedding f)
  refine ⟨f c, ?_⟩
  intro k hk₁ hk₂
  apply finiteAvoidance_of_finite_family_lift _ f A E hE c hc
  intro v p hp
  rcases hP3 k hk₁ hk₂ p with hv | ⟨i, hi, q, hqregion, hqvertices⟩
  · exact Or.inl hv
  · obtain ⟨b, r, hb, hr⟩ := hP1 i hi q hqregion
    refine Or.inr ⟨i, hi, b, hb, r, ?_⟩
    intro hcr
    rcases hqvertices (f c) (hr c hcr) with hcp | hcException
    · exact hp hcp
    · exact hcE hcException

/-- The actual R-phase model at the hit of the leftmost index of the window
`[-K,K]`. The input uses the fixed time-zero code convention of
`DirectedContainLaw1` and `RPhaseLawTransfer`
`lem-infty-cut`, lines 133–139). This defines only a code sequence; identifying
its KMSW image with the hatted submap remains P1. -/
@[expose] noncomputable def cutWindowRPhaseCodes (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (K : ℕ) : ℕ → Fin 3 :=
  rCodeSequence (RandomWalk.codeShift
    (boundaryHitTime (fun i => ω (i + 1)) h (-(K : ℤ))) ω)

/- The exact window finite-avoidance premise consumed by
`BusemannM0OnePremise`, conditional on P1, P2, and P3 for the actual leftmost
P1 is the avoidance-reflecting `lem-quad-kmsw` identification (lines 525–537);
P2 is the common allocated-family witness supplied almost surely by
geometry of lines 136–139, in the explicit path-replacement form below.
Finiteness of the entry family and error set alone does not prove P3. This
deterministic implication makes no unconditional or almost-sure closure claim. -/
theorem boundary_windowFiniteAvoidance_of_rPhaseCommonRegions
    (ω : ℕ → Fin 3) (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (f : ∀ K : ℕ, PresentVertex (cutWindowRPhaseCodes ω h K) ↪
      PresentVertex (fun i => ω (i + 1)))
    (A : ℕ → Finset ℕ) (region : ℕ → Set ℕ)
    (E : ℕ → Set (PresentVertex (fun i => ω (i + 1))))
    (hE : ∀ K, (E K).Finite)
    (hP1 : ∀ K i, i ∈ A K →
      ∀ {v} (q : Path (f K (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K))) v),
        (∀ e ∈ pathEdgeList q, e ∈ region K) →
          ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
          ∃ r : Path (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) b,
            f K b = v ∧ ∀ y ∈ r.vertices, f K y ∈ q.vertices)
    (hP2 : ∀ K, {c : PresentVertex (cutWindowRPhaseCodes ω h K) |
      ∀ i ∈ A K, FiniteAvoidance
        (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) c}.Infinite)
    (hP3 : ∀ (K : ℕ) (k : ℤ), -(K : ℤ) ≤ k → k ≤ K →
      ∀ {v} (p : Path
        (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
          PresentVertex (fun i => ω (i + 1))) v),
        v ∈ E K ∨ ∃ i ∈ A K,
          ∃ q : Path (f K (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K))) v,
            (∀ e ∈ pathEdgeList q, e ∈ region K) ∧
            ∀ y ∈ q.vertices, y ∈ p.vertices ∨ y ∈ E K) :
    ∀ K : ℕ, ∃ z : PresentVertex (fun i => ω (i + 1)),
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
        FiniteAvoidance
          (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
            PresentVertex (fun i => ω (i + 1))) z := by
  intro K
  exact boundary_windowFiniteAvoidance_of_commonRegion
    (fun i => ω (i + 1)) h K (cutWindowRPhaseCodes ω h K)
    (f K) (A K) (region K) (E K) (hE K) (hP1 K) (hP2 K) (hP3 K)

end DirectedDistances.KMSW
