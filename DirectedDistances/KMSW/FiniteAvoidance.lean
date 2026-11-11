module

public import DirectedDistances.KMSW.BusemannFromCut
public import DirectedDistances.RandomWalk.SecondCoordinateUnbounded

/-! # Finite avoidance and eventual path separation

Finite sets of endpoints reachable along paths avoiding one vertex give an
eventual cut for every injective reachable sequence. For the Pitman UIQBOT
realization, record barriers give infinitely many such vertices from every
allocated start. This is the UIQBOT-level input to `lem-infty-cut`; transfer to
the maps `M̂_{τ_k,∞}` inside `M_{0,∞}` remains a separate step -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory DirectedDistances.RandomWalk
open scoped Classical

/-- The set of endpoints reached from `a` by a directed path that avoids `z` -/
def FiniteAvoidance {w : ℕ → Fin 3} (a z : PresentVertex w) : Prop :=
  ({v : PresentVertex w | ∃ p : Path a v, z ∉ p.vertices} : Set (PresentVertex w)).Finite

/-- A finite set of endpoints reachable along paths avoiding `z` is eventually
left by every injective sequence of reachable vertices -/
theorem finiteAvoidance_eventually_forces_path_through {w : ℕ → Fin 3}
    {a z : PresentVertex w} (havoid : FiniteAvoidance a z)
    (y : ℕ → PresentVertex w) (hy : Function.Injective y)
    (_hreach : ∀ j, Reachable a (y j)) :
    ∃ N, ∀ j, N ≤ j → ∀ p : Path a (y j), z ∈ p.vertices := by
  let S : Set (PresentVertex w) := {v | ∃ p : Path a v, z ∉ p.vertices}
  have hindices : (y ⁻¹' S).Finite := by
    apply Set.Finite.preimage (s := S)
    · intro i hi j hj hij
      exact hy hij
    · simpa only [S, FiniteAvoidance] using havoid
  obtain ⟨N, hN⟩ := hindices.bddAbove
  refine ⟨N + 1, ?_⟩
  intro j hj p
  by_contra hp
  have hjavoid : j ∈ y ⁻¹' S := ⟨p, hp⟩
  have hjle : j ≤ N := hN hjavoid
  omega

/-- Finite avoidance supplies the eventual-cut premise used to construct the -/
theorem finiteAvoidance_implies_busemannCutHypothesis {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w)
    (h : ∀ K : ℕ, ∃ z : PresentVertex w,
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K → FiniteAvoidance (x k) z) :
    BusemannCutHypothesis x := by
  intro K
  obtain ⟨z, hz⟩ := h K
  refine ⟨z, ?_⟩
  intro k hk₁ hk₂ y hy hreach
  exact finiteAvoidance_eventually_forces_path_through (hz k hk₁ hk₂) y hy hreach

private theorem presentVertex_id_ext {w : ℕ → Fin 3} {u v : PresentVertex w}
    (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

private theorem earlierRecordVertex_mem_recordBefore {w : ℕ → Fin 3}
    {m n : ℕ} (hmn : m < n)
    (hA : ∀ j < n, R w n ≤ R w j - 1) :
    recordVertex w m ∈ recordBefore w n := by
  have hmEdge : act w m < (kmswStage w n).nextEdge := by
    exact (act_lt_nextEdge w (le_refl m)).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_of_lt hmn))
  have hmBound := (kmswStage_endpoints_lt_nextVertex w n (act w m) hmEdge).1
  have hmStageEq : (kmswStage w m).west (act w m) =
      (kmswStage w n).west (act w m) := by
    exact (edge_endpoints_eq w (act_lt_nextEdge w (le_refl m))).1.trans
      (edge_endpoints_eq w hmEdge).1.symm
  change (recordVertex w m).id < (kmswStage w n).nextVertex ∧
    (recordVertex w m).id ≠ (recordVertex w n).id ∧
    (recordVertex w m).id ≠ (kmswStage w n).east (act w n)
  refine ⟨?_, ?_, ?_⟩
  · change (kmswStage w m).west (act w m) < _
    rw [hmStageEq]
    exact hmBound
  · intro heq
    exact recordVertex_ne w hmn hA (presentVertex_id_ext heq)
  · intro heq
    have hnot := activeEast_ne_activeInitial w
      (j := m) (n := n) (Nat.le_of_lt hmn)
    apply hnot
    rw [CutConverse.activeInitial_eq]
    exact heq.symm

/-- From the finite old side of a record, only finitely many endpoints can be
reached while avoiding that record vertex. The path-separation theorem puts
every such endpoint back in `recordBefore`; this region is finite because all
its vertex IDs are below the finite-stage vertex bound -/
private theorem finiteAvoidance_of_recordBefore {w : ℕ → Fin 3}
    {a : PresentVertex w} (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (ha : a ∈ recordBefore w n) :
    FiniteAvoidance a (recordVertex w n) := by
  let S : Set (PresentVertex w) := {v | v.id < (kmswStage w n).nextVertex}
  have hS : S.Finite := by
    apply Set.Finite.subset (Set.finite_range
      (fun i : Fin (kmswStage w n).nextVertex => (⟨i.val⟩ : PresentVertex w)))
    intro v hv
    change v.id < (kmswStage w n).nextVertex at hv
    exact ⟨⟨v.id, hv⟩, by cases v; rfl⟩
  change ({v : PresentVertex w | ∃ p : Path a v,
    recordVertex w n ∉ p.vertices} : Set (PresentVertex w)).Finite
  apply hS.subset
  intro v hv
  by_contra hnot
  have hnotBefore : v ∉ recordBefore w n := by
    intro hvBefore
    apply hnot
    exact hvBefore.1
  rcases hv with ⟨p, havoid⟩
  have hmust := recordVertex_mem_path_from_before w n hA hB
    (Or.inl ha) hnotBefore p
  exact havoid hmust

private theorem infinite_finiteAvoidance_of_records {w : ℕ → Fin 3}
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hrecords : {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite)
    (a : PresentVertex w) (halloc : ∃ N, a.id < (kmswStage w N).nextVertex) :
    {z : PresentVertex w | FiniteAvoidance a z}.Infinite := by
  obtain ⟨m, hm⟩ := allocated_vertex_eventually_activeInitial_of_R_unbounded
    w hR a.id halloc
  have hma : recordVertex w m = a := by
    apply presentVertex_id_ext
    simpa only [recordVertex, CutConverse.activeInitial_eq] using hm
  let G : Set ℕ := {n | (∀ j < n, R w n ≤ R w j - 1) ∧
    (∀ j, n ≤ j → L w n ≤ L w j) ∧ m < n}
  have hG : G.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro q
    obtain ⟨n, hn, hnq⟩ := (Set.infinite_iff_exists_gt.mp hrecords) (max m q)
    refine ⟨n, ?_, ?_⟩
    · exact ⟨hn.1, hn.2, by omega⟩
    · omega
  have hinj : Set.InjOn (recordVertex w) G := by
    intro n hn k hk heq
    rcases lt_trichotomy n k with hlt | heq' | hgt
    · exact False.elim (recordVertex_ne w hlt hk.1 heq)
    · exact heq'
    · exact False.elim (recordVertex_ne w hgt hn.1 heq.symm)
  have himage : (recordVertex w '' G).Infinite := hG.image hinj
  have hsub : recordVertex w '' G ⊆ {z | FiniteAvoidance a z} := by
    rintro z ⟨n, hn, rfl⟩
    have hn' : (∀ j < n, R w n ≤ R w j - 1) ∧
        (∀ j, n ≤ j → L w n ≤ L w j) ∧ m < n := by
      change (∀ j < n, R w n ≤ R w j - 1) ∧
        (∀ j, n ≤ j → L w n ≤ L w j) ∧ m < n at hn
      exact hn
    have haBefore := earlierRecordVertex_mem_recordBefore hn'.2.2 hn'.1
    exact hma ▸ finiteAvoidance_of_recordBefore n hn'.1 hn'.2.1 haBefore
  exact himage.mono hsub

/-- Almost surely, every allocated UIQBOT vertex has infinitely many vertices
whose removal leaves only finitely many endpoints reachable from that start
without visiting the removed vertex. This follows from the infinitely many
record barriers and finite-stage confinement, using
It is the UIQBOT-level cut input to `lem-infty-cut`; the transfer to
`M̂_{τ_k,∞}` inside `M_{0,∞}` is separate -/
theorem pitmanCodes_ae_infinite_finiteAvoidance_any_allocated :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ a : PresentVertex w, (∃ N, a.id < (kmswStage w N).nextVertex) →
        {z : PresentVertex w | FiniteAvoidance a z}.Infinite := by
  filter_upwards [pitmanCodes_ae_infinite_cutSeparation_records,
    RandomWalk.pitmanCodes_ae_R_unbounded_below] with ω hrecordsAE hRAE
  dsimp only
  let w : ℕ → Fin 3 := pitmanCode (fun i => ω (i + 1))
  have hrecords : {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite := by
    simpa [w] using hrecordsAE
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hRAE a
    exact ⟨n, by rw [RandomWalk.kmsw_R_eq]; exact hn⟩
  intro a halloc
  exact infinite_finiteAvoidance_of_records hR hrecords a halloc

/-- Almost surely, the source `0` has infinitely many finite-avoidance cut
vertices in the fallback-free UIQBOT realization. This is the UIQBOT-level
input to `lem-infty-cut`; transferring it to `M̂_{τ_k,∞}` inside -/
theorem pitmanCodes_ae_infinite_source_finiteAvoidance :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      {z : PresentVertex w | FiniteAvoidance (⟨0⟩ : PresentVertex w) z}.Infinite := by
  filter_upwards [pitmanCodes_ae_infinite_finiteAvoidance_any_allocated] with ω hω
  dsimp only
  exact hω (⟨0⟩ : PresentVertex (pitmanCode (fun i => ω (i + 1))))
    ⟨0, by simp [kmswStage, kmswInit]⟩

end DirectedDistances.KMSW
