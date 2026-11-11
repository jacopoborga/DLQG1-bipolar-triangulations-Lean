/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FiniteAvoidance

/-! # Finite windows of finite-avoidance cuts

The record barriers give one common finite-avoidance vertex for every finite
family of allocated vertices. This is the UIQBOT-level input to
`lem-infty-cut`; transfer to `M̂_{τ_k,∞}` inside `M_{0,∞}` is a separate step -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory DirectedDistances.RandomWalk
open scoped Classical

private theorem window_presentVertex_id_ext {w : ℕ → Fin 3}
    {u v : PresentVertex w} (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

private theorem window_earlierRecordVertex_mem_recordBefore {w : ℕ → Fin 3}
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
    exact recordVertex_ne w hmn hA (window_presentVertex_id_ext heq)
  · intro heq
    have hnot := activeEast_ne_activeInitial w
      (j := m) (n := n) (Nat.le_of_lt hmn)
    apply hnot
    rw [CutConverse.activeInitial_eq]
    exact heq.symm

private theorem window_finiteAvoidance_of_recordBefore {w : ℕ → Fin 3}
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

/-- Infinitely many record vertices are finite-avoidance vertices for every
member of a finite allocated family. The record hypotheses are the same
record inequalities used in `FiniteAvoidance` -/
theorem finiteAvoidance_infinite_common_of_records
    {w : ℕ → Fin 3}
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hrecords : {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite)
    (A : Finset ℕ)
    (halloc : ∀ a ∈ A, ∃ N, a < (kmswStage w N).nextVertex) :
    {z : PresentVertex w | ∀ a ∈ A,
      FiniteAvoidance (⟨a⟩ : PresentVertex w) z}.Infinite := by
  classical
  let m : ℕ → ℕ := fun a =>
    if ha : a ∈ A then
      (allocated_vertex_eventually_activeInitial_of_R_unbounded
        w hR a (halloc a ha)).choose
    else 0
  have hm_spec (a : ℕ) (ha : a ∈ A) : activeInitial w (m a) = a := by
    dsimp [m]
    rw [dite_eq_left ha]
    exact (allocated_vertex_eventually_activeInitial_of_R_unbounded
      w hR a (halloc a ha)).choose_spec
  let M : ℕ := A.sup m
  let G : Set ℕ := {n | (∀ j < n, R w n ≤ R w j - 1) ∧
    (∀ j, n ≤ j → L w n ≤ L w j) ∧ ∀ a ∈ A, m a < n}
  have hG : G.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro q
    obtain ⟨n, hn, hnq⟩ := (Set.infinite_iff_exists_gt.mp hrecords) (max M q)
    refine ⟨n, ?_, ?_⟩
    · refine ⟨hn.1, hn.2, ?_⟩
      intro a ha
      have ham : m a ≤ M := Finset.le_sup (f := m) ha
      omega
    · omega
  have hinj : Set.InjOn (recordVertex w) G := by
    intro n hn k hk heq
    rcases lt_trichotomy n k with hlt | heq' | hgt
    · exact False.elim (recordVertex_ne w hlt hk.1 heq)
    · exact heq'
    · exact False.elim (recordVertex_ne w hgt hn.1 heq.symm)
  have himage : (recordVertex w '' G).Infinite := hG.image hinj
  have hsub : recordVertex w '' G ⊆
      {z : PresentVertex w | ∀ a ∈ A,
        FiniteAvoidance (⟨a⟩ : PresentVertex w) z} := by
    rintro z ⟨n, hn, rfl⟩
    intro a ha
    have hn' : (∀ j < n, R w n ≤ R w j - 1) ∧
        (∀ j, n ≤ j → L w n ≤ L w j) ∧ ∀ a ∈ A, m a < n := hn
    have haRecord : recordVertex w (m a) = (⟨a⟩ : PresentVertex w) := by
      apply window_presentVertex_id_ext
      simpa only [recordVertex, CutConverse.activeInitial_eq] using hm_spec a ha
    have haBefore := window_earlierRecordVertex_mem_recordBefore
      (hn'.2.2 a ha) hn'.1
    exact haRecord ▸ window_finiteAvoidance_of_recordBefore n
      hn'.1 hn'.2.1 haBefore
  exact himage.mono hsub

/-- Almost surely, every finite family of allocated UIQBOT vertices has
infinitely many common finite-avoidance vertices. This is the UIQBOT-level
input to `lem-infty-cut`; transfer to `M̂_{τ_k,∞}` inside `M_{0,∞}` remains a -/
theorem pitmanCodes_ae_infinite_common_finiteAvoidance_any_allocated :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ A : Finset ℕ,
        (∀ a ∈ A, ∃ N, a < (kmswStage w N).nextVertex) →
          {z : PresentVertex w | ∀ a ∈ A,
            FiniteAvoidance (⟨a⟩ : PresentVertex w) z}.Infinite := by
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
  intro A halloc
  exact finiteAvoidance_infinite_common_of_records hR hrecords A halloc

/-- Almost surely, every bi-infinite family of allocated UIQBOT vertices
satisfies the finite-window cut premise for its Busemann function. This is the
UIQBOT-level input to `lem-infty-cut`; transfer to `M̂_{τ_k,∞}` inside -/
theorem pitmanCodes_ae_busemannCutHypothesis_of_allocated :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ x : ℤ → PresentVertex w,
        (∀ k, ∃ N, (x k).id < (kmswStage w N).nextVertex) →
          BusemannCutHypothesis x := by
  filter_upwards [pitmanCodes_ae_infinite_common_finiteAvoidance_any_allocated]
    with ω hω
  dsimp only
  intro x hx
  apply finiteAvoidance_implies_busemannCutHypothesis
  intro K
  let A : Finset ℕ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).image
    (fun k : ℤ => (x k).id)
  have hA : ∀ a ∈ A, ∃ N, a <
      (kmswStage (pitmanCode (fun i => ω (i + 1))) N).nextVertex := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    exact hx k
  obtain ⟨z, hz⟩ := (hω A hA).nonempty
  refine ⟨z, ?_⟩
  intro k hk₁ hk₂
  have hmem : (x k).id ∈ A := by
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩, rfl⟩
  have havoid := hz (x k).id hmem
  have hxid : (⟨(x k).id⟩ : PresentVertex
      (pitmanCode (fun i => ω (i + 1)))) = x k :=
    window_presentVertex_id_ext rfl
  rw [hxid] at havoid
  exact havoid

end DirectedDistances.KMSW
