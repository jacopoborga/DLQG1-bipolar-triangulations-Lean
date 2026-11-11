/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTConsumerFactorization
public import DirectedDistances.Paper.Section5.InftyCut

/-! # Cut-path determination obligations toward Proposition 3.9

Selected consumer: `DirectedDistances.Paper.Section5.lem_infty_cut`,
`DirectedDistances/Paper/Section5/InftyCut.lean:38`, in particular its shared
vertex sequence and simultaneous endpoint/path clause at lines 74–89.

The lemmas below eliminate the universal quantifier over infinite endpoint
sequences in favor of finite avoiding-reachable endpoint sets, then express
those sets using bounded code vertex IDs and the counted theorem's actual
identified cut paths. These are deterministic equivalences, not a proof of
geometric finite-ball recovery. No consumer attribution qualifier is removed.
The exact remaining determination statement is recorded at the end. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Quiver MeasureTheory Filter Set
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open scoped Topology

/-- Helper toward Proposition 3.9: for the path predicate used by
`lem_infty_cut`, finite avoidance is equivalent to eventual visitation along
every injective reachable endpoint sequence. The converse rules out an
infinite avoiding set by using an injective sequence inside that same set. -/
theorem uibot_finiteAvoidance_iff_eventual_path_visit
    {w : ℕ → Fin 3} (a z : PresentVertex w) :
    FiniteAvoidance a z ↔
      ∀ y : ℕ → PresentVertex w, Function.Injective y →
        (∀ j, Reachable a (y j)) →
        ∃ J : ℕ, ∀ j, J ≤ j → ∀ p : Path a (y j), z ∈ p.vertices := by
  constructor
  · intro h y hy hreach
    exact finiteAvoidance_eventually_forces_path_through h y hy hreach
  · intro h
    classical
    by_contra hfinite
    let S : Set (PresentVertex w) := {b | ∃ p : Path a b, z ∉ p.vertices}
    have hS : S.Infinite := hfinite
    let e : ℕ ↪ S := hS.natEmbedding
    let y : ℕ → PresentVertex w := fun j => (e j).val
    have hy : Function.Injective y := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    have hreach : ∀ j, Reachable a (y j) := by
      intro j
      obtain ⟨p, _⟩ := (e j).property
      exact ⟨p⟩
    obtain ⟨J, hJ⟩ := h y hy hreach
    obtain ⟨p, hp⟩ := (e J).property
    exact hp (hJ J le_rfl p)

/-- Helper toward Proposition 3.9: the entire shared cut-sequence clause
of `lem_infty_cut` on its identified run carrier is equivalent to infinitude
of the common finite-avoidance set. The same vertex is tested against every
boundary start before any endpoint sequence is chosen. -/
theorem uibot_infinite_common_finiteAvoidance_iff_cut_sequence
    {w : ℕ → Fin 3} (x : ℤ → PresentVertex w) (k k' : ℤ) :
    {z : PresentVertex w | ∀ ell : ℤ, ell ∈ Icc k k' →
      FiniteAvoidance (x ell) z}.Infinite ↔
      ∃ v : ℕ → PresentVertex w, Function.Injective v ∧
        ∀ ell : ℤ, ell ∈ Icc k k' →
          ∀ y : ℕ → PresentVertex w, Function.Injective y →
            (∀ j, Reachable (x ell) (y j)) →
            ∀ m, ∃ J : ℕ, ∀ j, J ≤ j →
              ∀ p : Path (x ell) (y j), v m ∈ p.vertices := by
  constructor
  · intro hS
    let S : Set (PresentVertex w) := {z | ∀ ell : ℤ, ell ∈ Icc k k' →
      FiniteAvoidance (x ell) z}
    let e : ℕ ↪ S := hS.natEmbedding
    refine ⟨fun m => (e m).val, ?_, ?_⟩
    · intro i j hij
      exact e.injective (Subtype.ext hij)
    · intro ell hell y hy hreach m
      exact finiteAvoidance_eventually_forces_path_through
        ((e m).property ell hell) y hy hreach
  · rintro ⟨v, hv, hvisit⟩
    apply Set.infinite_of_injective_forall_mem hv
    intro m ell hell
    apply (uibot_finiteAvoidance_iff_eventual_path_visit (x ell) (v m)).2
    intro y hy hreach
    exact hvisit ell hell y hy hreach m

/-- Helper toward Proposition 3.9: on the counted consumer's run carrier,
finite avoidance is exactly a bound on the IDs of endpoints of avoiding
paths. No bound on path lengths, reachability, or recurrence is assumed. -/
theorem uibot_finiteAvoidance_iff_exists_bound
    {w : ℕ → Fin 3} (a z : PresentVertex w) :
    FiniteAvoidance a z ↔
      ∃ B : ℕ, ∀ b : ℕ, B ≤ b →
        ∀ p : Path a (⟨b⟩ : PresentVertex w), z ∈ p.vertices := by
  constructor
  · intro hfinite
    have hids : (PresentVertex.id ''
        {b : PresentVertex w | ∃ p : Path a b, z ∉ p.vertices}).Finite :=
      hfinite.image PresentVertex.id
    obtain ⟨N, hN⟩ := hids.bddAbove
    refine ⟨N + 1, ?_⟩
    intro b hb p
    by_contra hp
    have hle : b ≤ N := hN ⟨⟨b⟩, ⟨p, hp⟩, rfl⟩
    omega
  · rintro ⟨B, hB⟩
    apply (Set.finite_range (fun i : Fin B => (⟨i.val⟩ : PresentVertex w))).subset
    intro b hb
    obtain ⟨p, hp⟩ := hb
    have hlt : b.id < B := by
      by_contra hnot
      exact hp (hB b.id (Nat.le_of_not_gt hnot) p)
    refine ⟨⟨b.id, hlt⟩, ?_⟩
    cases b
    rfl

/-- Helper toward Proposition 3.9: the bounded avoidance tests are exactly
tests of the finite cut vertex paths appearing in `lem_infty_cut`. This uses
the proved run-to-cut path equivalence, retaining the actual cut relation;
it does not replace that relation by adjacency in the whole-plane map. -/
theorem uibot_finiteAvoidance_iff_identified_cut_path_bound
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (a c : ℕ) :
    FiniteAvoidance (⟨a⟩ : PresentVertex (shiftedStream W 0)) ⟨c⟩ ↔
      ∃ B : ℕ, ∀ b : ℕ, B ≤ b →
        ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
          p 0 = wholePlaneVertexι W 0 a →
          p (Fin.last n) = wholePlaneVertexι W 0 b →
          (∀ i : Fin n, m0CutDirectedStep W H (m0CutData W H h hLL).seam
            (p i.castSucc) (p i.succ)) →
          ∃ i, p i = wholePlaneVertexι W 0 c := by
  rw [uibot_finiteAvoidance_iff_exists_bound]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun b hb => (m0Cut_visit_iff W H h hLL a b c).2 (hB b hb)⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, fun b hb => (m0Cut_visit_iff W H h hLL a b c).1 (hB b hb)⟩

/- OPEN DETERMINATION, selected consumer Lemma 5.3. A concrete sufficient
test-family recovery statement, with every binder, is the following. This
is a proof obligation, not an assumption or an admitted declaration.
The ball-class index r denotes geometric radius r + 1.

  ∀ DC : UIBOTDeterministicComparison,
    ∃ phiBoundary : (r : ℕ) → Quotient (d39GeomBallClassSetoid.{0} r) → ℤ → ℕ,
    ∃ phiAvoidance : (r : ℕ) → Quotient (d39GeomBallClassSetoid.{0} r) →
        ℕ → ℕ → Bool,
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∀ (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ),
          Tendsto (fun r => phiBoundary r (d39GeomBallClassMap r
            (uibotMeasurableWholePlaneClassMap DC W)) k) atTop
            (𝓝 (boundaryVertex (shiftedStream W 0) h k))) ∧
        (∀ a z : ℕ,
          Tendsto (fun r => phiAvoidance r (d39GeomBallClassMap r
            (uibotMeasurableWholePlaneClassMap DC W)) a z) atTop
            (𝓝 (@decide (FiniteAvoidance
              (⟨a⟩ : PresentVertex (shiftedStream W 0)) ⟨z⟩)
              (Classical.propDecidable _))))

Even this labelled sufficient route requires recovery of the run-zero
enumeration and cut from unmarked geometric balls; code measurability and
the forward code-to-ball comparison do not give it. Geometric invariance
and identification of the recovered tests with the same root, cut, missing
edges, boundary and face data must accompany such a construction before a
consumer qualification can be removed. The existing deterministic DC is
unchanged. No assertion about its truth is made here.

The other suggested consumers were inspected but not selected for proof:
`DirectedDistances.Paper.Section3.lem_uibot_bdy` at
`DirectedDistances/Paper/Section3/UIBOTBoundary.lean:45` needs simultaneous
geometric Peano-run and inclusion recovery for every integer start;
`DirectedDistances.Paper.Section5.directed_contain` at
`DirectedDistances/Paper/Section5/DirectedContain.lean:41` needs stopped
encoding recovery and the same boundary stopping witnesses in containment.
Neither follows from the finite bipolar Peano inverse theorem alone. -/

end DirectedDistances.PaperProofs.Section3

end
