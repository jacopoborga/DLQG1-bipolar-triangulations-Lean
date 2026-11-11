module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.RandomWalk.IIDCodeRelabel

/-! # Finite-stage and first-hit alignment helpers

Helpers toward Lemma 7.2 (`lem-cell-ldp-lower`, -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

/-- Helper toward Lemma 7.2 (`lem-cell-ldp-lower`,
coordinate, with no time shift; not the paper result. -/
theorem shifted_codeWalk_fst_eq_L (ω : ℕ → Fin 3) (n : ℕ) :
    L (fun i => ω (i + 1)) n = (RandomWalk.codeWalk ω n).1 := by
  simp [L, RandomWalk.codeWalk, Prod.fst_sum]

/-- Transport one present arrow to a later KMSW stage, preserving its endpoints. -/
private def stageArrow_mono {w : ℕ → Fin 3} {s t : ℕ} (hst : s ≤ t)
    {a b : StagePresentVertex w s} (e : a ⟶ b) :
    (⟨a.id⟩ : StagePresentVertex w t) ⟶ ⟨b.id⟩ := by
  have hp := present_mono w e.property.1 e.property.2.1 t hst
  have hend := present_endpoints_stable w e.property.1 e.property.2.1 hst
  exact ⟨e.val, hp.1, hp.2,
    hend.1.trans e.property.2.2.1, hend.2.trans e.property.2.2.2⟩

/-- Helper toward Lemma 7.2 (`lem-cell-ldp-lower`,
length to a later stage; not the paper result. -/
theorem stage_path_mono {w : ℕ → Fin 3} {s t : ℕ} (hst : s ≤ t)
    {a b : StagePresentVertex w s} (p : Path a b) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w t) ⟨b.id⟩,
      q.length = p.length := by
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | cons p e ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q.cons (stageArrow_mono hst e), ?_⟩
    simp [Path.length_cons, hq]

/-- Helper toward Lemma 7.2 (`lem-cell-ldp-lower`,
stages; not the paper result. -/
theorem stage_path_mono_length_ge {w : ℕ → Fin 3} {s t m : ℕ} (hst : s ≤ t)
    {a b : StagePresentVertex w s} (p : Path a b) (hm : m ≤ p.length) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w t) ⟨b.id⟩,
      m ≤ q.length := by
  obtain ⟨q, hq⟩ := stage_path_mono hst p
  exact ⟨q, hq ▸ hm⟩

/-- Helper toward Lemma 7.2 (`lem-cell-ldp-lower`,
first code-walk coordinate; not the paper result. -/
theorem boundaryHitTime_shift_eq_codeFstFirstHit (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℕ) (hk : 1 ≤ k) :
    ((boundaryHitTime (fun i => ω (i + 1)) h (-(k : ℤ)) : ℕ) : ℕ∞) =
      RandomWalk.codeFstFirstHit (-(k : ℤ)) ω := by
  classical
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let a : ℤ := -(k : ℤ)
  have hsource : ∃ n, L w n = a := h.leftHit a (by dsimp [a]; omega)
  have hwalk (n : ℕ) : L w n = (RandomWalk.codeWalk ω n).1 := by
    simpa [w] using shifted_codeWalk_fst_eq_L ω n
  have hcode : ∃ n, (RandomWalk.codeWalk ω n).1 = a := by
    obtain ⟨n, hn⟩ := hsource
    exact ⟨n, by rw [← hwalk n]; exact hn⟩
  have hfind : Nat.find hsource = Nat.find hcode := by
    apply le_antisymm
    · have hc : L w (Nat.find hcode) = a := by
        rw [hwalk]
        exact Nat.find_spec hcode
      exact Nat.find_min' hsource hc
    · have hs : (RandomWalk.codeWalk ω (Nat.find hsource)).1 = a := by
        rw [← hwalk]
        exact Nat.find_spec hsource
      exact Nat.find_min' hcode hs
  have htime : boundaryHitTime (fun i => ω (i + 1)) h (-(k : ℤ)) =
      Nat.find hsource := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : (-(k : ℤ)) ≠ 0),
      dite_eq_right (by omega : ¬ 0 < -(k : ℤ))]
  rw [htime]
  unfold RandomWalk.codeFstFirstHit
  rw [dite_eq_left hcode, hfind]

/-- Helper toward Lemma 7.2 (`lem-cell-ldp-lower`,
`boundaryHitTime`; not the paper result. -/
theorem boundaryHitTime_le_of_codeFstFirstHit_le (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k N : ℕ) (hk : 1 ≤ k)
    (hN : RandomWalk.codeFstFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)) :
    boundaryHitTime (fun i => ω (i + 1)) h (-(k : ℤ)) ≤ N := by
  rw [← boundaryHitTime_shift_eq_codeFstFirstHit ω h k hk] at hN
  exact ENat.natCast_le_natCast.mp hN

/-- Helper toward Lemma 7.2 (`lem-cell-ldp-lower`,
namely the initial edge; not the paper result. -/
theorem stage_has_present_directed_edge (w : ℕ → Fin 3) {n : ℕ} (_hn : 1 ≤ n) :
    ∃ a b : StagePresentVertex w n, ∃ q : Path a b, 1 ≤ q.length := by
  let q : Path (⟨0⟩ : StagePresentVertex w n) ⟨1⟩ :=
    Hom.toPath (initialEdgeArrow w n)
  exact ⟨⟨0⟩, ⟨1⟩, q, by simp [q]⟩

end DirectedDistances.PaperProofs.Section7
