/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDistance

/-! # Domain for geometric Definition 3.8 -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open scoped ENNReal

universe uV uE




structure D39GeomDomain {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) : Prop where
  connected : ∀ v w : V, (d39GeomGraph M).Reachable v w
  locallyFinite : ∀ v : V,
    ({e : E | M.toPlaneMapWithMissing.src e = v ∨
      M.toPlaneMapWithMissing.tgt e = v}).Finite
  rootValid : M.toPlaneMapWithMissing.missing rho.1 ∨
    ∃ h : ¬ M.toPlaneMapWithMissing.missing rho.1,
      M.forward ⟨rho.1, h⟩ = rho.2

namespace D39GeomDomain

variable {V : Type uV} {E : Type uE}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}

/-- Helper toward Definition 3.8: local finiteness of geometric edge
identities gives finite simple-graph neighborhoods. -/
private theorem neighborSet_finite (hM : D39GeomDomain M rho) (v : V) :
    (d39GeomGraph M).neighborSet v |>.Finite := by
  classical
  let I : Set E := {e | M.toPlaneMapWithMissing.src e = v ∨
    M.toPlaneMapWithMissing.tgt e = v}
  have hI : I.Finite := hM.locallyFinite v
  have hs : (M.toPlaneMapWithMissing.src '' I).Finite := hI.image _
  have ht : (M.toPlaneMapWithMissing.tgt '' I).Finite := hI.image _
  apply (hs.union ht).subset
  intro w hw
  rcases hw with ⟨hne, e, he | he⟩
  · rcases he with ⟨hsrc, htgt⟩
    exact Or.inr ⟨e, ⟨Or.inl hsrc, htgt⟩⟩
  · rcases he with ⟨hsrc, htgt⟩
    exact Or.inl ⟨e, ⟨Or.inr htgt, hsrc⟩⟩

/-- Helper toward Definition 3.8: every finite-radius vertex ball is finite. -/
theorem ballVertices_finite (hM : D39GeomDomain M rho) (r : ℕ) :
    (d39GeomBallVertices M rho r).Finite := by
  classical
  induction r with
  | zero =>
      simp [d39GeomBallVertices, d39GeomGraphDistance]
  | succ r ihr =>
      let G := d39GeomGraph M
      let c := d39GeomRootVertex M rho
      let B := d39GeomBallVertices M rho r
      have hneigh : ∀ x ∈ B, (G.neighborSet x).Finite := by
        intro x hx
        exact neighborSet_finite hM x
      have hcover : d39GeomBallVertices M rho (r + 1) ⊆
          B ∪ ⋃ x ∈ B, G.neighborSet x := by
        intro v hv
        have hreach : G.Reachable c v := hM.connected c v
        obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_edist
        change G.edist c v ≤ (r + 1 : ℕ∞) at hv
        have hplen : p.length ≤ r + 1 := by
          have hcast : (p.length : ℕ∞) ≤ (r + 1 : ℕ∞) := by
            rw [hp]
            exact hv
          exact_mod_cast hcast
        cases hq : p.reverse with
        | nil =>
            left
            change G.edist c c ≤ (r : ℕ∞)
            simp
        | @cons a b d hadj s =>
            have hlen : s.length + 1 = p.length := by
              have h := congrArg SimpleGraph.Walk.length hq
              simpa [SimpleGraph.Walk.length_reverse,
                SimpleGraph.Walk.length_cons] using h.symm
            have hslen : s.length ≤ r := by
              omega
            have hb : b ∈ B := by
              change G.edist c b ≤ (r : ℕ∞)
              calc
                G.edist c b = G.edist b c := G.edist_comm
                _ ≤ (s.length : ℕ∞) := s.edist_le
                _ ≤ (r : ℕ∞) := by exact_mod_cast hslen
            right
            apply Set.mem_iUnion.mpr
            refine ⟨b, Set.mem_iUnion.mpr ⟨hb, ?_⟩⟩
            exact hadj.symm
      exact ihr.union (ihr.biUnion hneigh) |>.subset hcover

/-- Helper toward Definition 3.8: every finite-radius geometric edge ball is
finite, counting parallel and missing edge identities separately. -/
theorem ballEdges_finite (hM : D39GeomDomain M rho) (r : ℕ) :
    (d39GeomBallEdges M rho r).Finite := by
  classical
  let B := d39GeomBallVertices M rho r
  have hB : B.Finite := ballVertices_finite hM r
  apply (hB.biUnion fun v _ => hM.locallyFinite v).subset
  intro e he
  change M.toPlaneMapWithMissing.src e ∈ B ∧
    M.toPlaneMapWithMissing.tgt e ∈ B at he
  refine Set.mem_iUnion.mpr ⟨M.toPlaneMapWithMissing.src e,
    Set.mem_iUnion.mpr ⟨he.1, ?_⟩⟩
  exact Or.inl rfl

/-- Helper toward Definition 3.8: connectedness and finite balls make the
vertex carrier countable. -/
theorem vertices_countable (hM : D39GeomDomain M rho) : Countable V := by
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion fun r : ℕ =>
    (ballVertices_finite hM r).countable).mono
  intro v _
  refine Set.mem_iUnion.mpr ?_
  obtain ⟨p, hp⟩ := hM.connected (d39GeomRootVertex M rho) v |>.exists_walk_length_eq_edist
  refine ⟨p.length, ?_⟩
  change (d39GeomGraph M).edist (d39GeomRootVertex M rho) v ≤
    (p.length : ℕ∞)
  rw [← hp]

/-- Helper toward Definition 3.8: local finiteness and countability of vertices
make the geometric edge-identity carrier countable. -/
theorem edges_countable (hM : D39GeomDomain M rho) : Countable E := by
  letI : Countable V := vertices_countable hM
  apply Set.countable_univ_iff.mp
  have hI : ∀ v : V,
      ({e : E | M.toPlaneMapWithMissing.src e = v ∨
        M.toPlaneMapWithMissing.tgt e = v}).Countable :=
    fun v => (hM.locallyFinite v).countable
  apply (Set.countable_iUnion hI).mono
  intro e _
  refine Set.mem_iUnion.mpr ⟨M.toPlaneMapWithMissing.src e, ?_⟩
  exact Or.inl rfl



theorem graphDistance_ne_top (hM : D39GeomDomain M rho) (v : V) :
    d39GeomGraphDistance M (d39GeomRootVertex M rho) v ≠ ⊤ := by
  exact (SimpleGraph.edist_ne_top_iff_reachable).2
    (hM.connected (d39GeomRootVertex M rho) v)

end D39GeomDomain

end DirectedDistances.PaperProofs.Section3
