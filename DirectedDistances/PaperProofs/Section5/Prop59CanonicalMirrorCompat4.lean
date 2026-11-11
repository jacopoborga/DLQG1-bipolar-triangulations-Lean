/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat3
public import DirectedDistances.PaperProofs.Section5.Prop516PLExteriorTransport

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). This file proves the
ambient-component comparison for a PL drawing restricted to a finite local topology
ball and records the remaining canonical-representation bridge. It makes no
paper-completion claim. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. Every complementary component of an
ambient PL drawing is contained in a complementary component of its positive
radius finite-ball restriction. -/
theorem prop59_PLRestriction_contains_ambientFace
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (F : P.Face) :
    ∃ G : (d39FacedBallPLDrawing M P r hr).Face, F.val ⊆ G.val := by
  let Q := d39FacedBallPLDrawing M P r hr
  obtain ⟨z, hz, hF⟩ := F.property
  have hzQ : z ∉ Q.image := by
    intro hzQ
    exact hz ((d39FacedBallPLDrawing_image_subset M P r hr) hzQ)
  let G : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  refine ⟨G, ?_⟩
  rw [hF]
  exact connectedComponentIn_mono z
    (Set.compl_subset_compl.mpr (d39FacedBallPLDrawing_image_subset M P r hr))

/-- Helper toward Proposition 5.9. The ambient unbounded component is
contained in the unique unbounded component of the finite-ball restriction. -/
theorem prop59_PLRestriction_ambientUnboundedFace_subset_unboundedFace
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (F : P.Face) (hF : P.IsUnbounded F) :
    ∃ G : (d39FacedBallPLDrawing M P r hr).Face,
      F.val ⊆ G.val ∧ (d39FacedBallPLDrawing M P r hr).IsUnbounded G := by
  let Q := d39FacedBallPLDrawing M P r hr
  let := d39FacedBallPLDrawing_finite_vertices M P r hr
  obtain ⟨G, hFG⟩ := prop59_PLRestriction_contains_ambientFace M P r hr F
  have hG : Q.IsUnbounded G := by
    intro R
    obtain ⟨z, hz, hzR⟩ := hF R
    exact ⟨z, hFG hz, hzR⟩
  obtain ⟨U, hU, hUnique⟩ := Q.existsUnique_unbounded_face
  have hGU : G = U := hUnique G hG
  refine ⟨U, ?_, hU⟩
  rw [← hGU]
  exact hFG

/-- Helper toward Proposition 5.9. A dart side bordering an unbounded face
of the ambient drawing belongs to the unbounded orbit on the restricted
positive-radius ball. -/
theorem prop59_ambientUnboundedDartSide_mem_restrictedExternalOrbit
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D) (F : P.Face)
    (hF : P.IsUnbounded F) (hborder : P.dartBorders d.1 F) :
    d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  let Q := d39FacedBallPLDrawing M P r hr
  let vert := restrictedVertex P (d39BallDarts M r : Set M.core.D)
  let hvert := d39FacedBallPLDrawing_vertex_surjective M P r hr
  let Fd := (d39FacedBall M r hr).plDartFace vert Q hvert d
  obtain ⟨G, hFG⟩ := prop59_PLRestriction_contains_ambientFace M P r hr F
  obtain ⟨δ, hδ, hleft⟩ := hborder
  obtain ⟨η, hη, hleft'⟩ :=
    ((d39FacedBall M r hr).plDartFace_eq_iff vert Q hvert d Fd).mp rfl
  let t := min δ η / 2
  have ht : 0 < t := half_pos (lt_min hδ hη)
  have htδ : t < δ := (half_lt_self (lt_min hδ hη)).trans_le (min_le_left _ _)
  have htη : t < η := (half_lt_self (lt_min hδ hη)).trans_le (min_le_right _ _)
  let z := (P.arc d.1).start + (t : ℂ) *
    ((P.arc d.1).initialDirection + (t : ℂ) * Complex.I *
      (P.arc d.1).initialDirection)
  have hzF : z ∈ F.val := hleft t t ht htδ ht htδ
  have hzFd : z ∈ Fd.val := by
    change (Q.arc d).start + (t : ℂ) *
      ((Q.arc d).initialDirection + (t : ℂ) * Complex.I *
        (Q.arc d).initialDirection) ∈ Fd.val
    simpa only [d39FacedBallPLDrawing_arc] using hleft' t t ht htη ht htη
  have hzG : z ∈ G.val := hFG hzF
  have hGfd : G = Fd := Q.faces_eq_of_mem hzG hzFd
  have hsub : F.val ⊆ Fd.val := by
    rw [← hGfd]
    exact hFG
  have hFd_unbounded : ¬ Bornology.IsBounded Fd.val := by
    intro hb
    obtain ⟨R, hball⟩ := hb.subset_closedBall (0 : ℂ)
    obtain ⟨w, hwF, hwR⟩ := hF (R + 1)
    have hwball : w ∈ Metric.closedBall (0 : ℂ) R := hball (hsub hwF)
    have hwnorm : ‖w‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hwball
    have hlarge : R < ‖w‖ := by linarith
    exact (not_le_of_gt hlarge) hwnorm
  exact (d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace
    M P r hr d).mpr hFd_unbounded









































end DirectedDistances.PaperProofs.Section5

end
