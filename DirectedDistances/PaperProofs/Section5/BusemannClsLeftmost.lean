/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.BusemannClsIdentity
public import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmostXdp
import DirectedDistances.PaperProofs.SourceResults.BusemannPaper
import Mathlib.Data.Nat.Find

/-! Supporting lemmas for paper labels `lem-busemann-cls` (see CORRESPONDENCE.md). -/

/-! # Least leftmost coalescence offsets and Lemma 5.7

one-based: the equality for every source `t ≥ 1` becomes equality at Lean
indices `theta + n` and `theta' + n` for every `n : ℕ`. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}



theorem m0Cut_geodesic_edge_injective {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    Function.Injective (fun n => wholePlaneEdgeι W 0 (P.codePath.edge n)) := by
  intro i j hij
  have he := wholePlaneEdgeι_injective W 0 hij
  apply infinitePresentPath_west_injective (H.1 0)
    (fun n => ⟨monotoneLayoutDrawing (shiftedStream W 0) n
      ((monotone_family_all (shiftedStream W 0)) n).choose,
      ((monotone_family_all (shiftedStream W 0)) n).choose_spec⟩) P.codePath
  exact congrArg (edgeWest (shiftedStream W 0)) he




theorem m0Cut_coalescence_offsets_ordered {k k' : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (Q : M0CutInfiniteGeodesic W H h hLL k' longest)
    {a b c d : ℕ} (hab : M0CutEdgeTailsCoalesce P Q a b)
    (hcd : M0CutEdgeTailsCoalesce P Q c d) (hac : a ≤ c) : b ≤ d := by
  have hfirst := hab (c - a)
  have hsecond := hcd 0
  have hac' : a + (c - a) = c := by omega
  rw [hac'] at hfirst
  simp only [Nat.add_zero] at hsecond
  have hidx := m0Cut_geodesic_edge_injective Q (hfirst.symm.trans hsecond)
  omega





theorem m0Cut_existsUnique_least_edge_coalescence {k k' : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (Q : M0CutInfiniteGeodesic W H h hLL k' longest)
    (hco : ∃ a b : ℕ, M0CutEdgeTailsCoalesce P Q a b) :
    ∃! q : ℕ × ℕ, M0CutLeastEdgeCoalescence P Q q.1 q.2 := by
  classical
  let a := Nat.find hco
  obtain ⟨b, hb⟩ := Nat.find_spec hco
  have hleast : M0CutLeastEdgeCoalescence P Q a b := by
    refine ⟨hb, fun c d hcd => ?_⟩
    have hac : a ≤ c := Nat.find_min' hco ⟨d, hcd⟩
    exact ⟨hac, m0Cut_coalescence_offsets_ordered P Q hb hcd hac⟩
  refine ⟨(a, b), hleast, ?_⟩
  intro q hq
  have h₁ := hleast.2 q.1 q.2 hq.1
  have h₂ := hq.2 a b hleast.1
  exact Prod.ext (Nat.le_antisymm h₂.1 h₁.1) (Nat.le_antisymm h₂.2 h₁.2)




theorem m0Cut_ae_leftmost_xdp_least_coalescence :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2 := by
  filter_upwards [Xdp.m0Cut_ae_leftmost_xdp_and_pairwise_coalescence] with W hW
  obtain ⟨H, h, hLL, hp, hall⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨R, T, P, hR, hleft, huniq, hcoal⟩ := hall longest
  refine ⟨R, T, P, hR, hleft, huniq, fun k => ?_⟩
  exact m0Cut_existsUnique_least_edge_coalescence (P k) (P (k - 1))
    (hcoal k (k - 1))





@[expose] def lemma57Statement : Prop :=
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∃! X : ℤ → ℤ, if longest then
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2) ∧
        ∀ X : ℤ → ℤ,
          (if longest then IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
            else IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) →
          ∀ (k : ℤ) (theta theta' : ℕ),
            M0CutLeastEdgeCoalescence (P k) (P (k - 1)) theta theta' →
            X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ)



theorem lemma57_holds : lemma57Statement := by
  filter_upwards [m0Cut_ae_leftmost_xdp_least_coalescence,
    DirectedDistances.PaperProofs.SourceResults.thm_busemann_paper_provider]
      with W hleft hb
  obtain ⟨H, h, hLL, hp, hall⟩ := hleft
  obtain ⟨HB, hB, hLLB, _, _, _, _, _, _, _, hsdp, hldp⟩ := hb
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨R, T, P, hR, hleft, huniq, hleast⟩ := hall longest
  refine ⟨R, T, P, hR, hleft, huniq, ?_, hleast, ?_⟩
  · cases longest with
    | false => exact hsdp
    | true => exact hldp
  · intro X hX k theta theta' hco
    exact m0Cut_busemann_cls_identity longest (P k) (P (k - 1))
      theta theta' hco X hX

end DirectedDistances.PaperProofs.Section5
