/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.GeoExist
public import DirectedDistances.KMSW.LeftmostGeodesicSdpSubmap

/-! # Both distance modes in Lemma 4.6

Candidate for the wording adopted in

The SDP construction uses the UIQBOT-specific shared-departure order theorem
and the same two geometric implications used by the LDP provider. It therefore
does not require the raw-map `BoundaryHitWitnesses` premise. The two distance
modes share one almost-sure event, all four UIQBOT witnesses, and one drawing. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory Quiver Filter DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Lemma 4.6 v2: an edge stream determines the finite-prefix
certificates of an infinite present path, retaining individual parallel edges.
This is the path equality argument used by the immutable LDP provider. -/
private theorem infinitePresentPath_eq_of_edge_eq (w : ℕ → Fin 3) {x : ℕ}
    (P Q : InfinitePresentPath w ⟨x⟩) (he : Q.edge = P.edge) : Q = P := by
  have hinj {u v : PresentVertex w} :
      Function.Injective (pathEdgeList (u := u) (v := v)) := by
    intro p
    induction p with
    | nil =>
      intro q hq
      cases q with
      | nil => rfl
      | cons q f =>
        have hr := congrArg List.reverse hq
        simp only [pathEdgeList, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.reverse_nil, reduceCtorEq] at hr
    | @cons a b p e ih =>
      intro q hq
      cases q with
      | nil =>
        have hr := congrArg List.reverse hq
        simp only [pathEdgeList, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.reverse_nil, List.cons_ne_nil] at hr
      | @cons c d q f =>
        have hr := congrArg List.reverse hq
        simp only [pathEdgeList, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.cons.injEq] at hr
        have hac : a = c := by
          cases a with | mk a =>
            cases c with | mk c =>
              congr 1
              exact e.property.2.1.symm.trans
                ((congrArg (edgeWest w) hr.1).trans f.property.2.1)
        subst c
        have hef : e = f := Subtype.ext hr.1
        subst f
        exact congrArg (fun r => r.cons e) (ih (List.reverse_injective hr.2))
  have hi : Q.initial = P.initial := by
    funext n
    have hp : pathEdgeList (Q.initial n).2 = pathEdgeList (P.initial n).2 := by
      rw [Q.prefix_edges, P.prefix_edges, he]
    have hv : (Q.initial n).1 = (P.initial n).1 := by
      have hid := (pathEdgeList_endpoint (Q.initial n).2).symm.trans
        ((congrArg (geodesicPrefixEnd w x) hp).trans
          (pathEdgeList_endpoint (P.initial n).2))
      cases hq : (Q.initial n).1 with | mk q =>
        cases hpv : (P.initial n).1 with | mk p =>
          congr 1
          simpa only [hq, hpv] using hid
    generalize Q.initial n = q at hp hv ⊢
    generalize P.initial n = p at hp hv ⊢
    obtain ⟨q, qp⟩ := q
    obtain ⟨p, pp⟩ := p
    change q = p at hv
    subst p
    exact congrArg (Sigma.mk q) (hinj hp)
  cases Q
  cases P
  cases he
  cases hi
  rfl

/-- Helper toward Lemma 4.6 v2: under the UIQBOT law, every allocated vertex
has a unique leftmost infinite geodesic for each of LDP and SDP, simultaneously
in the stage-compatible x-monotone drawing of the immutable LDP statement.
Leftmost means full trace containment in the closed region bounded by the
geodesic and the same rightmost directed path (Definition 4.5). -/
theorem geo_exist_both_modes :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∃ Q : ∀ n, StageDrawing w n, (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
        ∃ G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) (kmswInfRot w hfin)
            (kmswLimitDartVertex w),
          G = monotoneFamilyDrawing w hfin (monotone_family_all w) ∧
          (∀ n v, G.pos v.val = (Q n).pos v) ∧
          (∀ n d, G.arc (d.1.val, d.2) = (Q n).arc d) ∧
          (∃ U : G.Face, G.IsUnbounded U ∧ (∀ F : G.Face, G.IsUnbounded F → F = U) ∧
            ∀ d, G.dartBorders d U ↔ limitExternalDart w d) ∧
          ∀ x : ℕ, (∃ n, x < (kmswStage w n).nextVertex) →
            (∃! P : InfinitePresentPath w ⟨x⟩, P.HasLongestSegments ∧
              ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasLongestSegments →
                pathTrace G (fun i => (P'.edge i, false)) ⊆
                  closedBetween (pathTrace G (fun i => (P.edge i, false)))
                    (pathTrace G
                      (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) ∧
            (∃! P : InfinitePresentPath w ⟨x⟩, P.HasShortestSegments ∧
              ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasShortestSegments →
                pathTrace G (fun i => (P'.edge i, false)) ⊆
                  closedBetween (pathTrace G (fun i => (P.edge i, false)))
                    (pathTrace G
                      (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) := by
  filter_upwards [DirectedDistances.PaperProofs.SourceResults.geo_exist,
    pitmanCodes_ae_exists_unique_inBetweenLeftmostRightmostSdp] with ω hldp hsdp
  obtain ⟨hfin, hL, ht, hR, Q, hQ, G, hG, hpos, harc, hface, hldp⟩ := hldp
  obtain ⟨hfinS, hLS, htS, hRS, hsdp⟩ := hsdp
  let w := pitmanCode (fun i => ω (i + 1))
  have hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  refine ⟨hfin, hL, ht, hR, Q, hQ, G, hG, hpos, harc, hface, fun x hx =>
    ⟨hldp x hx, ?_⟩⟩
  rw [hG]
  have hiff : ∀ P : InfinitePresentPath w ⟨x⟩,
      (P.HasShortestSegments ∧ ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasShortestSegments →
        InBetweenLeftmostRightmost w hfin hL ht hR x P
          (kmswRightmostPath w hfin hL ht hR x) P') ↔
      (P.HasShortestSegments ∧ ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasShortestSegments →
        pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P'.edge i, false)) ⊆
          closedBetween (pathTrace (monotoneLimitDrawing w hfin hfam)
              (fun i => (P.edge i, false)))
            (pathTrace (monotoneLimitDrawing w hfin hfam)
              (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) := by
    intro P
    refine and_congr_right (fun _ => forall_congr' (fun P' => imp_congr_right (fun _ => ?_)))
    exact ⟨trace_subset_closedBetween_of_inBetween w hfin hL ht hR hfam x P _ P',
      inBetween_of_trace_subset_closedBetween w hfin hL ht hR hfam x P _ P'⟩
  obtain ⟨es, ⟨P, hPes, hP, hleft⟩, huniq⟩ := hsdp x
  refine ⟨P, (hiff P).mp ⟨hP, hleft⟩, ?_⟩
  intro P' hP'
  obtain ⟨hshort, hbetween⟩ := (hiff P').mpr hP'
  exact infinitePresentPath_eq_of_edge_eq w P P'
    ((huniq P'.edge ⟨P', rfl, hshort, hbetween⟩).trans hPes.symm)

end DirectedDistances.PaperProofs.Section4
