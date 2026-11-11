/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.LeftmostGeodesicSubmap

/-! Supporting lemmas for paper labels `def-infinite-geo`, `lem-geo-exist` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory Quiver Filter DirectedDistances.RandomWalk DirectedDistances.KMSW



theorem geo_exist :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∀ x : ℕ, (∃ n, x < (kmswStage w n).nextVertex) →
          ∃! P : InfinitePresentPath w ⟨x⟩, P.HasLongestSegments ∧
            ∀ Q : InfinitePresentPath w ⟨x⟩, Q.HasLongestSegments →
              InBetweenLeftmostRightmost w hfin hL ht hR x P
                (kmswRightmostPath w hfin hL ht hR x) Q := by
  filter_upwards [pitmanCodes_ae_exists_unique_inBetweenLeftmostRightmostLdp] with ω hω
  obtain ⟨hfin, hL, ht, hR, hall⟩ := hω
  let w := pitmanCode (fun i => ω (i + 1))
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
  refine ⟨hfin, hL, ht, hR, fun x _hx => ?_⟩
  obtain ⟨es, ⟨P, hPes, hP, hleft⟩, huniq⟩ := hall x
  refine ⟨P, ⟨hP, hleft⟩, ?_⟩
  rintro Q ⟨hQ, hQleft⟩
  have he : Q.edge = P.edge :=
    (huniq Q.edge ⟨Q, rfl, hQ, hQleft⟩).trans hPes.symm
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

end DirectedDistances.PaperProofs.Section4
