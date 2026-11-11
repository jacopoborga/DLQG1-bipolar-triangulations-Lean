/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundaryOrder3






public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ}

/-- Helper toward Lemma 5.5: the corrected primed dart embedding preserves
both geometric endpoints, including the terminal endpoint of a traversal. -/
theorem lPlus_primed_dart_endpoints
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (d : ℕ × Bool) :
    kmswDartEndpoint (shiftedStream W 0) (lMinusPrimedDartImage hτ d) =
        boundaryGluingPrimedVertexMap W h k hτ
          (kmswDartEndpoint
            (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) d) ∧
      kmswDartEndpoint (shiftedStream W 0)
          ((lMinusPrimedDartImage hτ d).1, !(lMinusPrimedDartImage hτ d).2) =
        boundaryGluingPrimedVertexMap W h k hτ
          (kmswDartEndpoint
            (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
            (d.1, !d.2)) := by
  constructor
  · exact lMinusPrimedDartImage_endpoint hτ d
  · have hn : lMinusPrimedDartImage hτ (d.1, !d.2) =
        ((lMinusPrimedDartImage hτ d).1, !(lMinusPrimedDartImage hτ d).2) := by
      apply Prod.ext
      · rfl
      change (!d.2 ^^ primedLimitSideFlip _ hτ d.1) =
        !(d.2 ^^ primedLimitSideFlip _ hτ d.1)
      cases d.2 <;> cases primedLimitSideFlip _ hτ d.1 <;> rfl
    rw [← hn]
    exact lMinusPrimedDartImage_endpoint hτ (d.1, !d.2)

/-- Helper toward Lemma 5.5: the corrected geometric embedding distinguishes
all primed darts, retaining both endpoint bits of each missing edge. -/
theorem lPlus_primed_dart_image_injective
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    Function.Injective (lMinusPrimedDartImage hτ) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  have he : boundaryGluingPrimedEdgeMap W h k hτ a =
      boundaryGluingPrimedEdgeMap W h k hτ c := congrArg Prod.fst heq
  have hac := boundaryGluingPrimedEdgeMap_injective W h k hτ he
  subst c
  have hb : (b ^^ primedLimitSideFlip _ hτ a) =
      (d ^^ primedLimitSideFlip _ hτ a) := congrArg Prod.snd heq
  exact Prod.ext rfl (Bool.xor_left_inj.mp hb)

/-- Helper toward Lemma 5.5: every ordered prefix dart has a unique primed
representative with the corrected endpoint bit. This uses geometric overlap,
and does not yet assert membership in an independently ordered boundary list. -/
theorem lPlus_prefix_primed_dart_exists_unique
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (d : ℕ × Bool)
    (hd : d ∈ lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)) :
    ∃! b : ℕ × Bool, lMinusPrimedDartImage hτ b = d := by
  have hmem := lPlusPrefixUpperLeftDarts_mem d hd
  obtain ⟨e, he⟩ :=
    boundaryGluingUpperLeftEdges_subset_primedEdges W h k hτ hfin hmem
  let b : ℕ × Bool :=
    (e, d.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ e)
  have hb : lMinusPrimedDartImage hτ b = d := by
    apply Prod.ext he
    change ((d.2 ^^ primedLimitSideFlip _ hτ e) ^^
      primedLimitSideFlip _ hτ e) = d.2
    cases d.2 <;> cases primedLimitSideFlip _ hτ e <;> rfl
  exact ⟨b, hb, fun c hc => lPlus_primed_dart_image_injective hτ (hc.trans hb.symm)⟩

/-- Helper toward Lemma 5.5: the ordered prefix has a unique list of primed
dart representatives. Equality of mapped lists records every edge ID and the
corrected bit in its original index order. Boundary membership is separate. -/
theorem lPlus_prefix_primed_dart_list_exists_unique
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    ∃! q : List (ℕ × Bool), q.map (lMinusPrimedDartImage hτ) =
      lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k) := by
  have hex : ∀ p : List (ℕ × Bool),
      (∀ d ∈ p, ∃ b, lMinusPrimedDartImage hτ b = d) →
      ∃ q : List (ℕ × Bool), q.map (lMinusPrimedDartImage hτ) = p := by
    intro p
    induction p with
    | nil => exact fun _ => ⟨[], rfl⟩
    | cons d p ih =>
      intro hp
      obtain ⟨b, hb⟩ := hp d List.mem_cons_self
      obtain ⟨q, hq⟩ := ih (fun e he => hp e (List.mem_cons_of_mem d he))
      exact ⟨b :: q, by rw [List.map_cons, hb, hq]⟩
  obtain ⟨q, hq⟩ := hex _ (fun d hd =>
    (lPlus_prefix_primed_dart_exists_unique hτ hfin d hd).exists)
  refine ⟨q, hq, fun r hr => ?_⟩
  exact List.map_injective_iff.mpr (lPlus_primed_dart_image_injective hτ)
    (hr.trans hq.symm)

/-- Helper toward Lemma 5.5: the unique primed lift has the same length,
geometric edge at every index, corrected local bit, and both embedded
endpoints. This is transport of the prefix order, not yet an independent
identification with the primed left-boundary order. -/
theorem lPlus_prefix_primed_dart_list_transport
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    let p := lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)
    ∃ q : List (ℕ × Bool), ∃ hlen : q.length = p.length,
      q.map (lMinusPrimedDartImage hτ) = p ∧
      ∀ i : Fin q.length,
        let a := p[i.val]'(hlen ▸ i.isLt)
        let b := q[i]
        a.1 = boundaryGluingPrimedEdgeMap W h k hτ b.1 ∧
          a.2 = (b.2 ^^ primedLimitSideFlip
            (boundaryGluingFutureStream W h k) hτ b.1) ∧
          kmswDartEndpoint (shiftedStream W 0) a =
            boundaryGluingPrimedVertexMap W h k hτ
              (kmswDartEndpoint
                (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) b) ∧
          kmswDartEndpoint (shiftedStream W 0) (a.1, !a.2) =
            boundaryGluingPrimedVertexMap W h k hτ
              (kmswDartEndpoint
                (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
                (b.1, !b.2)) := by
  dsimp only
  obtain ⟨q, hq, _⟩ := lPlus_prefix_primed_dart_list_exists_unique hτ hfin
  have hlen : q.length =
      (lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)).length := by
    simpa only [List.length_map] using congrArg List.length hq
  refine ⟨q, hlen, hq, ?_⟩
  intro i
  have hip : i.val <
      (lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)).length := by omega
  have hi : lMinusPrimedDartImage hτ q[i] =
      (lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k))[i.val] := by
    have hh := congrArg (fun r : List (ℕ × Bool) => r[i.val]?) hq
    simpa only [List.getElem?_map, List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem hip, Option.map_some,
      Option.some.injEq, Fin.getElem_fin] using hh
  refine ⟨(congrArg Prod.fst hi).symm, (congrArg Prod.snd hi).symm, ?_, ?_⟩
  · rw [← hi]
    exact (lPlus_primed_dart_endpoints hτ q[i]).1
  · rw [← hi]
    exact (lPlus_primed_dart_endpoints hτ q[i]).2

/-- Helper toward Lemma 5.5: the stopped prefix chain has consecutive
limit-level endpoints, so no finite-stage endpoint is silently substituted. -/
theorem lPlus_prefix_upper_left_dart_endpoint_chain :
    List.IsChain (fun a b : ℕ × Bool =>
      kmswDartEndpoint (shiftedStream W 0) (a.1, !a.2) =
        kmswDartEndpoint (shiftedStream W 0) b)
      (lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  have hbound (d : ℕ × Bool)
      (hd : d ∈ lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)) :
      d.1 < (kmswStage w t).nextEdge := by
    have hm := lPlusPrefixUpperLeftDarts_mem d hd
    have he : d.1 ∈ (kmswStage w t).UL := List.mem_of_mem_dropLast hm
    apply (kmswStage_boundary_ids_lt_nextEdge w t).2 d.1
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl he))
  apply (lPlusPrefixUpperLeftDarts_chain (W := W) (h := h) (k := k)).imp_of_mem_imp
  intro a b ha hb hab
  obtain ⟨haBit, hbBit, hend⟩ := hab
  simp only [kmswDartEndpoint, haBit, hbBit, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  exact ((edge_endpoints_eq w (hbound a ha)).1.symm.trans hend).trans
    (edge_endpoints_eq w (hbound b hb)).2

/-- Helper toward Lemma 5.5: the unique corrected primed lift is a local
geometric dart chain.
This does not replace the remaining independent left-boundary order proof. -/
theorem lPlus_prefix_primed_dart_chain
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    ∃ q : List (ℕ × Bool),
      q.map (lMinusPrimedDartImage hτ) =
        lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k) ∧
      List.IsChain (fun a b : ℕ × Bool =>
        kmswDartEndpoint
            (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
            (a.1, !a.2) =
          kmswDartEndpoint
            (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) b) q := by
  obtain ⟨q, hq, _⟩ := lPlus_prefix_primed_dart_list_exists_unique hτ hfin
  refine ⟨q, hq, ?_⟩
  have hc := lPlus_prefix_upper_left_dart_endpoint_chain
    (W := W) (h := h) (k := k)
  rw [← hq] at hc
  apply (List.isChain_map (lMinusPrimedDartImage hτ)).mp hc |>.imp
  intro a b hab
  have hv : Function.Injective (boundaryGluingPrimedVertexMap W h k hτ) := by
    apply (boundaryGluingFutureVertexMap_injective W h k).comp
    intro v z hvz
    exact (primedLimit_maps_injective_on_allocated
      (boundaryGluingFutureStream W h k) hτ).2
      ((primedLocalIds_eventually_allocated (boundaryGluingFutureStream W h k) hτ).2 v)
      ((primedLocalIds_eventually_allocated (boundaryGluingFutureStream W h k) hτ).2 z) hvz
  apply hv
  rw [← (lPlus_primed_dart_endpoints hτ a).2,
    ← (lPlus_primed_dart_endpoints hτ b).1]
  exact hab

/-- Helper toward Lemma 5.5: the lifted prefix representative is identified
by the very same overlap relation used by `lPlusGluedDartEquiv`. The bit is
transported by the primed side flip, rather than uniformly reversed. -/
theorem lPlus_prefix_primed_glued_representative
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hk : 0 ≤ k) (d : ℕ × Bool)
    (hd : d ∈ lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)) :
    ∃ (ha : d.1 ∈ boundaryGluingPrefixMinusEdges W h k) (b : ℕ × Bool),
      (⟦Sum.inl ⟨d, ha⟩⟧ : LPlusGluedDart longest hqMode hτ) =
          ⟦Sum.inr (Sum.inl b)⟧ ∧
        d.1 = boundaryGluingPrimedEdgeMap W h k hτ b.1 ∧
        d.2 = (b.2 ^^ primedLimitSideFlip
          (boundaryGluingFutureStream W h k) hτ b.1) := by
  have hu := lPlusPrefixUpperLeftDarts_mem d hd
  have hkpos : 0 < k := by
    by_contra hn
    have hz := boundaryGluingUpperLeftEdges_of_nonpos W h k (by omega)
    rw [hz] at hu
    exact hu
  have ha : d.1 ∈ boundaryGluingPrefixMinusEdges W h k := by
    have hm : d.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        boundaryGluingPrimedEdges W h k hτ := by
      rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin hk]
      exact hu
    exact hm.1
  obtain ⟨b, hb, _⟩ := lPlus_prefix_primed_dart_exists_unique hτ hfin d hd
  have he : d.1 = boundaryGluingPrimedEdgeMap W h k hτ b.1 :=
    (congrArg Prod.fst hb).symm
  have hbit : d.2 = (b.2 ^^ primedLimitSideFlip
      (boundaryGluingFutureStream W h k) hτ b.1) := (congrArg Prod.snd hb).symm
  refine ⟨ha, b, ?_, he, hbit⟩
  exact (lPlusPrefixPrimedGluedDart_eq_iff
    (hτ := hτ) (hqMode := hqMode) (hfin := hfin) (hk := hkpos) ⟨d, ha⟩ b).mpr
      ⟨he, hbit, hu⟩






































































end DirectedDistances.PaperProofs.Section5
