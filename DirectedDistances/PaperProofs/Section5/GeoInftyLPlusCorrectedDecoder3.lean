/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCorrectedDecoder

/-! Formalization-internal decoder correction/analysis, not a manuscript change.
This continuation studies terminal non-port darts using explicit block
representatives. It makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "es" => List.reverse (List.dropLast
  (State.UL (kmswStage w (boundaryHitTime w h k))))
local notation "IP" => lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IT" => lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IH" => lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)

/-- Helper toward Lemma 5.5: no terminal-star dart has a hatted
representative, including hatted non-port darts. -/
theorem lPlus_terminal_not_hatted (hn : 0 < (es).length) (d : Q)
    (hv : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    d ∉ Set.range IH := by
  rintro ⟨a, ha⟩
  have he := congrArg (fun q => kmswLimitDartVertex w (D q).val) ha
  exact lPlus_upperLeft_west_not_hatted hτ ((es).length - 1) _
    (List.getElem?_eq_getElem (by omega)) a.val (hv.symm.trans he.symm)

include hfin hk in
/-- Helper toward Lemma 5.5: excluding all attachment ports makes the
prefix and primed representative classes disjoint. This uses the exact
edge intersection, preserving dart bits and edge identities. -/
theorem lPlus_nonport_prefix_not_primed (p : LPlusPrefixDart W h k)
    (hport : ∀ j : Fin (es).length, ∀ b : Bool, p.val ≠ (es[j.val], b)) :
    IP p ∉ Set.range IT := by
  rintro ⟨q, hq⟩
  have he : lMinusPrimedDartImage hτ q = p.val :=
    (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hq
  have hm : p.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
      boundaryGluingPrimedEdges W h k hτ :=
    ⟨p.property, he ▸ (show (lMinusPrimedDartImage hτ q).1 ∈
      boundaryGluingPrimedEdges W h k hτ from ⟨q.1, rfl⟩)⟩
  rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin hk] at hm
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (List.mem_reverse.mpr hm)
  exact hport ⟨j, hj⟩ p.val.2 (Prod.ext hje.symm rfl)

/-- Helper toward Lemma 5.5: every terminal non-port dart is exclusively
a prefix dart or a primed dart. No hatted or shared class remains. -/
theorem lPlus_terminal_nonport_block_classification
    (hn : 0 < (es).length) (d : Q)
    (hv : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : ∀ j : Fin (es).length, ∀ b : Bool, (D d).val ≠ (es[j.val], b)) :
    (∃ p : LPlusPrefixDart W h k, d = IP p ∧ d ∉ Set.range IT) ∨
      (∃ p : ℕ × Bool, d = IT p ∧ d ∉ Set.range IP) := by
  have hnotH := lPlus_terminal_not_hatted hτ hp P hqMode Tpath hfin hleft hk hn d hv
  revert hport hnotH
  induction d using Quotient.inductionOn with
  | h a =>
    intro hport hnotH
    rcases a with p | (p | a)
    · exact Or.inl ⟨p, rfl,
        lPlus_nonport_prefix_not_primed hτ hqMode hfin hk p hport⟩
    · refine Or.inr ⟨p, rfl, ?_⟩
      rintro ⟨q, hq⟩
      have hnq := lPlus_nonport_prefix_not_primed hτ hqMode hfin hk q
        (fun j b he => hport j b (by rw [← hq]; exact he))
      exact hnq ⟨p, hq.symm⟩
    · exact (hnotH ⟨a, rfl⟩).elim

/-- Helper toward Lemma 5.5: after the first fresh-left triangle, the
only old darts at its new lower-left vertex are `(1,false)` and `(2,false)`.
The missing edge with ID 2 is retained geometrically. -/
theorem lPlus_first_left_vertex_two_iff (hc₀ : w 0 = 0)
    (e : ℕ) (he : e < 3) (b : Bool) :
    kmswLimitDartVertex w (e, b) = 2 ↔ (e = 1 ∨ e = 2) ∧ b = false := by
  have hs : (kmswStage w 1).nextEdge = 3 := by
    simp [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  obtain ⟨hw, ht⟩ := edge_endpoints_eq w (j := 1) (e := e) (by omega)
  simp only [kmswLimitDartVertex, ← hw, ← ht]
  interval_cases e <;> cases b <;>
    simp [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]

/-- Helper toward Lemma 5.5: in the left/down cylinder, the terminal
prefix star consists of exactly the attachment dart and the old missing
lower-left dart. -/
theorem lPlus_left_down_prefix_terminal_darts
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2)
    (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val = 2) :
    p.val = (1, false) ∨ p.val = (2, false) := by
  subst k
  have htime := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hpref := (Set.ext_iff.mp (lPlusPrefixMinusEdges_eq_previousStage
    (W := W) (h := h) (by omega : 0 < (1 : ℤ))) p.val.1).mp p.property
  have hprev : boundaryHitTime w h 1 - 1 = 1 := by omega
  change p.val.1 < (kmswStage w (boundaryHitTime w h 1 - 1)).nextEdge at hpref
  rw [hprev] at hpref
  have hbound : p.val.1 < 3 := by
    simpa [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge] using hpref
  obtain ⟨he, hb⟩ := (lPlus_first_left_vertex_two_iff hc₀ p.val.1 hbound p.val.2).mp hv
  exact he.elim (fun he => Or.inl (Prod.ext he hb))
    (fun he => Or.inr (Prod.ext he hb))

/-- Helper toward Lemma 5.5: the left/down cylinder has a single
upper-left attachment edge, with geometric ID 1. -/
theorem lPlus_left_down_attachment_eq
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) : es = [1] := by
  subst k
  rw [lPlus_hit_one_of_left_down (h := h) hc₀ hc₁]
  simp [kmswStage, hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep,
    kmswInit, State.addEdge]

include hfin hk in
/-- Helper toward Lemma 5.5: the old missing lower-left dart is outside
the primed block in the left/down cylinder. -/
theorem lPlus_left_down_lowerLeft_not_primed
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    (2, false) ∉ Set.range (lMinusPrimedDartImage hτ) := by
  subst k
  have ht := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hpref : 2 ∈ boundaryGluingPrefixMinusEdges W h 1 := by
    rw [lPlusPrefixMinusEdges_eq_previousStage (W := W) (h := h)
      (by omega : 0 < (1 : ℤ))]
    change 2 < (kmswStage w (boundaryHitTime w h 1 - 1)).nextEdge
    have hprev : boundaryHitTime w h 1 - 1 = 1 := by omega
    rw [hprev]
    simp [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  rintro ⟨p, hp⟩
  have hm : 2 ∈ boundaryGluingPrefixMinusEdges W h 1 ∩
      boundaryGluingPrimedEdges W h 1 hτ :=
    ⟨hpref, ⟨p.1, congrArg Prod.fst hp⟩⟩
  rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h 1 hτ hfin hk] at hm
  have hes := lPlus_left_down_attachment_eq (h := h) rfl hc₀ hc₁
  have hm' : 2 ∈ (List.reverse (List.dropLast
      (State.UL (kmswStage w (boundaryHitTime w h 1))))) := List.mem_reverse.mpr hm
  rw [hes] at hm'
  simp at hm'

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: in the left/down terminal star, the full
side adds exactly the old lower-left dart to the primed block. -/
theorem lPlus_left_down_terminal_side_mem_iff
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2)
    (x : ℕ × Bool) (hv : kmswLimitDartVertex w x = 2) :
    x.1 ∈ (S).edges ↔ x ∈ Set.range (lMinusPrimedDartImage hτ) ∨ x = (2, false) := by
  have hes := lPlus_left_down_attachment_eq (h := h) hk₁ hc₀ hc₁
  have hn : 0 < (es).length := by rw [hes]; decide
  let i : Fin (es).length := ⟨0, hn⟩
  have hei : es[i.val] = 1 := by simp [i, hes]
  obtain ⟨q, hq, _⟩ := lPlusUpperLeftGluedDart_primed_representative
    hτ hqMode hfin hk i false
  have ht : (1, false) ∈ Set.range (lMinusPrimedDartImage hτ) :=
    ⟨q, by simpa only [hei] using hq⟩
  have hvertex : kmswLimitDartVertex w (1, false) = 2 :=
    (lPlus_first_left_vertex_two_iff hc₀ 1 (by omega) false).mpr ⟨Or.inl rfl, rfl⟩
  change x ∈ {d : ℕ × Bool | d.1 ∈ (S).edges} ↔ _
  rw [← lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
  constructor
  · rintro ⟨p | (p | a), he⟩
    · have hclass := lPlus_left_down_prefix_terminal_darts hk₁ hc₀ hc₁ p
        ((congrArg (kmswLimitDartVertex w) he).trans hv)
      rcases hclass with hclass | hclass
      · have hx : x = (1, false) := he.symm.trans hclass
        exact Or.inl (hx.symm ▸ ht)
      · exact Or.inr (he.symm.trans hclass)
    · exact Or.inl ⟨p, he⟩
    · have hvi : kmswLimitDartVertex w (es[i.val], false) = 2 := by
        simpa only [hei] using hvertex
      exact (lPlus_upperLeft_west_not_hatted hτ i.val _
        (List.getElem?_eq_getElem i.isLt) a.val
          (hvi.trans
            (hv.symm.trans (congrArg (kmswLimitDartVertex w) he.symm)))).elim
  · rintro (⟨p, hp⟩ | rfl)
    · exact ⟨.inr (.inl p), hp⟩
    · obtain ⟨d, t, hd, _, _, _⟩ := lPlusGluedCorrectedRotation4_transports_left_down
        hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁
      rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
      exact hd ▸ (D d).property

include hqMode Tpath hleft hk in
/-- Helper toward Lemma 5.5: actual first returns in the left/down
terminal primed star. Its own-block predecessor of the attachment returns
instead to the old lower-left dart; every other primed input keeps its
own-block successor. No first-return premise is assumed. -/
theorem lPlus_left_down_terminal_primed_side_rotation
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2)
    (p : ℕ × Bool)
    (hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) = 2) :
    let y := lMinusPrimedDartImage hτ
      (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p)
    (S).rotation (lMinusPrimedDartImage hτ p)
      (if y = (1, false) then (2, false) else y) := by
  let σ := kmswInfRot w (H.1 0)
  let x := lMinusPrimedDartImage hτ p
  let y := lMinusPrimedDartImage hτ
    (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) p)
  change (S).rotation x (if y = (1, false) then (2, false) else y)
  have hσ : σ (2, false) = (1, false) :=
    (lPlus_first_left_lowerLeft_rotations (H := H) hc₀).1
  have hnot := lPlus_left_down_lowerLeft_not_primed hτ hfin hk hk₁ hc₀ hc₁
  have hxb : x ≠ (2, false) := fun hx => hnot ⟨p, hx⟩
  have hes := lPlus_left_down_attachment_eq (h := h) hk₁ hc₀ hc₁
  have hn : 0 < (es).length := by rw [hes]; decide
  let i : Fin (es).length := ⟨0, hn⟩
  obtain ⟨q, hq, _⟩ := lPlusUpperLeftGluedDart_primed_representative
    hτ hqMode hfin hk i false
  have ht : (1, false) ∈ Set.range (lMinusPrimedDartImage hτ) :=
    ⟨q, by simpa [i, hes] using hq⟩
  obtain ⟨n, hn, hend, hgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  change (σ : _ → _)^[n] x = y at hend
  have hstep (j : ℕ) : σ ((σ : _ → _)^[j] x) = (σ : _ → _)^[j + 1] x :=
    (Function.iterate_succ_apply' ..).symm
  have hvertex (j : ℕ) : kmswLimitDartVertex w ((σ : _ → _)^[j] x) = 2 := by
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) x _).mp
      ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩).symm.trans hv
  have hmem (j : ℕ) (hj : (((σ : _ → _)^[j] x).1 ∈ (S).edges)) :
      (σ : _ → _)^[j] x ∈ Set.range (lMinusPrimedDartImage hτ) ∨
        (σ : _ → _)^[j] x = (2, false) :=
    (lPlus_left_down_terminal_side_mem_iff hτ hp P hqMode Tpath hfin hleft hk
      hk₁ hc₀ hc₁ _ (hvertex j)).mp hj
  by_cases hy : y = (1, false)
  · rw [ite_eq_left hy]
    have hn2 : 1 < n := by
      by_contra hh
      have hn1 : n = 1 := by omega
      have he : σ x = σ (2, false) := by
        simpa only [hn1, Function.iterate_one, hy, hσ] using hend
      exact hxb (σ.injective he)
    have he : (σ : _ → _)^[n - 1] x = (2, false) := by
      apply σ.injective
      rw [hstep, Nat.sub_add_cancel hn, hend, hy, hσ]
    refine ⟨n - 1, by omega, he, ?_⟩
    intro j hj hjn hjmem
    rcases hmem j hjmem with hjprime | hjb
    · exact hgap j hj (by omega) hjprime
    · have he' : (σ : _ → _)^[j + 1] x = (1, false) := by
        rw [← hstep, hjb, hσ]
      exact hgap (j + 1) (by omega) (by omega) (he'.symm ▸ ht)
  · rw [ite_eq_right hy]
    refine ⟨n, hn, hend, ?_⟩
    intro j hj hjn hjmem
    rcases hmem j hjmem with hjprime | hjb
    · exact hgap j hj hjn hjprime
    · have he' : (σ : _ → _)^[j + 1] x = (1, false) := by
        rw [← hstep, hjb, hσ]
      by_cases hlt : j + 1 < n
      · exact hgap (j + 1) (by omega) hlt (he'.symm ▸ ht)
      · have heq : j + 1 = n := by omega
        exact hy (hend.symm.trans (heq ▸ he'))

/-- Helper toward Lemma 5.5: the finite-prefix successor of the terminal
port is the old lower-left dart in the left/down cylinder. -/
theorem lPlus_left_down_prefix_terminal_successor
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2)
    (t : Q) (ht : (D t).val = (1, false)) :
    (D (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk t)).val =
      (2, false) := by
  subst k
  have htime := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hprev : boundaryHitTime w h 1 - 1 = 1 := by omega
  have hmem (e : ℕ) (he : e < 3) : e ∈ boundaryGluingPrefixMinusEdges W h 1 := by
    rw [lPlusPrefixMinusEdges_eq_previousStage (W := W) (h := h)
      (by omega : 0 < (1 : ℤ))]
    change e < (kmswStage w (boundaryHitTime w h 1 - 1)).nextEdge
    rw [hprev]
    simpa [kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge] using he
  let p : LPlusPrefixDart W h 1 := ⟨(1, false), hmem 1 (by omega)⟩
  let r : LPlusPrefixDart W h 1 := ⟨(2, false), hmem 2 (by omega)⟩
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := 1) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  obtain ⟨ha, hb, hstage⟩ := lPlus_terminal_stage_of_first_left hc₀
  have hPR : PR p = r := by
    rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk
      (by omega : 0 < (1 : ℤ))]
    apply Subtype.ext
    have hlocal : ∀ (n : ℕ) (hn : n = 1) (he : 1 < (kmswStage w n).nextEdge),
        ((stageRot w n (⟨1, he⟩, false)).1.val,
          (stageRot w n (⟨1, he⟩, false)).2) = (2, false) := by
      intro n hn he
      subst n
      exact congrArg (fun q : StageDart (kmswStage w 1).nextEdge => (q.1.val, q.2)) hstage
    exact hlocal _ hprev _
  have hpt : lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode) p = t := by
    apply (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk).injective
    exact Subtype.ext ht.symm
  rw [← hpt]
  have he := (PR.extendDomain_apply_image
    (Equiv.ofInjective _ (lPlusPrefixGluedDart_injective
      (hτ := hτ) (hqMode := hqMode))) p).trans
    (congrArg (lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)) hPR)
  exact congrArg (fun d =>
    (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk d).val) he

/-- Helper toward Lemma 5.5: rotation 4 computes the correct actual
first return for both terminal primed non-port classes in the left/down
cylinder, including the primed predecessor of the terminal port. -/
theorem lPlusGluedCorrectedRotation4_left_down_primed_nonport_rotation_iff
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2)
    (p : ℕ × Bool)
    (hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) = 2)
    (hport : lMinusPrimedDartImage hτ p ≠ (1, false)) (e : Q) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk (IT p) = e ↔
      (S).rotation (D (IT p)).val (D e).val := by
  let d := IT p
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let y := TE d
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hes := lPlus_left_down_attachment_eq (h := h) hk₁ hc₀ hc₁
  have hn : 0 < (es).length := by rw [hes]; decide
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(es).length - 1, by omega⟩, false)
  have htv : (D t).val = (1, false) := by
    change (es[(es).length - 1], false) = _
    simp [hes]
  let b := PE t
  have hbv : (D b).val = (2, false) :=
    lPlus_left_down_prefix_terminal_successor hτ hp P hqMode Tpath hfin hleft hk
      hk₁ hc₀ hc₁ t htv
  have hbnot : b ∉ Set.range IT := by
    rintro ⟨q, hq⟩
    exact lPlus_left_down_lowerLeft_not_primed hτ hfin hk hk₁ hc₀ hc₁
      ⟨q, (congrArg (fun a => (D a).val) hq).trans hbv⟩
  have hdt : d ≠ t := fun he => hport
    ((congrArg (fun a => (D a).val) he).trans htv)
  have hnotP : d ∉ Set.range IP := by
    rintro ⟨q, hq⟩
    have he := congrArg (fun a => (D a).val) hq
    have hc := lPlus_left_down_prefix_terminal_darts hk₁ hc₀ hc₁ q
      ((congrArg (kmswLimitDartVertex w) he).trans hv)
    rcases hc with hc | hc
    · exact hport (he.symm.trans hc)
    · exact lPlus_left_down_lowerLeft_not_primed hτ hfin hk hk₁ hc₀ hc₁
        ⟨p, he.symm.trans hc⟩
  have hnotUL : d ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnotP ⟨⟨(_, j.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk j.1⟩, hj⟩
  have hTE : y = IT (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) p) :=
    (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin)).extendDomain_apply_image _ p
  have hyv : kmswLimitDartVertex w (D y).val = 2 := by
    obtain ⟨n, _, he, _⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
    rw [hTE]
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow,
        lPlusPrimedGluedDart, lPlusGluedDartEquivNonneg_mk,
        lPlusBlockDartImage, lMinusPrimedDartImage] using he⟩).symm.trans hv
  have hnotH : y ∉ Set.range IH :=
    lPlus_terminal_not_hatted hτ hp P hqMode Tpath hfin hleft hk hn y
      (hyv.trans (by change 2 = kmswLimitDartVertex w (D t).val; rw [htv]; exact
        ((lPlus_first_left_vertex_two_iff hc₀ 1 (by omega) false).mpr
          ⟨Or.inl rfl, rfl⟩).symm))
  have hnotB : y ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨j, hj⟩
    exact hnotH ⟨_, hj⟩
  have hRd : R d = y := by
    change lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode (TE
        (lPlusUpperLeftCornerRotation hτ hqMode hfin hk (PE d)))) = y
    rw [show PE d = d from Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP,
      show lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d from
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL]
    change lPlusHattedExtendedRotation hτ hqMode (lPlusBetaCornerRotation hτ hqMode y) = y
    rw [show lPlusBetaCornerRotation hτ hqMode y = y from
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB]
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
  obtain ⟨t', ht', hRt'⟩ := lPlus_terminal_corrected_of_left_down
    hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁
  have ht't : t' = t := (D).injective (Subtype.ext (ht'.trans htv.symm))
  have hRt : R t = b := (D).injective (Subtype.ext
    ((ht't ▸ hRt').trans hbv.symm))
  have hyt : y ≠ TE t := fun he => hdt (TE.injective he)
  have hyb : y ≠ b := by
    intro he
    rw [hTE] at he
    exact hbnot ⟨_, he⟩
  have htb : t ≠ b := by
    intro he
    have hh := (congrArg (fun a => (D a).val) he)
    rw [htv, hbv] at hh
    exact (by decide : (1, false) ≠ (2, false)) hh
  have hcalc : lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d =
      if y = t then b else y := by
    rw [lPlusGluedCorrectedRotation4_apply hτ hp P hqMode Tpath hfin hleft hk hn]
    change Equiv.swap t b (lPlusGluedCorrectedRotation2
      hτ hp P hqMode Tpath hfin hleft hk d) = _
    rw [lPlusGluedCorrectedRotation2_eq_blockRotation2 hτ hqMode hfin hk hp P Tpath hleft]
    unfold lPlusGluedBlockRotation2
    rw [dite_eq_left hn]
    change Equiv.swap t b (Equiv.swap (R t) (TE t) (R d)) = _
    rw [hRt, hRd, Equiv.swap_apply_of_ne_of_ne hyb hyt]
    by_cases hyt' : y = t
    · rw [ite_eq_left hyt', hyt', Equiv.swap_apply_left]
    · rw [ite_eq_right hyt', Equiv.swap_apply_of_ne_of_ne hyt' hyb]
  have hactual := lPlus_left_down_terminal_primed_side_rotation
    hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁ p hv
  dsimp only at hactual
  have hrot : (S).rotation (D d).val
      (D (lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d)).val := by
    rw [hcalc]
    by_cases hy : y = t
    · rw [ite_eq_left hy, hbv]
      have he : lMinusPrimedDartImage hτ
          (kmswInfRot (primedCode (primedSimInput U) hτ)
            (primedCode_finiteIncidence U hτ hfin) p) = (1, false) := by
        exact (congrArg (fun a => (D a).val) (hTE.symm.trans hy)).trans htv
      rw [ite_eq_left he] at hactual
      simpa only [d, lPlusPrimedGluedDart,
        lPlusGluedDartEquivNonneg_mk, lPlusBlockDartImage, lMinusPrimedDartImage] using hactual
    · rw [ite_eq_right hy]
      have he : lMinusPrimedDartImage hτ
          (kmswInfRot (primedCode (primedSimInput U) hτ)
            (primedCode_finiteIncidence U hτ hfin) p) ≠ (1, false) := by
        intro he
        exact hy ((D).injective (Subtype.ext
          ((congrArg (fun a => (D a).val) hTE).trans (he.trans htv.symm))))
      rw [hTE]
      rw [ite_eq_right he] at hactual
      simpa only [d, lPlusPrimedGluedDart,
        lPlusGluedDartEquivNonneg_mk, lPlusBlockDartImage, lMinusPrimedDartImage] using hactual
  constructor
  · intro he
    exact he ▸ hrot
  · intro he
    have huniq := firstReturn_endpoint_unique (kmswInfRot w (H.1 0) : _ → _)
      {a : ℕ × Bool | a.1 ∈ (S).edges}
      (D (lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d)).property
      (D e).property hrot he
    exact (D).injective (Subtype.ext huniq)

/-- Helper toward Lemma 5.5: rotation 4 transports every dart in the
left/down cylinder. This is a conditional code-cylinder result, retaining
all geometric and probabilistic witness binders of the decoder. -/
theorem lPlusGluedCorrectedRotation4_left_down_rotation_iff
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) (d e : Q) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
      (S).rotation (D d).val (D e).val := by
  have hes := lPlus_left_down_attachment_eq (h := h) hk₁ hc₀ hc₁
  have hn : 0 < (es).length := by rw [hes]; decide
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(es).length - 1, by omega⟩, false)
  have htv : (D t).val = (1, false) := by
    change (es[(es).length - 1], false) = _
    simp [hes]
  have hvertex : kmswLimitDartVertex w (1, false) = 2 :=
    (lPlus_first_left_vertex_two_iff hc₀ 1 (by omega) false).mpr ⟨Or.inl rfl, rfl⟩
  by_cases hv : kmswLimitDartVertex w (D d).val = 2
  · rcases (lPlus_left_down_terminal_side_mem_iff hτ hp P hqMode Tpath hfin hleft hk
      hk₁ hc₀ hc₁ (D d).val hv).mp (D d).property with ⟨p, hp'⟩ | hb
    · have hd : d = IT p := (D).injective (Subtype.ext hp'.symm)
      by_cases hport : lMinusPrimedDartImage hτ p = (1, false)
      · have hdt : d = t := (D).injective (Subtype.ext (hp'.symm.trans (hport.trans htv.symm)))
        rw [hdt]
        exact lPlusGluedCorrectedRotation4_terminal_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk hn e
      · rw [hd]
        exact lPlusGluedCorrectedRotation4_left_down_primed_nonport_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁ p
          ((congrArg (kmswLimitDartVertex w) hp').trans hv) hport e
    · obtain ⟨b, t', hb', ht', hbt, hrot⟩ :=
        lPlusGluedCorrectedRotation4_transports_left_down
          hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁
      have hdb : d = b := (D).injective (Subtype.ext (hb.trans hb'.symm))
      rw [hdb]
      constructor
      · intro he
        have ht'e : t' = e := hbt.symm.trans he
        exact ht'e ▸ hrot
      · intro he
        have huniq := firstReturn_endpoint_unique (kmswInfRot w (H.1 0) : _ → _)
          {a : ℕ × Bool | a.1 ∈ (S).edges} (D t').property (D e).property hrot he
        exact hbt.trans ((D).injective (Subtype.ext huniq))
  · apply lPlusGluedCorrectedRotation4_rotation_iff_of_ne_terminal
      hτ hp P hqMode Tpath hfin hleft hk hn d e
    simpa only [hes, List.length_cons, List.length_nil, Nat.add_zero,
      Nat.sub_self, List.getElem_cons_zero] using (fun he => hv (he.trans hvertex))




theorem boundaryGluing_nonneg_left_markedIso_lPlusCodeBlockSide4_of_left_down
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    Nonempty (GeometricSideMarkedIso S
      (lPlusCodeBlockSide4 hτ hp P hqMode Tpath hfin hleft hk)) := by
  let B := lPlusCodeBlockSide4 hτ hp P hqMode Tpath hfin hleft hk
  let E := lPlusActualCodeBlockCellEquiv4 hτ hp P hqMode Tpath hfin hleft hk
  refine ⟨{ equiv := E, relation_iff := ?_ }⟩
  intro r u v
  by_cases hr : r = .rotation
  · subst r
    cases u with
    | inl u => cases v <;> rfl
    | inr d =>
      cases v with
      | inl v => rfl
      | inr e =>
        change (S).rotation d.val e.val ↔ B.rotation d.val e.val
        obtain ⟨a, rfl⟩ := (D).surjective d
        obtain ⟨b, rfl⟩ := (D).surjective e
        exact (lPlusGluedCorrectedRotation4_left_down_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk hk₁ hc₀ hc₁ a b).symm.trans
            (lPlusCodeBlockSide4_rotation_glued_iff
              hτ hp P hqMode Tpath hfin hleft hk a b).symm
  · exact lPlusActualCodeBlockCellEquiv4_relation_iff_of_ne_rotation
      hτ hp P hqMode Tpath hfin hleft hk r hr u v

/-- Helper toward Lemma 5.5: every finite dart off the outer word has
its immediate finite successor in the ambient rotation. This concrete
triangle class does not require completion of the vertex star. -/
theorem lPlus_nonouter_ambient_rotation (u : ℕ → Fin 3)
    (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
      ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage u n).nextEdge)
    (hd : d ∉ stageOuterWord u n) :
    kmswInfRot u hf (d.1.val, d.2) =
      ((stageRot u n d).1.val, (stageRot u n d).2) := by
  obtain ho | ⟨j, ⟨hj, hdj⟩, _⟩ := stage_dart_partition u n d
  · exact (hd ho).elim
  have hs := stageTriangle_isFace u j n hj
  have hi := kmswInfFaceSucc_stageTriangle_cycle u hf j
  have hlocal (q r : StageDart (kmswStage u n).nextEdge)
      (hfr : (kmswMap u n).faceSucc r = q)
      (hir : kmswInfFaceSucc u hf (r.1.val, r.2) = (q.1.val, q.2)) :
      kmswInfRot u hf (q.1.val, q.2) =
        ((stageRot u n q).1.val, (stageRot u n q).2) := by
    change (stageRot u n).symm (edgeFlip _ r) = q at hfr
    have hsr := ((stageRot u n).symm_apply_eq.mp hfr).symm
    change (kmswInfRot u hf).symm (r.1.val, !r.2) = (q.1.val, q.2) at hir
    have hir' := ((kmswInfRot u hf).symm_apply_eq.mp hir).symm
    exact hir'.trans (congrArg (fun a : StageDart (kmswStage u n).nextEdge =>
      (a.1.val, a.2)) hsr).symm
  have hdeq (q : StageDart (kmswStage u n).nextEdge)
      (he : (d.1.val, d.2) = (q.1.val, q.2)) : d = q :=
    Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) he))
      (congrArg (fun z : ℕ × Bool => z.2) he)
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hdj
  rcases hdj with hdj | hdj | hdj
  · have he : d = stageTriangleDart₁ u n j hj := hdeq _ hdj
    rw [he]
    exact hlocal _ (stageTriangleDart₃ u n j hj) hs.2.2.1 hi.2.2.1
  · have he : d = stageTriangleDart₂ u n j hj := hdeq _ hdj
    rw [he]
    exact hlocal _ (stageTriangleDart₁ u n j hj) hs.1 hi.1
  · have he : d = stageTriangleDart₃ u n j hj := hdeq _ hdj
    rw [he]
    exact hlocal _ (stageTriangleDart₂ u n j hj) hs.2.1 hi.2.1

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a nonouter prefix dart has its actual side
first return in one ambient step, equal to its finite-prefix successor.
This applies in particular to nonouter darts of the terminal prefix star. -/
theorem lPlus_nonouter_prefix_side_rotation (hkpos : 0 < k)
    (p : LPlusPrefixDart W h k)
    (hpout : lPlusPrefixDartStage hkpos p ∉
      stageOuterWord w (boundaryHitTime w h k - 1)) :
    (S).rotation p.val
      (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
        (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
        (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk p).val := by
  rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos]
  refine ⟨1, by omega, ?_, ?_⟩
  · exact lPlus_nonouter_ambient_rotation w (H.1 0)
      (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos p) hpout
  · intro j hj hj1
    omega

/-- Helper toward Lemma 5.5: at an arbitrary terminal star, rotation 4
transports a nonouter prefix dart whose finite-prefix successor is also
away from the attachment ports. These are explicit finite triangle classes;
the hypothesis does not assume any ambient return or transport. -/
theorem lPlusGluedCorrectedRotation4_terminal_nonouter_prefix_rotation_iff
    (hn : 0 < (es).length) (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : ∀ j : Fin (es).length, ∀ b : Bool, p.val ≠ (es[j.val], b))
    (hpout : lPlusPrefixDartStage
      (lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk hn) p ∉
        stageOuterWord w (boundaryHitTime w h k - 1))
    (hnext : ∀ j : Fin (es).length, ∀ b : Bool,
      (D (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk (IP p))).val ≠
        (es[j.val], b)) (e : Q) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk (IP p) = e ↔
      (S).rotation (D (IP p)).val (D e).val := by
  let d := IP p
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let y := PE d
  let R := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(es).length - 1, by omega⟩, false)
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
    (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
    (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  have hy : y = IP (PR p) := PR.extendDomain_apply_image _ p
  have hrot : (S).rotation (D d).val (D y).val := by
    rw [hy]
    exact lPlus_nonouter_prefix_side_rotation hτ hp P hqMode Tpath hfin hleft hk
      (lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk hn) p hpout
  have hnotT : y ∉ Set.range IT := by
    rw [hy]
    exact lPlus_nonport_prefix_not_primed hτ hqMode hfin hk (PR p)
      (fun j b he => hnext j b (by change (D y).val = _; rw [hy]; exact he))
  have hnotUL : y ∉ Set.range (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨j, hj⟩
    exact hnext j.1 j.2 (congrArg (fun a => (D a).val) hj.symm)
  have hyv : kmswLimitDartVertex w (D y).val =
      kmswLimitDartVertex w (es[(es).length - 1], false) :=
    (lPlusPrefixExtendedRotation_vertex hτ hp P hqMode Tpath hfin hleft hk d).trans hv
  have hnotH := lPlus_terminal_not_hatted hτ hp P hqMode Tpath hfin hleft hk hn y hyv
  have hnotB : y ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨j, hj⟩
    exact hnotH ⟨_, hj⟩
  have hR : R d = y := by
    change lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode (lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusUpperLeftCornerRotation hτ hqMode hfin hk y))) = y
    rw [show lPlusUpperLeftCornerRotation hτ hqMode hfin hk y = y from
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotUL,
      show lPlusPrimedExtendedRotation hτ hqMode hfin y = y from
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotT,
      show lPlusBetaCornerRotation hτ hqMode y = y from
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB]
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
  have hdt : d ≠ t := by
    intro he
    exact hport ⟨(es).length - 1, by omega⟩ false
      (congrArg (fun a => (D a).val) he)
  have hret : R d = lPlusGluedCodeReturn (H := H) hτ hqMode d :=
    hR.trans ((lPlusGluedCodeReturn_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk d y).mpr hrot).symm
  have hC : lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = y := by
    rw [lPlusGluedCorrectedRotation2_eq_of_ne
      hτ hp P hqMode Tpath hfin hleft hk hn d hdt, hR]
    intro he
    exact hdt (lPlusGluedCodeReturn_injective (H := H) hτ hqMode
      (hret.symm.trans he))
  have h4 : lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = y := by
    rw [lPlusGluedCorrectedRotation4_apply hτ hp P hqMode Tpath hfin hleft hk hn, hC]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he
      exact hnext ⟨(es).length - 1, by omega⟩ false
        (congrArg (fun a => (D a).val) he)
    · exact fun he => hdt (PE.injective he)
  rw [h4]
  constructor
  · intro he
    exact he ▸ hrot
  · intro he
    exact (D).injective (Subtype.ext (firstReturn_endpoint_unique
      (kmswInfRot w (H.1 0) : _ → _) {a : ℕ × Bool | a.1 ∈ (S).edges}
      (D y).property (D e).property hrot he))

end DirectedDistances.PaperProofs.Section5



























































































































