/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCorrectedDecoder3

/-! Terminal-star analysis for corrected rotation 4. This is a formalization-internal
helper; it makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: along an allocated finite boundary chain,
every later west endpoint has strictly larger rank than the initial one. -/
theorem lPlus_chain_initial_rank (u : ℕ → Fin 3) (n a : ℕ) (as : List ℕ)
    (hc : WestEastChain (kmswStage u n) (a :: as))
    (hb : ∀ e ∈ a :: as, e < (kmswStage u n).nextEdge) :
    ∀ e ∈ a :: as,
      (e = a ∨ kmswStageRank u n ((kmswStage u n).west a) <
        kmswStageRank u n ((kmswStage u n).west e)) ∧
      kmswStageRank u n ((kmswStage u n).west a) <
        kmswStageRank u n ((kmswStage u n).east e) := by
  induction as generalizing a with
  | nil =>
    intro e he
    have he' : e = a := List.mem_singleton.mp he
    subst e
    exact ⟨Or.inl rfl, kmswStageRank_strict u n a (hb a (by simp))⟩
  | cons b bs ih =>
    intro e he
    have ha := kmswStageRank_strict u n a (hb a (by simp))
    have hab : (kmswStage u n).east a = (kmswStage u n).west b :=
      hc.rel_head? (by simp)
    rw [hab] at ha
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact ⟨Or.inl rfl, kmswStageRank_strict u n a (hb a (by simp))⟩
    · obtain ⟨hwest, heast⟩ := ih b hc.tail
        (fun f hf => hb f (List.mem_cons_of_mem a hf)) e he
      refine ⟨Or.inr ?_, ha.trans heast⟩
      rcases hwest with rfl | hwest
      · exact ha
      · exact ha.trans hwest

/-- Helper toward Lemma 5.5: at the west endpoint of the first upper
boundary edge, the finite outer word contains exactly that west dart.
Missing lower-boundary edges are included in this classification. -/
theorem lPlus_stage_outer_initial_dart_eq (u : ℕ → Fin 3) (n a : ℕ)
    (as : List ℕ) (ha : (kmswStage u n).UL = a :: as)
    (x : StageDart (kmswStage u n).nextEdge)
    (hx : x ∈ stageOuterWord u n)
    (hv : stageEndpoint (kmswStage u n) x = (kmswStage u n).west a) :
    (x.1.val, x.2) = (a, false) := by
  let s := kmswStage u n
  change s.UL = a :: as at ha
  have hI := kmswStage_boundary_chain_invariant u n
  have hB := (kmswStage_boundary_ids_lt_nextEdge u n).2
  have hU : WestEastChain s (a :: (as ++ s.UR)) := by
    have hi : WestEastChain s (s.UL ++ s.UR) := hI.1
    simpa only [ha, List.cons_append] using hi
  have hUb : ∀ e ∈ a :: (as ++ s.UR), e < s.nextEdge := by
    intro e he
    apply hB e
    have he' : e ∈ s.UL ++ s.UR := by simpa only [ha, List.cons_append] using he
    simp only [List.mem_append] at he' ⊢
    tauto
  have hLne : s.LL ++ s.LR ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ hI.2.2.2.2.1
  obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hLne
  have hL : WestEastChain s (b :: bs) := hbs ▸ hI.2.1
  have hLb : ∀ e ∈ b :: bs, e < s.nextEdge := by
    intro e he
    apply hB e
    have he' : e ∈ s.LL ++ s.LR := by rw [hbs]; exact he
    simp only [List.mem_append] at he' ⊢
    tauto
  have hstart : s.west a = s.west b := by
    have hs := hI.2.2.1
    change boundaryStart s (s.UL ++ s.UR) = boundaryStart s (s.LL ++ s.LR) at hs
    rw [ha, hbs] at hs
    exact Option.some.inj hs
  have ho := (stageOuterWord_mem_iff u n x).mp hx
  rcases ho with ⟨hb, he⟩ | ⟨hb, he⟩
  · have he' : x.1.val ∈ a :: (as ++ s.UR) := by
      have hm : x.1.val ∈ s.UL ++ s.UR := List.mem_append.mpr he
      simpa only [ha, List.cons_append] using hm
    have hwest : s.west x.1.val = s.west a := by
      simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hv
    obtain ⟨heq | hlt, _⟩ := lPlus_chain_initial_rank u n a _ hU hUb _ he'
    · exact Prod.ext heq hb
    · rw [hwest] at hlt
      exact (lt_irrefl _ hlt).elim
  · have he' : x.1.val ∈ b :: bs := by
      rw [← hbs]
      exact List.mem_append.mpr he.symm
    have heast : s.east x.1.val = s.west a := by
      simpa only [stageEndpoint, hb, ↓reduceIte] using hv
    have hlt := (lPlus_chain_initial_rank u n b bs hL hLb _ he').2
    rw [heast, hstart] at hlt
    exact (lt_irrefl _ hlt).elim

/-- Helper toward Lemma 5.5: among both ends of all upper-chain edges,
only the first west dart is based at the initial upper-chain vertex. -/
theorem lPlus_stage_upper_initial_dart_eq (u : ℕ → Fin 3) (n a : ℕ)
    (as : List ℕ) (ha : (kmswStage u n).UL = a :: as)
    (x : StageDart (kmswStage u n).nextEdge)
    (hx : x.1.val ∈ (kmswStage u n).UL)
    (hv : stageEndpoint (kmswStage u n) x = (kmswStage u n).west a) :
    (x.1.val, x.2) = (a, false) := by
  have hc : WestEastChain (kmswStage u n) (a :: as) := by
    rw [← ha]
    exact (kmswStage_boundary_chain_invariant u n).1.left_of_append
  have hb : ∀ e ∈ a :: as, e < (kmswStage u n).nextEdge := by
    intro e he
    exact stageRotation_UL_bound u n e (by rw [ha]; exact he)
  have hr := lPlus_chain_initial_rank u n a as hc hb x.1.val (by rw [← ha]; exact hx)
  cases hs : x.2 with
  | false =>
    have he : (kmswStage u n).west x.1.val = (kmswStage u n).west a := by
      simpa only [stageEndpoint, hs, Bool.false_eq_true, ↓reduceIte] using hv
    rcases hr.1 with heq | hlt
    · exact Prod.ext heq rfl
    · rw [he] at hlt
      exact (lt_irrefl _ hlt).elim
  | true =>
    have he : (kmswStage u n).east x.1.val = (kmswStage u n).west a := by
      simpa only [stageEndpoint, hs, ↓reduceIte] using hv
    have hlt := hr.2
    rw [he] at hlt
    exact (lt_irrefl _ hlt).elim

/-- Helper toward Lemma 5.5: the finite prefix star from the successor
of its first upper-left west port back to that port is an uninterrupted
arc of the actual ambient rotation. The arc may be empty. -/
theorem lPlus_stage_initial_prefix_arc (u : ℕ → Fin 3)
    (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
      ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite)
    (n a : ℕ) (as : List ℕ) (ha : (kmswStage u n).UL = a :: as)
    (ha' : a < (kmswStage u n).nextEdge) :
    let t : StageDart (kmswStage u n).nextEdge := (⟨a, ha'⟩, false)
    let R := stageRot u n
    let b := R t
    let V := fun x : StageDart (kmswStage u n).nextEdge => (x.1.val, x.2)
    ∃ m : ℕ,
      (kmswInfRot u hf : _ → _)^[m] (V b) = (a, false) ∧
      (∀ j ≤ m, (kmswInfRot u hf : _ → _)^[j] (V b) = V ((R ^ j) b)) ∧
      ∀ j < m, V ((R ^ j) b) ≠ (a, false) := by
  dsimp only
  let t : StageDart (kmswStage u n).nextEdge := (⟨a, ha'⟩, false)
  let R := stageRot u n
  let b := R t
  let V := fun x : StageDart (kmswStage u n).nextEdge => (x.1.val, x.2)
  have hV : Function.Injective V := by
    intro x y he
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) he))
      (congrArg (fun z : ℕ × Bool => z.2) he)
  have hstep (x : StageDart (kmswStage u n).nextEdge) :
      stageEndpoint (kmswStage u n) (R x) = stageEndpoint (kmswStage u n) x :=
    ((stageRot_sameCycle_iff_endpoint_eq u n x (R x)).mp ⟨1, rfl⟩).symm
  have hvertex (j : ℕ) : stageEndpoint (kmswStage u n) ((R ^ j) b) =
      (kmswStage u n).west a := by
    induction j with
    | zero => exact hstep t
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hstep _).trans ih
  have hex : ∃ m : ℕ, (R ^ m) b = t :=
    ((stageRot_sameCycle_iff_endpoint_eq u n b t).mpr (hvertex 0)).exists_nat_pow_eq
  let m := Nat.find hex
  have hm : (R ^ m) b = t := Nat.find_spec hex
  have hne (j : ℕ) (hj : j < m) : V ((R ^ j) b) ≠ (a, false) := by
    intro he
    exact Nat.find_min hex hj (hV he)
  have hiter (j : ℕ) (hj : j ≤ m) :
      (kmswInfRot u hf : _ → _)^[j] (V b) = V ((R ^ j) b) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have ho : (R ^ j) b ∉ stageOuterWord u n := by
        intro ho
        exact hne j (by omega)
          (lPlus_stage_outer_initial_dart_eq u n a as ha _ ho (hvertex j))
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact (lPlus_nonouter_ambient_rotation u hf n _ ho).trans
        (by rw [pow_succ', Equiv.Perm.mul_apply])
  exact ⟨m, (hiter m le_rfl).trans (congrArg V hm), hiter, hne⟩

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
local notation "es" => List.reverse (List.dropLast
  (State.UL (kmswStage w (boundaryHitTime w h k))))
local notation "IP" => lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IT" => lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IH" => lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "PR" => lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
  (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
  (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
local notation "PE" => lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
local notation "TE" => lPlusPrimedExtendedRotation hτ hqMode hfin
local notation "R" => lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk

include hk in
/-- Helper toward Lemma 5.5: the terminal attachment edge is exactly
the first edge of the preceding finite upper-left boundary. -/
theorem lPlus_terminal_previous_upperLeft_cons (hn : 0 < (es).length) :
    ∃ as, (kmswStage w (boundaryHitTime w h k - 1)).UL =
      es[(es).length - 1] :: as := by
  have he := lPlus_attachment_upperLeft_eq_previous
    (W := W) (h := h) (lPlus_upperLeft_nonempty_pos hk hn)
  have hn' : (kmswStage w (boundaryHitTime w h k - 1)).UL ≠ [] := by
    intro hz
    rw [he, hz] at hn
    simp at hn
  obtain ⟨a, as, ha⟩ := List.exists_cons_of_ne_nil hn'
  refine ⟨as, ?_⟩
  have ht : es[(es).length - 1] = a := by
    have ht' : es[(es).length - 1]? = some a := by
      rw [he, ha, List.getElem?_reverse (by simp)]
      simp
    exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans ht')
  rw [ht]
  exact ha

include hk in
/-- Helper toward Lemma 5.5: every nonterminal-port prefix dart in the
terminal star belongs to an old triangle, rather than the finite outer word. -/
theorem lPlus_terminal_prefix_nonport_not_outer (hn : 0 < (es).length)
    (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hp : p.val ≠ (es[(es).length - 1], false)) :
    lPlusPrefixDartStage (lPlus_upperLeft_nonempty_pos hk hn) p ∉
      stageOuterWord w (boundaryHitTime w h k - 1) := by
  intro hout
  obtain ⟨as, ha⟩ := lPlus_terminal_previous_upperLeft_cons hk hn
  let a : LPlusPrefixDart W h k := ⟨(es[(es).length - 1], false), by
    rw [lPlusPrefixMinusEdges_eq_previousStage (lPlus_upperLeft_nonempty_pos hk hn)]
    exact stageRotation_UL_bound w _ _ (by rw [ha]; simp)⟩
  have hvertex := (lPlusPrefixDartStage_endpoint
    (lPlus_upperLeft_nonempty_pos hk hn) p).trans
      (hv.trans (lPlusPrefixDartStage_endpoint
        (lPlus_upperLeft_nonempty_pos hk hn) a).symm)
  exact hp (lPlus_stage_outer_initial_dart_eq w _ _ as ha
    (lPlusPrefixDartStage (lPlus_upperLeft_nonempty_pos hk hn) p) hout hvertex)

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every terminal prefix dart except the
attachment port has its actual side return in one ambient step. -/
theorem lPlus_terminal_prefix_nonport_side_rotation (hn : 0 < (es).length)
    (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : p.val ≠ (es[(es).length - 1], false)) :
    (S).rotation p.val
      (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
        (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
        (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk p).val := by
  exact lPlus_nonouter_prefix_side_rotation hτ hp P hqMode Tpath hfin hleft hk
    (lPlus_upperLeft_nonempty_pos hk hn) p
    (lPlus_terminal_prefix_nonport_not_outer hk hn p hv hport)

include hk in
/-- Helper toward Lemma 5.5: every attachment dart in the terminal
star equals its unique terminal west port, with its endpoint bit retained. -/
theorem lPlus_terminal_attachment_dart_eq (hn : 0 < (es).length)
    (i : Fin (es).length) (b : Bool)
    (hv : kmswLimitDartVertex w (es[i.val], b) =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    (es[i.val], b) = (es[(es).length - 1], false) := by
  have hkpos := lPlus_upperLeft_nonempty_pos hk hn
  obtain ⟨as, ha⟩ := lPlus_terminal_previous_upperLeft_cons hk hn
  have hm : es[i.val] ∈ (kmswStage w (boundaryHitTime w h k - 1)).UL := by
    have hi := List.getElem_mem i.isLt
    have he := lPlus_attachment_upperLeft_eq_previous (W := W) (h := h) hkpos
    exact List.mem_reverse.mp
      (Eq.mp (congrArg (fun l : List ℕ => es[i.val] ∈ l) he) hi)
  have hb := stageRotation_UL_bound w _ _ hm
  let p : LPlusPrefixDart W h k := ⟨(es[i.val], b), by
    rw [lPlusPrefixMinusEdges_eq_previousStage hkpos]
    exact hb⟩
  let t : LPlusPrefixDart W h k := ⟨(es[(es).length - 1], false), by
    rw [lPlusPrefixMinusEdges_eq_previousStage hkpos]
    exact stageRotation_UL_bound w _ _ (by rw [ha]; simp)⟩
  exact lPlus_stage_upper_initial_dart_eq w _ _ as ha
    (lPlusPrefixDartStage hkpos p) hm
    ((lPlusPrefixDartStage_endpoint hkpos p).trans
      (hv.trans (lPlusPrefixDartStage_endpoint hkpos t).symm))

include hfin hk in
/-- Helper toward Lemma 5.5: the prefix and primed terminal stars
intersect in exactly the terminal west port. -/
theorem lPlus_terminal_prefix_primed_intersection (hn : 0 < (es).length)
    (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hpT : p.val ∈ Set.range (lMinusPrimedDartImage hτ)) :
    p.val = (es[(es).length - 1], false) := by
  obtain ⟨q, hq⟩ := hpT
  have hm : p.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
      boundaryGluingPrimedEdges W h k hτ :=
    ⟨p.property, ⟨q.1, congrArg Prod.fst hq⟩⟩
  rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin hk] at hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem (List.mem_reverse.mpr hm)
  have hp' : p.val = (es[i], p.val.2) := Prod.ext he.symm rfl
  exact hp'.trans (lPlus_terminal_attachment_dart_eq hk hn ⟨i, hi⟩ p.val.2
    ((congrArg (kmswLimitDartVertex w) hp').symm.trans hv))

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every non-port dart of the terminal prefix
star has its finite-prefix successor in one ambient step. -/
theorem lPlus_terminal_prefix_nonport_ambient_rotation (hn : 0 < (es).length)
    (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : p.val ≠ (es[(es).length - 1], false)) :
    kmswInfRot w (H.1 0) p.val =
      (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
        (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
        (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk p).val := by
  rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk
    (lPlus_upperLeft_nonempty_pos hk hn)]
  exact lPlus_nonouter_ambient_rotation w (H.1 0) _ _
    (lPlus_terminal_prefix_nonport_not_outer hk hn p hv hport)

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at the terminal vertex the actual side
contains precisely prefix darts and primed darts. -/
theorem lPlus_terminal_side_mem_iff (hn : 0 < (es).length)
    (x : ℕ × Bool)
    (hv : kmswLimitDartVertex w x =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    x.1 ∈ (S).edges ↔ x.1 ∈ boundaryGluingPrefixMinusEdges W h k ∨
      x ∈ Set.range (lMinusPrimedDartImage hτ) := by
  change x ∈ {d : ℕ × Bool | d.1 ∈ (S).edges} ↔ _
  rw [← lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
  constructor
  · rintro ⟨p | (p | a), he⟩
    · exact Or.inl (he ▸ p.property)
    · exact Or.inr ⟨p, he⟩
    · exact (lPlus_upperLeft_west_not_hatted hτ ((es).length - 1) _
        (List.getElem?_eq_getElem (by omega)) a.val
          (hv.symm.trans (congrArg (kmswLimitDartVertex w) he.symm))).elim
  · rintro (hpref | ⟨p, rfl⟩)
    · exact ⟨.inl ⟨x, hpref⟩, rfl⟩
    · exact ⟨.inr (.inl p), rfl⟩

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the prefix rotation preserves the endpoint
of each explicit prefix dart. -/
theorem lPlus_prefix_rotation_vertex (p : LPlusPrefixDart W h k) :
    kmswLimitDartVertex w (PR p).val = kmswLimitDartVertex w p.val := by
  have he : lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk (IP p) =
      IP (PR p) := (PR).extendDomain_apply_image _ p
  have hv := lPlusPrefixExtendedRotation_vertex hτ hp P hqMode Tpath hfin hleft hk (IP p)
  rw [he] at hv
  exact hv

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: except at the finite successor of the
terminal port, every terminal prefix dart has its ambient predecessor in
the same prefix star. This is an explicit dart-class dichotomy. -/
theorem lPlus_terminal_prefix_predecessor (hn : 0 < (es).length)
    (t p : LPlusPrefixDart W h k)
    (ht : t.val = (es[(es).length - 1], false))
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    p = PR t ∨ kmswInfRot w (H.1 0) ((PR).symm p).val = p.val := by
  by_cases he : ((PR).symm p).val = (es[(es).length - 1], false)
  · have he' : (PR).symm p = t := Subtype.ext (he.trans ht.symm)
    exact Or.inl ((PR).symm_apply_eq.mp he')
  · right
    have hv' : kmswLimitDartVertex w ((PR).symm p).val =
        kmswLimitDartVertex w (es[(es).length - 1], false) :=
      (lPlus_prefix_rotation_vertex hτ hp P hqMode Tpath hfin hleft hk
        ((PR).symm p)).symm.trans (by simpa only [Equiv.apply_symm_apply] using hv)
    simpa only [Equiv.apply_symm_apply] using
      lPlus_terminal_prefix_nonport_ambient_rotation hτ hp P hqMode Tpath hfin hleft hk
        hn ((PR).symm p) hv' he

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the first positive ambient entry from a
terminal primed non-port into the prefix star is its finite successor port.
All minimality is proved from the explicit dart classes. -/
theorem lPlus_terminal_first_prefix_entry (hn : 0 < (es).length)
    (t : LPlusPrefixDart W h k)
    (ht : t.val = (es[(es).length - 1], false))
    (p : ℕ × Bool)
    (hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : lMinusPrimedDartImage hτ p ≠ (es[(es).length - 1], false)) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (lMinusPrimedDartImage hτ p) =
        (PR t).val ∧
      ∀ j, 0 < j → j < n →
        ((kmswInfRot w (H.1 0) : _ → _)^[j]
          (lMinusPrimedDartImage hτ p)).1 ∉ boundaryGluingPrefixMinusEdges W h k := by
  let σ := kmswInfRot w (H.1 0)
  let x := lMinusPrimedDartImage hτ p
  have hex : ∃ n : ℕ, 0 < n ∧
      ((σ : _ → _)^[n] x).1 ∈ boundaryGluingPrefixMinusEdges W h k := by
    obtain ⟨m, hm⟩ := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) x t.val).mpr
      (hv.trans (congrArg (kmswLimitDartVertex w) ht).symm)
    have hm' : (σ : _ → _)^[m] x = t.val := by
      simpa only [σ, Equiv.Perm.coe_pow] using hm
    have hmpos : 0 < m := by
      by_contra hh
      have hm0 : m = 0 := by omega
      have hx : x = t.val := by
        simpa only [hm0, Function.iterate_zero, id_eq] using hm'
      exact hport (hx.trans ht)
    exact ⟨m, hmpos, hm'.symm ▸ t.property⟩
  let n := Nat.find hex
  obtain ⟨hnpos, hmem⟩ := Nat.find_spec hex
  have hgap (j : ℕ) (hj : 0 < j) (hjn : j < n) :
      ((σ : _ → _)^[j] x).1 ∉ boundaryGluingPrefixMinusEdges W h k :=
    fun hjmem => Nat.find_min hex hjn ⟨hj, hjmem⟩
  refine ⟨n, hnpos, ?_, hgap⟩
  let q : LPlusPrefixDart W h k := ⟨(σ : _ → _)^[n] x, hmem⟩
  have hqv : kmswLimitDartVertex w q.val =
      kmswLimitDartVertex w (es[(es).length - 1], false) :=
    ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) x q.val).mp
      ⟨n, by simp only [q, σ, Equiv.Perm.coe_pow]⟩).symm.trans hv
  rcases lPlus_terminal_prefix_predecessor hτ hp P hqMode Tpath hfin hleft hk
      hn t q ht hqv with he | he
  · exact congrArg Subtype.val he
  · have hprev : (σ : _ → _)^[n - 1] x = ((PR).symm q).val := by
      apply σ.injective
      calc
        σ ((σ : _ → _)^[n - 1] x) = (σ : _ → _)^[n - 1 + 1] x :=
          (Function.iterate_succ_apply' ..).symm
        _ = q.val := by rw [Nat.sub_add_cancel hnpos]
        _ = σ ((PR).symm q).val := he.symm
    by_cases hn1 : n = 1
    · have hx : x = ((PR).symm q).val := by simpa only [hn1, Nat.sub_self,
          Function.iterate_zero, id_eq] using hprev
      have hrv : kmswLimitDartVertex w ((PR).symm q).val =
          kmswLimitDartVertex w (es[(es).length - 1], false) := hx ▸ hv
      exact (hport (hx.trans (lPlus_terminal_prefix_primed_intersection hτ hfin hk hn
        ((PR).symm q) hrv ⟨p, hx⟩))).elim
    · exact (hgap (n - 1) (by omega) (by omega)
        (hprev.symm ▸ ((PR).symm q).property)).elim

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: in the general terminal star, a primed
non-port returns to the finite successor of the terminal port exactly when
its own primed return is that terminal port. Every other primed return is
unchanged. The prefix and primed arcs cannot interleave. -/
theorem lPlus_terminal_primed_side_rotation (hn : 0 < (es).length)
    (t : LPlusPrefixDart W h k)
    (ht : t.val = (es[(es).length - 1], false))
    (p : ℕ × Bool)
    (hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : lMinusPrimedDartImage hτ p ≠ (es[(es).length - 1], false)) :
    let y := lMinusPrimedDartImage hτ
      (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p)
    (S).rotation (lMinusPrimedDartImage hτ p)
      (if y = t.val then (PR t).val else y) := by
  let σ := kmswInfRot w (H.1 0)
  let x := lMinusPrimedDartImage hτ p
  let y := lMinusPrimedDartImage hτ
    (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) p)
  change (S).rotation x (if y = t.val then (PR t).val else y)
  obtain ⟨a, ha, haend, hagap⟩ := lPlus_terminal_first_prefix_entry
    hτ hp P hqMode Tpath hfin hleft hk hn t ht p hv hport
  obtain ⟨b, hb, hbend, hbgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  change (σ : _ → _)^[b] x = y at hbend
  have hvertex (j : ℕ) : kmswLimitDartVertex w ((σ : _ → _)^[j] x) =
      kmswLimitDartVertex w (es[(es).length - 1], false) :=
    ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) x _).mp
      ⟨j, by simp only [σ, Equiv.Perm.coe_pow]⟩).symm.trans hv
  have htprime : t.val ∈ Set.range (lMinusPrimedDartImage hτ) := by
    obtain ⟨q, hq, _⟩ := lPlusUpperLeftGluedDart_primed_representative
      hτ hqMode hfin hk ⟨(es).length - 1, by omega⟩ false
    exact ⟨q, hq.trans ht.symm⟩
  have horder : a ≤ b ↔ y = t.val := by
    constructor
    · intro hab
      have hforward (j : ℕ) (haj : a ≤ j) (hjb : j ≤ b) :
          ((σ : _ → _)^[j] x).1 ∈ boundaryGluingPrefixMinusEdges W h k := by
        induction j with
        | zero => omega
        | succ j ih =>
          by_cases hej : a = j + 1
          · rw [← hej, haend]
            exact (PR t).property
          · have hjmem := ih (by omega) (by omega)
            let q : LPlusPrefixDart W h k := ⟨(σ : _ → _)^[j] x, hjmem⟩
            have hqport : q.val ≠ (es[(es).length - 1], false) := by
              intro he
              have hqprime : q.val ∈ Set.range (lMinusPrimedDartImage hτ) := by
                rw [he, ← ht]
                exact htprime
              exact hbgap j (by omega) (by omega) hqprime
            have he := lPlus_terminal_prefix_nonport_ambient_rotation
              hτ hp P hqMode Tpath hfin hleft hk hn q (hvertex j) hqport
            have he' : (σ : _ → _)^[j + 1] x = (PR q).val :=
              (Function.iterate_succ_apply' ..).trans he
            exact he'.symm ▸ (PR q).property
      let q : LPlusPrefixDart W h k := ⟨y, hbend ▸ hforward b hab le_rfl⟩
      exact (lPlus_terminal_prefix_primed_intersection hτ hfin hk hn q
        ((congrArg (kmswLimitDartVertex w) hbend).symm.trans (hvertex b))
        ⟨_, rfl⟩).trans ht.symm
    · intro hy
      by_contra hh
      have hmem : ((σ : _ → _)^[b] x).1 ∈ boundaryGluingPrefixMinusEdges W h k :=
        (hbend.trans hy).symm ▸ t.property
      exact hagap b hb (by omega) hmem
  have hgap (j : ℕ) (hj : 0 < j) (hja : j < a) (hjb : j < b) :
      ((σ : _ → _)^[j] x).1 ∉ (S).edges := by
    intro hjmem
    rcases (lPlus_terminal_side_mem_iff hτ hp P hqMode Tpath hfin hleft hk
      hn _ (hvertex j)).mp hjmem with hpre | hprime
    · exact hagap j hj hja hpre
    · exact hbgap j hj hjb hprime
  by_cases hy : y = t.val
  · rw [ite_eq_left hy]
    exact ⟨a, ha, haend, fun j hj hja => hgap j hj hja
      (lt_of_lt_of_le hja (horder.mpr hy))⟩
  · rw [ite_eq_right hy]
    have hba : b < a := by
      have hh : ¬ a ≤ b := fun hab => hy (horder.mp hab)
      omega
    exact ⟨b, hb, hbend, fun j hj hjb => hgap j hj (hjb.trans hba) hjb⟩

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the primed extended rotation preserves
the ambient vertex, including darts outside its block. -/
theorem lPlus_primed_extended_rotation_vertex (d : Q) :
    kmswLimitDartVertex w (D (TE d)).val = kmswLimitDartVertex w (D d).val := by
  by_cases hd : d ∈ Set.range IT
  · obtain ⟨p, rfl⟩ := hd
    have he : TE (IT p) = IT (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p) :=
      (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin)).extendDomain_apply_image _ p
    rw [he]
    change kmswLimitDartVertex w (lMinusPrimedDartImage hτ
      (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p)) =
      kmswLimitDartVertex w (lMinusPrimedDartImage hτ p)
    obtain ⟨n, _, hn, _⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩).symm
  · rw [show TE d = d from Equiv.Perm.extendDomain_apply_not_subtype _ _ hd]

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the upper-left corner permutation fixes
the complete terminal star, whose only attachment dart is the last west port. -/
theorem lPlus_terminal_upperLeft_corner_eq (hn : 0 < (es).length) (d : Q)
    (hv : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    lPlusUpperLeftCornerRotation hτ hqMode hfin hk d = d := by
  let UL := lPlusUpperLeftGluedDart hτ hqMode hfin hk
  let i : Fin (es).length := ⟨(es).length - 1, by omega⟩
  by_cases hd : d ∈ Set.range UL
  · obtain ⟨j, hj⟩ := hd
    have he : (es[j.1.val], j.2) = (es[(es).length - 1], false) :=
      lPlus_terminal_attachment_dart_eq hk hn j.1 j.2
        ((congrArg (fun q => kmswLimitDartVertex w (D q).val) hj).trans hv)
    have hdt : d = UL (i, false) := (D).injective (Subtype.ext
      ((congrArg (fun q => (D q).val) hj).symm.trans he))
    rw [hdt]
    have hcorner : lPlusUpperLeftCornerPerm (es).length (i, false) = (i, false) := by
      change lPlusUpperLeftCorner (es).length (i, false) = _
      simp only [lPlusUpperLeftCorner, Bool.false_eq_true, ↓reduceIte,
        dite_eq_right (show ¬ i.val + 1 < (es).length by dsimp [i]; omega)]
    exact ((lPlusUpperLeftCornerPerm (es).length).extendDomain_apply_image
      (Equiv.ofInjective _ (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))
        (i, false)).trans (congrArg UL hcorner)
  · exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hd

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: on the terminal star the original block
permutation is precisely primed rotation after prefix rotation. -/
theorem lPlus_terminal_block_rotation (hn : 0 < (es).length) (d : Q)
    (hv : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    R d = TE (PE d) := by
  have hpev := (lPlusPrefixExtendedRotation_vertex hτ hp P hqMode Tpath hfin hleft hk d).trans hv
  have htev := (lPlus_primed_extended_rotation_vertex hτ hp P hqMode Tpath hfin hleft hk
    (PE d)).trans hpev
  have hnotH := lPlus_terminal_not_hatted hτ hp P hqMode Tpath hfin hleft hk hn
    (TE (PE d)) htev
  have hnotB : TE (PE d) ∉ Set.range (lPlusBetaGluedDart hτ hqMode) := by
    rintro ⟨j, hj⟩
    exact hnotH ⟨_, hj⟩
  change lPlusHattedExtendedRotation hτ hqMode
    (lPlusBetaCornerRotation hτ hqMode
      (TE (lPlusUpperLeftCornerRotation hτ hqMode hfin hk (PE d)))) = _
  rw [lPlus_terminal_upperLeft_corner_eq hτ hp P hqMode Tpath hfin hleft hk hn (PE d) hpev,
    show lPlusBetaCornerRotation hτ hqMode (TE (PE d)) = TE (PE d) from
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotB]
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH

include hqMode hfin hk in
/-- Helper toward Lemma 5.5: the primed factor fixes every terminal
prefix non-port, by the exact prefix/primed intersection. -/
theorem lPlus_terminal_prefix_primed_fixed (hn : 0 < (es).length)
    (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : p.val ≠ (es[(es).length - 1], false)) :
    TE (IP p) = IP p := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  rintro ⟨q, hq⟩
  have he : lMinusPrimedDartImage hτ q = p.val :=
    (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hq
  exact hport (lPlus_terminal_prefix_primed_intersection hτ hfin hk hn p hv ⟨q, he⟩)

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the terminal rotation 4 factors into two
explicit swaps after the prefix and primed factors. -/
theorem lPlus_terminal_rotation4_factors (hn : 0 < (es).length) (d : Q)
    (hv : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(es).length - 1, by omega⟩, false)
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d =
      Equiv.swap t (PE t) (Equiv.swap (TE (PE t)) (TE t) (TE (PE d))) := by
  dsimp only
  rw [lPlusGluedCorrectedRotation4_apply hτ hp P hqMode Tpath hfin hleft hk hn,
    lPlusGluedCorrectedRotation2_eq_blockRotation2 hτ hqMode hfin hk hp P Tpath hleft]
  unfold lPlusGluedBlockRotation2
  rw [dite_eq_left hn]
  dsimp only
  rw [Equiv.Perm.mul_apply,
    lPlus_terminal_block_rotation hτ hp P hqMode Tpath hfin hleft hk hn d hv,
    lPlus_terminal_block_rotation hτ hp P hqMode Tpath hfin hleft hk hn _ rfl]

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: rotation 4 transports every terminal prefix
non-port, including the finite predecessor of the terminal port. -/
theorem lPlusGluedCorrectedRotation4_terminal_prefix_nonport
    (hn : 0 < (es).length) (p : LPlusPrefixDart W h k)
    (hv : kmswLimitDartVertex w p.val =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : p.val ≠ (es[(es).length - 1], false)) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk (IP p) =
      IP (PR p) := by
  let i : Fin (es).length := ⟨(es).length - 1, by omega⟩
  let tp : LPlusPrefixDart W h k :=
    ⟨(es[i.val], false), lPlusUpperLeftEdge_mem_prefix hτ hfin hk i⟩
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
  let b := PE t
  let y := IP (PR p)
  have ht : t = IP tp := rfl
  have hb : b = IP (PR tp) := (PR).extendDomain_apply_image _ tp
  have hy : PE (IP p) = y := (PR).extendDomain_apply_image _ p
  have hyv : kmswLimitDartVertex w (D y).val =
      kmswLimitDartVertex w (es[(es).length - 1], false) :=
    (lPlus_prefix_rotation_vertex hτ hp P hqMode Tpath hfin hleft hk p).trans hv
  have hdt : IP p ≠ t := fun he => hport (congrArg (fun q => (D q).val) he)
  have hyb : y ≠ b := fun he => hdt ((PE).injective (hy.trans he))
  rw [lPlus_terminal_rotation4_factors hτ hp P hqMode Tpath hfin hleft hk hn (IP p) hv]
  change Equiv.swap t b (Equiv.swap (TE b) (TE t) (TE (PE (IP p)))) = y
  rw [hy]
  by_cases hyt : y = t
  · have hbt : b ≠ t := fun he => hyb (hyt.trans he.symm)
    have hTEb : TE b = b := by
      rw [hb]
      apply lPlus_terminal_prefix_primed_fixed hτ hqMode hfin hk hn
        (PR tp) (lPlus_prefix_rotation_vertex hτ hp P hqMode Tpath hfin hleft hk tp)
      intro he
      exact hbt ((D).injective (Subtype.ext
        ((congrArg (fun q => (D q).val) hb).trans he)))
    rw [hyt, Equiv.swap_apply_right, hTEb, Equiv.swap_apply_right]
  · have hTEy : TE y = y := by
      apply lPlus_terminal_prefix_primed_fixed hτ hqMode hfin hk hn
        (PR p) hyv
      intro he
      exact hyt ((D).injective (Subtype.ext he))
    rw [Equiv.swap_apply_of_ne_of_ne
      (fun he => hyb ((TE).injective he)) (fun he => hyt ((TE).injective he)), hTEy,
      Equiv.swap_apply_of_ne_of_ne hyt hyb]

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: rotation 4 transports every terminal
primed non-port, with its own-block terminal return redirected to the
finite-prefix successor of the terminal port. -/
theorem lPlusGluedCorrectedRotation4_terminal_primed_nonport
    (hn : 0 < (es).length) (p : ℕ × Bool)
    (hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w (es[(es).length - 1], false))
    (hport : lMinusPrimedDartImage hτ p ≠ (es[(es).length - 1], false)) :
    (S).rotation (D (IT p)).val
      (D (lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk (IT p))).val := by
  let i : Fin (es).length := ⟨(es).length - 1, by omega⟩
  let tp : LPlusPrefixDart W h k :=
    ⟨(es[i.val], false), lPlusUpperLeftEdge_mem_prefix hτ hfin hk i⟩
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
  let d := IT p
  let b := PE t
  let y := TE d
  have hb : b = IP (PR tp) := (PR).extendDomain_apply_image _ tp
  have hbv : kmswLimitDartVertex w (PR tp).val =
      kmswLimitDartVertex w (es[(es).length - 1], false) :=
    lPlus_prefix_rotation_vertex hτ hp P hqMode Tpath hfin hleft hk tp
  have hnotP : d ∉ Set.range IP := by
    rintro ⟨q, hq⟩
    have he : q.val = lMinusPrimedDartImage hτ p :=
      congrArg (fun a => (D a).val) hq
    exact hport (he.symm.trans (lPlus_terminal_prefix_primed_intersection
      hτ hfin hk hn q ((congrArg (kmswLimitDartVertex w) he).trans hv) ⟨p, he.symm⟩))
  have hPE : PE d = d := Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotP
  have hdt : d ≠ t := fun he => hport (congrArg (fun q => (D q).val) he)
  have hdb : d ≠ b := fun he => hnotP ⟨PR tp, hb.symm.trans he.symm⟩
  have hTE : y = IT (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) p) :=
    (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin)).extendDomain_apply_image _ p
  have hcalc : lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d =
      if y = t then b else y := by
    rw [lPlus_terminal_rotation4_factors hτ hp P hqMode Tpath hfin hleft hk hn d hv]
    change Equiv.swap t b (Equiv.swap (TE b) (TE t) (TE (PE d))) = _
    rw [hPE, Equiv.swap_apply_of_ne_of_ne
      (fun he => hdb ((TE).injective he)) (fun he => hdt ((TE).injective he))]
    change Equiv.swap t b y = _
    by_cases hyt : y = t
    · rw [ite_eq_left hyt, hyt, Equiv.swap_apply_left]
    · have hyb : y ≠ b := by
        intro he
        have he' : (PR tp).val = lMinusPrimedDartImage hτ
            (kmswInfRot (primedCode (primedSimInput U) hτ)
              (primedCode_finiteIncidence U hτ hfin) p) :=
          congrArg (fun q => (D q).val) (hb.symm.trans (he.symm.trans hTE))
        have hbt : b = t := (D).injective (Subtype.ext
          ((congrArg (fun q => (D q).val) hb).trans
            (lPlus_terminal_prefix_primed_intersection hτ hfin hk hn (PR tp) hbv
              ⟨_, he'.symm⟩)))
        exact hyt (he.trans hbt)
      rw [ite_eq_right hyt, Equiv.swap_apply_of_ne_of_ne hyt hyb]
  have hactual := lPlus_terminal_primed_side_rotation hτ hp P hqMode Tpath hfin hleft hk
    hn tp rfl p hv hport
  dsimp only at hactual
  rw [hcalc]
  by_cases hyt : y = t
  · rw [ite_eq_left hyt, hb]
    have he : lMinusPrimedDartImage hτ
        (kmswInfRot (primedCode (primedSimInput U) hτ)
          (primedCode_finiteIncidence U hτ hfin) p) = tp.val :=
      congrArg (fun q => (D q).val) (hTE.symm.trans hyt)
    rw [ite_eq_left he] at hactual
    exact hactual
  · rw [ite_eq_right hyt, hTE]
    have he : lMinusPrimedDartImage hτ
        (kmswInfRot (primedCode (primedSimInput U) hτ)
          (primedCode_finiteIncidence U hτ hfin) p) ≠ tp.val := by
      intro he
      exact hyt ((D).injective (Subtype.ext
        ((congrArg (fun q => (D q).val) hTE).trans he)))
    rw [ite_eq_right he] at hactual
    exact hactual

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: rotation 4 transports the entire terminal
vertex star, with the exact unrestricted decoder binders. -/
theorem lPlusGluedCorrectedRotation4_terminal_vertex_rotation_iff
    (hn : 0 < (es).length) (d e : Q)
    (hd : kmswLimitDartVertex w (D d).val =
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
      (S).rotation (D d).val (D e).val := by
  let C := lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(es).length - 1, by omega⟩, false)
  have hrot : (S).rotation (D d).val (D (C d)).val := by
    by_cases hport : (D d).val = (es[(es).length - 1], false)
    · have hdt : d = t := (D).injective (Subtype.ext hport)
      rw [hdt]
      exact (lPlusGluedCorrectedRotation4_terminal_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk hn (C t)).mp rfl
    · rcases (lPlus_terminal_side_mem_iff hτ hp P hqMode Tpath hfin hleft hk
        hn (D d).val hd).mp (D d).property with hpre | ⟨p, hp'⟩
      · let p : LPlusPrefixDart W h k := ⟨(D d).val, hpre⟩
        have hdp : d = IP p := (D).injective (Subtype.ext rfl)
        rw [hdp]
        change (S).rotation p.val (D (C (IP p))).val
        rw [show C (IP p) = IP (PR p) from
          lPlusGluedCorrectedRotation4_terminal_prefix_nonport
            hτ hp P hqMode Tpath hfin hleft hk hn p hd hport]
        exact lPlus_terminal_prefix_nonport_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk hn p hd hport
      · have hdp : d = IT p := (D).injective (Subtype.ext hp'.symm)
        rw [hdp]
        exact lPlusGluedCorrectedRotation4_terminal_primed_nonport
          hτ hp P hqMode Tpath hfin hleft hk hn p
          ((congrArg (kmswLimitDartVertex w) hp').trans hd)
          (fun he => hport (hp'.symm.trans he))
  constructor
  · intro he
    exact he ▸ hrot
  · intro he
    exact (D).injective (Subtype.ext (firstReturn_endpoint_unique
      (kmswInfRot w (H.1 0) : _ → _) {a : ℕ × Bool | a.1 ∈ (S).edges}
      (D (C d)).property (D e).property hrot he))

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: rotation 4 transports every dart, including
the empty attachment and every terminal prefix and primed class. -/
theorem lPlusGluedCorrectedRotation4_rotation_iff (d e : Q) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
      (S).rotation (D d).val (D e).val := by
  by_cases hn : 0 < (es).length
  · by_cases hd : kmswLimitDartVertex w (D d).val =
        kmswLimitDartVertex w (es[(es).length - 1], false)
    · exact lPlusGluedCorrectedRotation4_terminal_vertex_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk hn d e hd
    · exact lPlusGluedCorrectedRotation4_rotation_iff_of_ne_terminal
        hτ hp P hqMode Tpath hfin hleft hk hn d e hd
  · exact lPlusGluedCorrectedRotation4_rotation_iff_of_empty
      hτ hp P hqMode Tpath hfin hleft hk hn d e

include hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the corrected code block side has its
unrestricted marked isomorphism with the actual nonnegative left side. -/
theorem boundaryGluing_nonneg_left_markedIso_lPlusCodeBlockSide4 :
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
        exact (lPlusGluedCorrectedRotation4_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk a b).symm.trans
            (lPlusCodeBlockSide4_rotation_glued_iff
              hτ hp P hqMode Tpath hfin hleft hk a b).symm
  · exact lPlusActualCodeBlockCellEquiv4_relation_iff_of_ne_rotation
      hτ hp P hqMode Tpath hfin hleft hk r hr u v

end DirectedDistances.PaperProofs.Section5

/- Validation (2026-11-06): all 25 declarations in this file were checked
by temporary `#print axioms` probes, each reporting exactly
[propext, Classical.choice, Quot.sound]. The three unrestricted targets were
also elaborated with `#check @...`, retaining the binders recorded in
CorrectedDecoder3:731,770,797. All probes were removed.
Development compile exits: 1,0,0,1,1,0,1,0,1,0,1,0,1,0,0,0.
The temporary axiom/signature probe compile exited 0. Only the prescribed
coordinator. These are helpers toward Lemma 5.5, not a paper-completion claim. -/

