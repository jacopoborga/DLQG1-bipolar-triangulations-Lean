/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff3

/-! Helper toward Lemma 5.5: nonnegative left attachment rotation separation. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: consecutive geometric values in the outer
word determine the finite face successor, retaining the dart bits. -/
private theorem lPlus_attachment_outer_step (u : ℕ → Fin 3) (n j : ℕ)
    (a b : ℕ × Bool)
    (ha : (stageOuterWordVal u n)[j]? = some a)
    (hb : (stageOuterWordVal u n)[j + 1]? = some b) :
    ∃ d e : StageDart (kmswStage u n).nextEdge,
      (d.1.val, d.2) = a ∧ (e.1.val, e.2) = b ∧
        (kmswMap u n).faceSucc d = e := by
  obtain ⟨d, e, hd, he, hde⟩ := outer_faceSucc_exists u n
    (stageOuterWord_faceSucc u n) j (List.getElem?_eq_some_iff.mp ha).1
  rw [Nat.mod_eq_of_lt (List.getElem?_eq_some_iff.mp hb).1] at he
  exact ⟨d, e, Option.some.inj (hd.symm.trans ha),
    Option.some.inj (he.symm.trans hb), hde⟩

/-- Helper toward Lemma 5.5: lower-left indices counted from the root
persist under subsequent KMSW steps. -/
private theorem lPlus_attachment_LL_index_persists (u : ℕ → Fin 3) (a b i : ℕ)
    (hab : a ≤ b) (hi : i < (kmswStage u a).LL.reverse.length) :
    (kmswStage u b).LL.reverse[i]? = (kmswStage u a).LL.reverse[i]? := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hib : i < (kmswStage u b).LL.reverse.length := by
      have hs := List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
      rw [← ih] at hs
      exact (List.getElem?_eq_some_iff.mp hs).1
    generalize hc : u b = c
    fin_cases c
    · cases hp : (kmswStage u b).UL.dropLast.reverse with
      | nil =>
        have hs : (kmswStage u (b + 1)).LL.reverse =
            (kmswStage u b).LL.reverse ++ [(kmswStage u b).nextEdge + 1] := by
          simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
        rw [hs, List.getElem?_append_left hib, ih]
      | cons f fs =>
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp,
          State.addEdge] using ih
    · simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
        State.addEdge] using ih
    · cases hp : (kmswStage u b).UR <;>
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp,
          State.addEdge] using ih

/-- Helper toward Lemma 5.5: the retained primed root immediately
precedes the lower-left run in the finite outer word. -/
private theorem lPlus_attachment_primed_word (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (n i e : ℕ)
    (he : (0 :: (kmswStage (primedCode (primedSimInput w) h) n).LL.reverse)[i]? = some e) :
    let u := primedCode (primedSimInput w) h
    (stageOuterWordVal u n)[(kmswStage u n).UL.length +
      (kmswStage u n).UR.length + i]? = some (e, true) := by
  dsimp only
  rw [stageOuterWordVal_eq_runs, primedStage_LR_eq_root]
  simp only [List.reverse_singleton, List.map_cons, List.map_nil, List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  have hidx : ∀ a b : ℕ, a + b + i - a - b = i := by omega
  rw [hidx]
  change ((0 :: (kmswStage (primedCode (primedSimInput w) h) n).LL.reverse).map
    (fun e => (e, true)))[i]? = _
  rw [List.getElem?_map, he]
  rfl

/-- Helper toward Lemma 5.5: two consecutive root/LL ports of the
independent primed code bound its exterior corner. The order persists at
every later stage, including a pair whose first edge is the retained root. -/
theorem lPlusPrimedRotation_lowerLeft_corner (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hf : primedLimitFiniteIncidence w)
    (m i a b : ℕ)
    (ha : (0 :: (kmswStage (primedCode (primedSimInput w) h) m).LL.reverse)[i]? = some a)
    (hb : (0 :: (kmswStage (primedCode (primedSimInput w) h) m).LL.reverse)[i + 1]? = some b) :
    kmswInfRot (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hf) (b, true) = (a, false) := by
  let u := primedCode (primedSimInput w) h
  have hstable (j n : ℕ) (hj : j < (0 :: (kmswStage u m).LL.reverse).length)
      (hn : m ≤ n) :
      (0 :: (kmswStage u n).LL.reverse)[j]? =
        (0 :: (kmswStage u m).LL.reverse)[j]? := by
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getElem?_cons_succ]
      exact lPlus_attachment_LL_index_persists u m n j hn (by simpa using hj)
  have hface : kmswInfFaceSucc u (primedCode_finiteIncidence w h hf)
      (a, true) = (b, true) := by
    apply kmswInfFaceSucc_eq_of_stages
    refine ⟨m, fun n hn => ?_⟩
    have ha' := (hstable i n (List.getElem?_eq_some_iff.mp ha).1 hn).trans ha
    have hb' := (hstable (i + 1) n (List.getElem?_eq_some_iff.mp hb).1 hn).trans hb
    exact lPlus_attachment_outer_step u n
      ((kmswStage u n).UL.length + (kmswStage u n).UR.length + i) _ _
      (lPlus_attachment_primed_word w h n i a ha')
      (by simpa only [Nat.add_assoc] using lPlus_attachment_primed_word w h n (i + 1) b hb')
  change (kmswInfRot u (primedCode_finiteIncidence w h hf)).symm (a, false) =
    (b, true) at hface
  have hr := congrArg (kmswInfRot u (primedCode_finiteIncidence w h hf)) hface
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

/-- Helper toward Lemma 5.5: consecutive edges read backward along the
upper-left list determine the finite exterior rotation corner. -/
theorem lPlusStageRotation_upperLeft_corner (w : ℕ → Fin 3) (n i a b : ℕ)
    (ha : (kmswStage w n).UL.reverse[i]? = some a)
    (hb : (kmswStage w n).UL.reverse[i + 1]? = some b) :
    ∃ ha' : a < (kmswStage w n).nextEdge, ∃ hb' : b < (kmswStage w n).nextEdge,
      stageRot w n (⟨a, ha'⟩, false) = (⟨b, hb'⟩, true) := by
  let s := kmswStage w n
  have hi : i + 1 < s.UL.length := by
    simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hb).1
  change s.UL.reverse[i]? = some a at ha
  change s.UL.reverse[i + 1]? = some b at hb
  have ha0 : s.UL[s.UL.length - 1 - i]? = some a := by
    rw [List.getElem?_reverse (by omega)] at ha
    exact ha
  have hb0 : s.UL[s.UL.length - 1 - (i + 1)]? = some b := by
    rw [List.getElem?_reverse (by omega)] at hb
    exact hb
  have hword (j e : ℕ) (he : s.UL[j]? = some e) :
      (stageOuterWordVal w n)[j]? = some (e, false) := by
    have hj := (List.getElem?_eq_some_iff.mp he).1
    change j < (kmswStage w n).UL.length at hj
    rw [stageOuterWordVal_eq_runs]
    rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map]; omega),
      List.getElem?_append_left (by simp only [List.length_append, List.length_map]; omega),
      List.getElem?_append_left (by simp only [List.length_map]; exact hj),
      List.getElem?_map, he]
    rfl
  have hidx : s.UL.length - 1 - (i + 1) + 1 = s.UL.length - 1 - i := by omega
  obtain ⟨d, e, hd, he, hde⟩ := lPlus_attachment_outer_step w n
    (s.UL.length - 1 - (i + 1)) _ _ (hword _ b hb0)
      (by rw [hidx]; exact hword _ a ha0)
  have hea : e.1.val = a := congrArg (fun z : ℕ × Bool => z.1) he
  have hdb : d.1.val = b := congrArg (fun z : ℕ × Bool => z.1) hd
  have ha' : a < s.nextEdge := by rw [← hea]; exact e.1.isLt
  have hb' : b < s.nextEdge := by rw [← hdb]; exact d.1.isLt
  refine ⟨ha', hb', ?_⟩
  have hd' : d = (⟨b, hb'⟩, false) :=
    Prod.ext (Fin.ext hdb) (congrArg (fun z : ℕ × Bool => z.2) hd)
  have he' : e = (⟨a, ha'⟩, false) :=
    Prod.ext (Fin.ext hea) (congrArg (fun z : ℕ × Bool => z.2) he)
  rw [hd', he'] at hde
  change (stageRot w n).symm (⟨b, hb'⟩, true) = (⟨a, ha'⟩, false) at hde
  have hr := congrArg (stageRot w n) hde
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W} {longest : Bool}

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "ULedges" =>
  (List.reverse (List.dropLast (State.UL
    (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)))))

/-- Helper toward Lemma 5.5: the positive stopped attachment is exactly
the upper-left list at the preceding stage, without the new active edge. -/
theorem lPlus_attachment_upperLeft_eq_previous (hk : 0 < k) :
    ULedges = (kmswStage w (boundaryHitTime w h k - 1)).UL.reverse := by
  obtain ⟨m, hm, hc, hur⟩ := lPlus_positive_hit_fresh w h hk
  rw [hm, Nat.add_sub_cancel]
  change (kmswStep (kmswStage w m) (w m)).UL.dropLast.reverse = _
  rw [hc]
  simp only [kmswStep, kmswCodeStep, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, kmswStepOfStep, hur,
    State.addEdge, List.dropLast_concat]

/-- Helper toward Lemma 5.5: each interior attachment corner has an
ambient arc excluding the deleted prefix in its open part. -/
theorem lPlus_prefix_upperLeft_boundary_gap
    (hτ : HasFlowLineHits U)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hk : 0 < k) (i a b : ℕ)
    (ha : ULedges[i]? = some a) (hb : ULedges[i + 1]? = some b) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (a, false) = (b, true) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (a, false) ∉
          Set.range (fun d : LPlusPrefixDart W h k => d.val) := by
  rw [lPlus_attachment_upperLeft_eq_previous hk] at ha hb
  obtain ⟨ha', hb', hcorner⟩ := lPlusStageRotation_upperLeft_corner w
    (boundaryHitTime w h k - 1) i a b ha hb
  let d := lPlusPrefixStageDart (W := W) (h := h) hk (⟨a, ha'⟩, false)
  have hr := lPlusPrefixDartImage_firstReturn (H := H) hτ longest hqMode hk d
  change ∃ n : ℕ, 0 < n ∧
    (kmswInfRot w (H.1 0) : _ → _)^[n] (a, false) =
      ((stageRot w (boundaryHitTime w h k - 1) (⟨a, ha'⟩, false)).1.val,
        (stageRot w (boundaryHitTime w h k - 1) (⟨a, ha'⟩, false)).2) ∧ _ at hr
  rw [hcorner] at hr
  exact hr

/-- Helper toward Lemma 5.5: each interior attachment corner has the
complementary ambient arc excluding the independent primed block. The
corrected ordered attachment supplies the two actual primed ports. -/
theorem lPlus_primed_upperLeft_boundary_gap
    (hτ : HasFlowLineHits U)
    (hfin : hatLimitFiniteIncidence U) (i a b : ℕ)
    (ha : ULedges[i]? = some a) (hb : ULedges[i + 1]? = some b) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (b, true) = (a, false) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (b, true) ∉
          Set.range (lMinusPrimedDartImage hτ) := by
  let u := primedCode (primedSimInput U) hτ
  obtain ⟨m, hm⟩ := lPlus_prefix_primed_ordered_dart_image hτ
  have hmap : ((0 :: (kmswStage u m).LL.reverse).take (ULedges).length).map
      (fun e => lMinusPrimedDartImage hτ (e, true)) =
        (ULedges).map (fun e => (e, true)) := by
    simpa only [List.map_map, Function.comp_def, lPlusPrefixUpperLeftDarts_eq,
      List.length_map] using hm
  have hlift (j e : ℕ) (he : ULedges[j]? = some e) :
      ∃ c, (0 :: (kmswStage u m).LL.reverse)[j]? = some c ∧
        lMinusPrimedDartImage hτ (c, true) = (e, true) := by
    have hj := (List.getElem?_eq_some_iff.mp he).1
    have hh := congrArg (fun r : List (ℕ × Bool) => r[j]?) hmap
    rw [List.getElem?_map, List.getElem?_map, he, Option.map_some] at hh
    obtain ⟨c, hc, hce⟩ := Option.map_eq_some_iff.mp hh
    rw [List.getElem?_take_of_lt hj] at hc
    exact ⟨c, hc, hce⟩
  obtain ⟨a', ha', hia⟩ := hlift i a ha
  obtain ⟨b', hb', hib⟩ := hlift (i + 1) b hb
  have hcorner := lPlusPrimedRotation_lowerLeft_corner U hτ hfin m i a' b' ha' hb'
  have hia' : lMinusPrimedDartImage hτ (a', false) = (a, false) := by
    have he : boundaryGluingPrimedEdgeMap W h k hτ a' = a :=
      congrArg (fun d : ℕ × Bool => d.1) hia
    have hs := congrArg (fun d : ℕ × Bool => d.2) hia
    apply Prod.ext (show (lMinusPrimedDartImage hτ (a', false)).1 = a from he)
    change (false ^^ primedLimitSideFlip U hτ a') = false
    change (true ^^ primedLimitSideFlip U hτ a') = true at hs
    cases hf : primedLimitSideFlip U hτ a' <;> simp_all only [Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.false_eq_true]
  obtain ⟨n, hn, hret, hgap⟩ := lMinusPrimedDartImage_firstReturn
    (H := H) hτ hfin (b', true)
  rw [hcorner, hib, hia'] at hret
  refine ⟨n, hn, hret, ?_⟩
  intro j hj hjn
  simpa only [hib] using hgap j hj hjn

/-- Helper toward Lemma 5.5: the two upper-left exterior arcs form a
complete minimal ambient vertex cycle. The open arcs exclude respectively
the prefix and primed blocks; both endpoint darts retain their identities. -/
theorem lPlus_upperLeft_rotation_separation
    (hτ : HasFlowLineHits U)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence U) (hk : 0 < k) (i a b : ℕ)
    (ha : ULedges[i]? = some a) (hb : ULedges[i + 1]? = some b) :
    let σ := kmswInfRot w (H.1 0)
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (σ : _ → _)^[n] (a, false) = (b, true) ∧
      (σ : _ → _)^[m] (b, true) = (a, false) ∧
      (∀ j : ℕ, 0 < j → j < n → (σ : _ → _)^[j] (a, false) ∉
        Set.range (fun d : LPlusPrefixDart W h k => d.val)) ∧
      (∀ j : ℕ, 0 < j → j < m → (σ : _ → _)^[j] (b, true) ∉
        Set.range (lMinusPrimedDartImage hτ)) ∧
      (σ : _ → _)^[n + m] (a, false) = (a, false) ∧
      ∀ j : ℕ, 0 < j → j < n + m →
        (σ : _ → _)^[j] (a, false) ≠ (a, false) := by
  dsimp only
  let σ := kmswInfRot w (H.1 0)
  obtain ⟨n, hn, hna, hgapP⟩ := lPlus_prefix_upperLeft_boundary_gap
    (H := H) hτ hqMode hk i a b ha hb
  obtain ⟨m, hm, hmb, hgapT⟩ := lPlus_primed_upperLeft_boundary_gap
    (H := H) hτ hfin i a b ha hb
  have haP : (a, false) ∈ Set.range (fun d : LPlusPrefixDart W h k => d.val) := by
    have hai := (List.getElem?_eq_some_iff.mp ha).1
    have hea : a = ULedges[i] := (List.getElem?_eq_some_iff.mp ha).2.symm
    refine ⟨⟨(a, false), ?_⟩, rfl⟩
    rw [hea]
    exact lPlusUpperLeftEdge_mem_prefix hτ hfin hk.le ⟨i, hai⟩
  have haT : (a, false) ∈ Set.range (lMinusPrimedDartImage hτ) := by
    have hu : a ∈ boundaryGluingUpperLeftEdges W h k :=
      List.mem_reverse.mp (List.mem_of_getElem? ha)
    obtain ⟨e, he⟩ := boundaryGluingUpperLeftEdges_subset_primedEdges W h k hτ hfin hu
    refine ⟨(e, primedLimitSideFlip U hτ e), ?_⟩
    apply Prod.ext he
    change (primedLimitSideFlip U hτ e ^^ primedLimitSideFlip U hτ e) = false
    exact Bool.xor_self _
  refine ⟨n, m, hn, hm, hna, hmb, hgapP, hgapT, ?_, ?_⟩
  · rw [Nat.add_comm n m, Function.iterate_add_apply, hna, hmb]
  · intro j hj hjnm he
    by_cases hjn : j < n
    · exact hgapP j hj hjn (he.symm ▸ haP)
    · by_cases hjeq : j = n
      · subst j
        exact (by decide : true ≠ false)
          (congrArg (fun d : ℕ × Bool => d.2) (hna.symm.trans he))
      · apply hgapT (j - n) (by omega) (by omega)
        have hs : (σ : _ → _)^[j - n] (b, true) = (a, false) := by
          rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
          exact he
        exact hs.symm ▸ haT

/-- Helper toward Lemma 5.5: the west endpoint of a future LL edge is
unreachable from the future root. Missing edges remain geometric edges. -/
private theorem lPlus_attachment_LL_west_unreachable (u : ℕ → Fin 3)
    (hu : BoundaryHitWitnesses u) (n e : ℕ) (he : e ∈ (kmswStage u n).LL) :
    ¬ MhatVertex u (edgeWest u e) := by
  have hrec : ∃ m, 0 < m ∧ (∀ j < m, L u m < L u j) ∧
      e = kmswLLCreatedEdge u m := by
    rw [kmswStage_LL_eq] at he
    obtain ⟨m, hm, hme⟩ := List.mem_map.mp he
    have hr := of_decide_eq_true (List.mem_filter.mp (List.mem_reverse.mp hm)).2
    exact ⟨m, hr.1, hr.2, hme.symm⟩
  obtain ⟨m, hm, hstrict, rfl⟩ := hrec
  have hk : L u m ≤ -1 := by
    have hh := hstrict 0 hm
    have hz : L u 0 = 0 := rfl
    omega
  have hfind : Nat.find (hu.leftHit (L u m) hk) = m := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (hu.leftHit (L u m) hk) rfl
    · by_contra hh
      have hs := hstrict (Nat.find (hu.leftHit (L u m) hk)) (by omega)
      have ht := Nat.find_spec (hu.leftHit (L u m) hk)
      omega
  have htime : boundaryHitTime u hu (L u m) = m := by
    simp only [boundaryHitTime, dite_eq_right (by omega : L u m ≠ 0),
      dite_eq_right (by omega : ¬ 0 < L u m)]
    exact hfind
  have hw : edgeWest u (kmswLLCreatedEdge u m) = boundaryVertex u hu (L u m) := by
    have hh := (boundaryVertex_left_missing_edge u hu hk).1
    rw [htime] at hh
    have hbound : kmswLLCreatedEdge u m < (kmswStage u m).nextEdge := by
      have hn := kmswStage_nextEdge_mono u (m := 0) (n := m) (Nat.zero_le _)
      change 1 ≤ (kmswStage u m).nextEdge at hn
      dsimp only [kmswLLCreatedEdge]
      omega
    exact (edge_endpoints_eq u hbound).1.symm.trans hh
  have hnzero : edgeWest u (kmswLLCreatedEdge u m) ≠ 0 := by
    intro hz
    have heq : boundaryVertex u hu (L u m) = boundaryVertex u hu 0 := by
      rw [← hw, hz, boundaryVertex_zero]
    have hh := boundaryVertex_injective u hu heq
    omega
  have noReach (v : PresentVertex u) (hv : v.id ≠ 0)
      (hi : ∀ f, EdgePresent u f → edgeEast u f ≠ v.id) :
      ¬ Quiver.Reachable (⟨0⟩ : PresentVertex u) v := by
    intro ⟨p⟩
    cases p with
    | nil => exact hv rfl
    | cons p f => exact hi f.val f.property.1 f.property.2.2
  apply noReach ⟨edgeWest u (kmswLLCreatedEdge u m)⟩ hnzero
  intro f hf heq
  exact boundaryVertex_nonpos_no_incoming u hu (by omega) f hf (heq.trans hw)

/-- Helper toward Lemma 5.5: the west endpoint of every upper-left
attachment edge has no incident hatted dart. This also covers the terminal
endpoint of the finite attachment, with no recurrence or separation premise. -/
theorem lPlus_upperLeft_west_not_hatted (hτ : HasFlowLineHits U)
    (i a : ℕ) (ha : ULedges[i]? = some a) (d : ℕ × Bool) :
    kmswLimitDartVertex w (a, false) ≠
      kmswLimitDartVertex w (boundaryGluingHatEdgeMap W h k hτ d.1, d.2) := by
  obtain ⟨m, hm⟩ := lPlus_prefix_future_LL_initial_segment hτ
  let n := primedStageTime U hτ m
  have hmap : ((kmswStage U n).LL.reverse.take (ULedges).length).map
      (boundaryGluingEdgeMap W h k) = ULedges := by
    simpa only [List.length_reverse] using hm
  have hi := (List.getElem?_eq_some_iff.mp ha).1
  have hx := congrArg (fun r : List ℕ => r[i]?) hmap
  rw [List.getElem?_map, ha] at hx
  obtain ⟨f, hf, hfa⟩ := Option.map_eq_some_iff.mp hx
  rw [List.getElem?_take_of_lt hi] at hf
  have hfLL : f ∈ (kmswStage U n).LL := List.mem_reverse.mp
    (List.mem_of_getElem? hf)
  have hno := lPlus_attachment_LL_west_unreachable U
    (hatBoundaryHitWitnesses U hτ) n f hfLL
  intro heq
  have hw := (boundaryGluing_future_edge_endpoints W h k f).1
  rw [hfa] at hw
  have hh : kmswLimitDartVertex w (boundaryGluingHatEdgeMap W h k hτ d.1, d.2) =
      boundaryGluingFutureVertexMap W h k
        (kmswDartEndpoint U (hatLimitEdgeMap U hτ d.1, d.2)) := by
    have hg := boundaryGluing_future_edge_endpoints W h k (hatLimitEdgeMap U hτ d.1)
    cases hb : d.2
    · exact hg.1
    · exact hg.2
  have hv : edgeWest U f =
      kmswDartEndpoint U (hatLimitEdgeMap U hτ d.1, d.2) := by
    apply boundaryGluingFutureVertexMap_injective W h k
    exact hw.symm.trans (heq.trans hh)
  apply hno
  rw [hv]
  have he := (hatExplicitEdgeEquiv U hτ
    ⟨d.1, hatCodes_edge_present U hτ d.1⟩).property
  cases hb : d.2
  · simpa only [MhatVertex, kmswDartEndpoint, hb, Bool.false_eq_true, ↓reduceIte,
      hatExplicitEdgeEquiv_apply] using he.2.1
  · simpa only [MhatVertex, kmswDartEndpoint, hb, ↓reduceIte,
      hatExplicitEdgeEquiv_apply] using he.2.2

/-- Helper toward Lemma 5.5: at the west port of an interior upper-left
attachment the primed return has no intervening dart from any of the three
glued blocks. The primed representative and all gaps are proved internally. -/
theorem lPlus_upperLeft_interior_west_firstReturn
    (hτ : HasFlowLineHits U)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence U) (hk : 0 < k) (i a b : ℕ)
    (ha : ULedges[i]? = some a) (hb : ULedges[i + 1]? = some b) :
    let M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
    let F := lPlusBlockDartImage (M := M) hτ
    let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin)
    ∃ p : ℕ × Bool, lMinusPrimedDartImage hτ p = (a, false) ∧
      ∃ t : ℕ, 0 < t ∧
        (kmswInfRot w (H.1 0) : _ → _)^[t] (a, false) =
          lMinusPrimedDartImage hτ (TR p) ∧
        ∀ j : ℕ, 0 < j → j < t →
          (kmswInfRot w (H.1 0) : _ → _)^[j] (a, false) ∉ Set.range F := by
  dsimp only
  let M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
  let F := lPlusBlockDartImage (M := M) hτ
  have hlift (j e : ℕ) (he : ULedges[j]? = some e) (c : Bool) :
      ∃ p : ℕ × Bool, lMinusPrimedDartImage hτ p = (e, c) := by
    have hu : e ∈ boundaryGluingUpperLeftEdges W h k :=
      List.mem_reverse.mp (List.mem_of_getElem? he)
    obtain ⟨f, hf⟩ := boundaryGluingUpperLeftEdges_subset_primedEdges W h k hτ hfin hu
    refine ⟨(f, c ^^ primedLimitSideFlip U hτ f), ?_⟩
    change (boundaryGluingPrimedEdgeMap W h k hτ f,
      (c ^^ primedLimitSideFlip U hτ f) ^^ primedLimitSideFlip U hτ f) = (e, c)
    exact Prod.ext hf (by rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false])
  obtain ⟨p, hp⟩ := hlift i a ha false
  obtain ⟨q, hq⟩ := hlift (i + 1) b hb true
  obtain ⟨n, hn, hna, hgapP⟩ := lPlus_prefix_upperLeft_boundary_gap
    (H := H) hτ hqMode hk i a b ha hb
  obtain ⟨t, ht, hret, hgapT⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  rw [hp] at hret hgapT
  have hbound : t ≤ n := by
    by_contra hh
    exact hgapT n hn (by omega) ⟨q, hq.trans hna.symm⟩
  refine ⟨p, hp, t, ht, hret, ?_⟩
  intro j hj hjt ⟨c, hc⟩
  cases c with
  | inl c => exact hgapP j hj (by omega) ⟨c, hc⟩
  | inr c =>
    cases c with
    | inl c => exact hgapT j hj hjt ⟨c, hc⟩
    | inr c =>
      have hv := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) (a, false)
        ((kmswInfRot w (H.1 0) : _ → _)^[j] (a, false))).mp
          ⟨j, by simp only [Equiv.Perm.coe_pow]⟩
      exact lPlus_upperLeft_west_not_hatted hτ i a ha c.val
        (hv.trans (congrArg (kmswLimitDartVertex w) hc.symm))

/-- Helper toward Lemma 5.5: at the east port of an interior upper-left
attachment the prefix return has no intervening dart from any glued block.
The complementary primed exterior arc bounds this return. -/
theorem lPlus_upperLeft_interior_east_firstReturn
    (hτ : HasFlowLineHits U)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence U) (hk : 0 < k) (i a b : ℕ)
    (ha : ULedges[i]? = some a) (hb : ULedges[i + 1]? = some b) :
    let M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
    let F := lPlusBlockDartImage (M := M) hτ
    ∃ p : LPlusPrefixDart W h k, p.val = (b, true) ∧
      ∃ t : ℕ, 0 < t ∧
        (kmswInfRot w (H.1 0) : _ → _)^[t] (b, true) =
          (lPlusPrefixStageDart hk (stageRot w (boundaryHitTime w h k - 1)
            (lPlusPrefixDartStage hk p))).val ∧
        ∀ j : ℕ, 0 < j → j < t →
          (kmswInfRot w (H.1 0) : _ → _)^[j] (b, true) ∉ Set.range F := by
  dsimp only
  let M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
  let F := lPlusBlockDartImage (M := M) hτ
  have hlift (j e : ℕ) (he : ULedges[j]? = some e) (c : Bool) :
      ∃ p : LPlusPrefixDart W h k, p.val = (e, c) := by
    obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.mp he
    refine ⟨⟨(e, c), ?_⟩, rfl⟩
    rw [← hje]
    exact lPlusUpperLeftEdge_mem_prefix hτ hfin hk.le ⟨j, hj⟩
  obtain ⟨p, hp⟩ := hlift (i + 1) b hb true
  obtain ⟨q, hq⟩ := hlift i a ha false
  obtain ⟨m, hm, hmb, hgapT⟩ := lPlus_primed_upperLeft_boundary_gap
    (H := H) hτ hfin i a b ha hb
  obtain ⟨n, hn, hna, _⟩ := lPlus_prefix_upperLeft_boundary_gap
    (H := H) hτ hqMode hk i a b ha hb
  have hab : kmswLimitDartVertex w (a, false) = kmswLimitDartVertex w (b, true) :=
    (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) (a, false) (b, true)).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow] using hna⟩
  obtain ⟨t, ht, hret, hgapP⟩ := lPlusPrefixDartImage_firstReturn
    (H := H) hτ longest hqMode hk p
  change (kmswInfRot w (H.1 0) : _ → _)^[t] p.val =
      (lPlusPrefixStageDart hk (stageRot w (boundaryHitTime w h k - 1)
        (lPlusPrefixDartStage hk p))).val at hret
  change ∀ j : ℕ, 0 < j → j < t →
      (kmswInfRot w (H.1 0) : _ → _)^[j] p.val ∉
        Set.range (fun d : LPlusPrefixDart W h k => d.val) at hgapP
  rw [hp] at hret hgapP
  have hbound : t ≤ m := by
    by_contra hh
    exact hgapP m hm (by omega) ⟨q, hq.trans hmb.symm⟩
  refine ⟨p, hp, t, ht, hret, ?_⟩
  intro j hj hjt ⟨c, hc⟩
  cases c with
  | inl c => exact hgapP j hj hjt ⟨c, hc⟩
  | inr c =>
    cases c with
    | inl c => exact hgapT j hj (by omega) ⟨c, hc⟩
    | inr c =>
      have hv := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) (b, true)
        ((kmswInfRot w (H.1 0) : _ → _)^[j] (b, true))).mp
          ⟨j, by simp only [Equiv.Perm.coe_pow]⟩
      exact lPlus_upperLeft_west_not_hatted hτ i a ha c.val
        (hab.trans (hv.trans (congrArg (kmswLimitDartVertex w) hc.symm)))

/-- Helper toward Lemma 5.5: both ports at each interior upper-left
attachment vertex have their actual geometric left-side returns. The west
port uses the primed return and the east port uses the prefix return. -/
theorem lPlus_upperLeft_interior_side_returns
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge w (boundaryHitTime w h (j - 1))))}
    (hτ : HasFlowLineHits U) (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath w (boundaryPresentVertex w h k))
    (hfin : hatLimitFiniteIncidence U)
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 < k) (i a b : ℕ)
    (ha : ULedges[i]? = some a) (hb : ULedges[i + 1]? = some b) :
    let S := m0GeodesicSide hp P ThinMapSide.left
    let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin)
    (∃ p : ℕ × Bool, lMinusPrimedDartImage hτ p = (a, false) ∧
      S.rotation (a, false) (lMinusPrimedDartImage hτ (TR p))) ∧
    ∃ q : LPlusPrefixDart W h k, q.val = (b, true) ∧
      S.rotation (b, true)
        (lPlusPrefixStageDart hk (stageRot w (boundaryHitTime w h k - 1)
          (lPlusPrefixDartStage hk q))).val := by
  dsimp only
  let M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
  let F := lPlusBlockDartImage (M := M) hτ
  have hmem (d : ℕ × Bool) (hd : d.1 ∈ (m0GeodesicSide hp P .left).edges) :
      d ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk.le]
    exact hd
  constructor
  · obtain ⟨p, hp', t, ht, hret, hgap⟩ := lPlus_upperLeft_interior_west_firstReturn
      (H := H) hτ hqMode hfin hk i a b ha hb
    refine ⟨p, hp', t, ht, hret, ?_⟩
    intro j hj hjt hs
    exact hgap j hj hjt (hmem _ hs)
  · obtain ⟨q, hq', t, ht, hret, hgap⟩ := lPlus_upperLeft_interior_east_firstReturn
      (H := H) hτ hqMode hfin hk i a b ha hb
    refine ⟨q, hq', t, ht, hret, ?_⟩
    intro j hj hjt hs
    exact hgap j hj hjt (hmem _ hs)


























































end DirectedDistances.PaperProofs.Section5
