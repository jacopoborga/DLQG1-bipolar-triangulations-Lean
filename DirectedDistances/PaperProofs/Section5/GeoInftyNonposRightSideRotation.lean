/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSide

/-! Rotation transport for the nonpositive right side. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: a negative hit is a fresh-left step, with no
earlier vertex at the new source. -/
theorem rMinus_negative_hit_fresh (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {k : ℤ} (hk : k < 0) :
    ∃ m, boundaryHitTime w h k = m + 1 ∧ w m = 0 ∧
      (kmswStage w m).UL.dropLast.reverse = [] := by
  have ht : boundaryHitTime w h k = Nat.find (h.leftHit k (by omega)) := by
    simp only [boundaryHitTime, dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬0 < k)]
  have hmin (j : ℕ) (hj : j < boundaryHitTime w h k) : L w j ≠ k := by
    rw [ht] at hj
    exact Nat.find_min (h.leftHit k (by omega)) hj
  have hstrict (j : ℕ) : j < boundaryHitTime w h k → k < L w j := by
    induction j with
    | zero => simp only [L, Finset.sum_range_zero]; omega
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hs : L w (j + 1) = L w j + ((w j : ℤ) - 1) :=
        Finset.sum_range_succ _ _
      have hn := hmin (j + 1) hj
      have hb := (w j).isLt
      omega
  have hhit := boundaryHitTime_left_spec w h (by omega : k ≤ -1)
  have hpos : 0 < boundaryHitTime w h k := by
    by_contra hn
    have hz : boundaryHitTime w h k = 0 := by omega
    rw [hz] at hhit
    simp only [L, Finset.sum_range_zero] at hhit
    omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : boundaryHitTime w h k ≠ 0)
  change boundaryHitTime w h k = m + 1 at hm
  have hp := hstrict m (by omega)
  have hs : L w (m + 1) = L w m + ((w m : ℤ) - 1) :=
    Finset.sum_range_succ _ _
  rw [hm] at hhit
  have hc : w m = 0 := by
    apply Fin.ext
    have hb := (w m).isLt
    omega
  have hprev : L w m = k + 1 := by rw [hc] at hs; norm_num at hs; omega
  have hrecord : minL w m = L w m := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) m
    have hb := hstrict j (by omega)
    have hl := runningMin_le (L w) m m le_rfl
    change minL w m = L w j at he
    change minL w m ≤ L w m at hl
    omega
  refine ⟨m, hm, hc, ?_⟩
  apply List.length_eq_zero_iff.mp
  simp only [List.length_reverse, List.length_dropLast]
  have hlen := kmswStage_UL_length w m
  omega

private theorem rMinus_resize_val {a b : ℕ} (h : a = b)
    (σ : Equiv.Perm (StageDart a)) (e : ℕ) (he : e < a) (he' : e < b) (c : Bool) :
    ((StageRotation.resize h σ (⟨e, he'⟩, c)).1.val,
      (StageRotation.resize h σ (⟨e, he'⟩, c)).2) =
      ((σ (⟨e, he⟩, c)).1.val, (σ (⟨e, he⟩, c)).2) := by
  cases h
  rfl

/-- Helper toward Lemma 5.5: the prefix successor at its negative-hit
initial shared dart is the west dart of the newly created missing edge. -/
theorem rMinus_negative_prefix_initial_rotation (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k < 0) :
    let n := boundaryHitTime w h k
    let d : StageDart (kmswStage w n).nextEdge :=
      (⟨act w n, act_lt_nextEdge w le_rfl⟩, false)
    ((stageRot w n d).1.val, (stageRot w n d).2) =
      (kmswLLCreatedEdge w n, false) := by
  obtain ⟨m, hm, hc, hl⟩ := rMinus_negative_hit_fresh w h hk
  dsimp only
  rw [hm]
  let s := kmswStage w m
  have hc' : kmswCodeStep (w m) = .left := by rw [hc]; rfl
  have hsize : (kmswStage w (m + 1)).nextEdge = s.nextEdge + 2 := by
    simp only [kmswStage, kmswStep, hc', kmswStepOfStep, hl, State.addEdge]
    rfl
  have hid : kmswLLCreatedEdge w (m + 1) = s.nextEdge + 1 := by
    simp only [kmswLLCreatedEdge, hsize]; omega
  have hact : act w (m + 1) = s.nextEdge := by
    simp only [act, kmswStage, kmswStep, hc', kmswStepOfStep, hl]
    rfl
  let σ := stageRot w m
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w le_rfl⟩, false)
  let A : StageDart s.nextEdge := (a.1, true)
  have hu : StageRotation.resize hsize (stageRot w (m + 1)) =
      StageRotation.leftFresh s.nextEdge σ a A :=
    StageRotation.step_leftFresh s a.1.isLt (stageRotation_UL_bound w m) σ (w m) hc' hl
  have hh := congrArg (fun d : StageDart (s.nextEdge + 2) => (d.1.val, d.2))
    (StageRotation.leftFresh_new s.nextEdge σ a A).2.2.1
  rw [← hu] at hh
  simp only [StageRotation.allocation_new] at hh
  rw [rMinus_resize_val (he := by rw [hsize]; omega)] at hh
  simpa only [hact, hid, Fin.val_zero, Fin.val_one, Nat.add_zero] using hh

/-- Helper toward Lemma 5.5: the fresh missing edge is allocated but is
neither the active edge nor an edge of the shared upper-right segment. -/
theorem rMinus_negative_missing_properties (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k < 0) :
    let n := boundaryHitTime w h k
    kmswLLCreatedEdge w n < (kmswStage w n).nextEdge ∧
      kmswLLCreatedEdge w n ≠ act w n ∧
      kmswLLCreatedEdge w n ∉ (kmswStage w n).active :: (kmswStage w n).UR := by
  obtain ⟨m, hm, hc, hl⟩ := rMinus_negative_hit_fresh w h hk
  dsimp only
  rw [hm]
  have hc' : kmswCodeStep (w m) = .left := by rw [hc]; rfl
  have hs : kmswStage w (m + 1) = kmswStepOfStep (kmswStage w m) .left := by
    change kmswStep (kmswStage w m) (w m) = _
    rw [kmswStep, hc']
  simp only [kmswLLCreatedEdge, act, hs, kmswStepOfStep, hl, State.addEdge,
    Nat.add_sub_cancel, List.mem_cons, not_or]
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro he
  have hb := (kmswStage_boundary_ids_lt_nextEdge w m).2 _
    (show (kmswStage w m).nextEdge + 1 ∈
        (kmswStage w m).UL ++ (kmswStage w m).UR ++
          (kmswStage w m).LL ++ (kmswStage w m).LR from by
      simp only [List.mem_append]; tauto)
  omega

/-- Helper toward Lemma 5.5: the missing prefix dart returns to the
initial shared dart in the finite prefix rotation. -/
theorem rMinus_negative_prefix_missing_rotation (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k < 0) :
    let n := boundaryHitTime w h k
    let d : StageDart (kmswStage w n).nextEdge :=
      (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hk).1⟩, false)
    ((stageRot w n d).1.val, (stageRot w n d).2) = (act w n, false) := by
  obtain ⟨m, hm, hc, hl⟩ := rMinus_negative_hit_fresh w h hk
  dsimp only
  generalize_proofs hbound
  revert hbound
  rw [hm]
  intro hbound
  let s := kmswStage w m
  have hc' : kmswCodeStep (w m) = .left := by rw [hc]; rfl
  have hsize : (kmswStage w (m + 1)).nextEdge = s.nextEdge + 2 := by
    simp only [kmswStage, kmswStep, hc', kmswStepOfStep, hl, State.addEdge]
    rfl
  have hid : kmswLLCreatedEdge w (m + 1) = s.nextEdge + 1 := by
    simp only [kmswLLCreatedEdge, hsize]; omega
  have hact : act w (m + 1) = s.nextEdge := by
    simp only [act, kmswStage, kmswStep, hc', kmswStepOfStep, hl]
    rfl
  let σ := stageRot w m
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w le_rfl⟩, false)
  let A : StageDart s.nextEdge := (a.1, true)
  have hu : StageRotation.resize hsize (stageRot w (m + 1)) =
      StageRotation.leftFresh s.nextEdge σ a A :=
    StageRotation.step_leftFresh s a.1.isLt (stageRotation_UL_bound w m) σ (w m) hc' hl
  have hh := congrArg (fun d : StageDart (s.nextEdge + 2) => (d.1.val, d.2))
    (StageRotation.leftFresh_new s.nextEdge σ a A).2.2.2
  rw [← hu] at hh
  simp only [StageRotation.allocation_new] at hh
  rw [rMinus_resize_val (he := by rw [hsize]; omega)] at hh
  simpa only [hact, hid, Fin.val_zero, Fin.val_one, Nat.add_zero] using hh

section InitialGeometry

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "w" => shiftedStream W 0
local notation "n" => boundaryHitTime (shiftedStream W 0) h k
local notation "F" => kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
local notation "q" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right q
local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "D" => rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the actual initial geometric successor at
a negative index. A nontrivial hatted source star is traversed first; when
that star is a singleton, the successor is the missing prefix boundary dart. -/
theorem rMinus_negative_initial_side_rotation_cases (hneg : k < 0) :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
    let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
    (S).rotation (act w n, false)
      (if Hrot c = c then (kmswLLCreatedEdge w n, false)
       else (EH (Hrot c).val.1, (Hrot c).val.2)) := by
  dsimp only
  let σ := kmswInfRot w (H.1 0)
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let a : ℕ × Bool := (act w n, false)
  let b : ℕ × Bool := (kmswLLCreatedEdge w n, false)
  have hca : J c = a :=
    (rMinusPrefixDartImage_boundary hτ hqMode 0 _ (by rfl) false).symm
  have hinj : Function.Injective J := by
    intro d e he
    change (EH d.val.1, d.val.2) = (EH e.val.1, e.val.2) at he
    apply Subtype.ext
    have hb := congrArg (fun z : ℕ × Bool => z.2) he
    have he' := congrArg (fun z : ℕ × Bool => z.1) he
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ he') hb
  have hba : b ≠ a := by
    intro he
    exact (rMinus_negative_missing_properties w h hneg).2.1 (congrArg Prod.fst he)
  have hσ : σ b = a := by
    have he := boundaryHit_negative_source_predecessor w h (H.1 0) k (by omega)
    exact (σ.symm_apply_eq.mp he).symm
  obtain ⟨p, hp0, hpe, hpgap⟩ := rMinusPrefixDartImage_firstReturn (H := H)
    (h := h) (k := k) (⟨act w n, act_lt_nextEdge w le_rfl⟩, false)
  change (σ : _ → _)^[p] a =
    ((stageRot w n (⟨act w n, act_lt_nextEdge w le_rfl⟩, false)).1.val,
      (stageRot w n (⟨act w n, act_lt_nextEdge w le_rfl⟩, false)).2) at hpe
  rw [rMinus_negative_prefix_initial_rotation w h hneg] at hpe
  change (σ : _ → _)^[p] a = b at hpe
  change ∀ j : ℕ, 0 < j → j < p → (σ : _ → _)^[j] a ∉
    Set.range (rMinusPrefixDartImage (h := h) (k := k)) at hpgap
  obtain ⟨t, ht, hte, htgap⟩ :=
    rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin c
  change (σ : _ → _)^[t] (J c) = J (Hrot c) at hte
  change ∀ j : ℕ, 0 < j → j < t → (σ : _ → _)^[j] (J c) ∉ Set.range J at htgap
  rw [hca] at hte htgap
  have haP : a ∈ Set.range (rMinusPrefixDartImage (h := h) (k := k)) :=
    ⟨(⟨act w n, act_lt_nextEdge w le_rfl⟩, false), rfl⟩
  have haH : a ∈ Set.range J := ⟨c, hca⟩
  have hnext : (σ : _ → _)^[p + 1] a = a := by
    rw [Function.iterate_succ_apply', hpe, hσ]
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix]
    have hta : (σ : _ → _)^[t] a = a := by rw [hfix, hca] at hte; exact hte
    have hpt : p < t := by
      by_contra hn
      rcases lt_or_eq_of_le (by omega : t ≤ p) with hlt | heq
      · exact hpgap t ht hlt (hta.symm ▸ haP)
      · exact hba ((heq ▸ hta).symm.trans hpe).symm
    refine ⟨p, hp0, hpe, ?_⟩
    intro j hj hjp hm
    rcases (Set.ext_iff.mp
      (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm with hP | hH
    · exact hpgap j hj hjp hP
    · exact htgap j hj (by omega) hH
  · rw [ite_eq_right hfix]
    have htp : t ≤ p := by
      by_contra hn
      have hle : p + 1 ≤ t := by omega
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact htgap (p + 1) (by omega) hlt (hnext.symm ▸ haH)
      · exact hfix (hinj (hca.trans (hnext.symm.trans (heq ▸ hte)))).symm
    refine ⟨t, ht, hte, ?_⟩
    intro j hj hjt hm
    rcases (Set.ext_iff.mp
      (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm with hP | hH
    · exact hpgap j hj (by omega) hP
    · exact htgap j hj hjt hH

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the newly created missing prefix dart
does not belong to the retained hatted block. -/
theorem rMinus_negative_missing_not_hatted (hneg : k < 0) :
    let b : StageDart (F).nextEdge :=
      (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
    rMinusCodePrefixDart F Q b ∉ Set.range (rMinusCodeHattedDart F Q) := by
  dsimp only
  rintro ⟨d, hd⟩
  have he := congrArg (fun z => (D z).val) hd
  rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix] at he
  have hv : kmswLLCreatedEdge w n = EH d.val.1 := (congrArg Prod.fst he).symm
  obtain ⟨i, hi, _⟩ := (rMinus_cross_edge_eq_iff hτ hqMode hfin
    ⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩
    ⟨d.val.1, d.property⟩).mp hv
  exact (rMinus_negative_missing_properties w h hneg).2.2
    (List.mem_iff_getElem?.mpr ⟨i, hi⟩)

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the original splice always sends its initial
shared dart to the missing prefix dart at a negative hit. -/
theorem rMinusCodeSpliceRotation_negative_initial (hneg : k < 0) :
    let i : Fin ((F).active :: (F).UR).length := ⟨0, by simp only [List.length_cons]; omega⟩
    let b : StageDart (F).nextEdge :=
      (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
    rMinusCodeSpliceRotation w n q (rMinusCodeBoundaryDart w n Q (i, false)) =
      rMinusCodePrefixDart F Q b := by
  dsimp only
  let i : Fin ((F).active :: (F).UR).length := ⟨0, by simp only [List.length_cons]; omega⟩
  let b : StageDart (F).nextEdge :=
    (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
  let y := rMinusCodePrefixDart F Q b
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  have hrot : stageRot w n (rMinusPrefixBoundaryDart w n (i, false)) = b := by
    have he := rMinus_negative_prefix_initial_rotation w h hneg
    dsimp only at he
    have hb := congrArg (fun z : ℕ × Bool => z.2) he
    have he' := congrArg (fun z : ℕ × Bool => z.1) he
    exact Prod.ext (Fin.ext he') hb
  have hP : (stageRot w n).extendDomain Pemb (rMinusCodeBoundaryDart w n Q (i, false)) = y := by
    rw [rMinusCodeBoundaryDart_eq_prefix]
    exact ((stageRot w n).extendDomain_apply_image Pemb _).trans
      (congrArg (rMinusCodePrefixDart F Q) hrot)
  have hnH : y ∉ Set.range (rMinusCodeHattedDart F Q) :=
    rMinus_negative_missing_not_hatted hτ hp P hqMode Tpath hfin hleft hk hneg
  have hnC : y ∉ Set.range (rMinusCodeBoundaryDart w n Q) := by
    rintro ⟨⟨j, c⟩, hj⟩
    apply hnH
    rw [← hj, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩
  change Hrot.extendDomain Hemb
    ((rMinusBoundaryCornerPerm _).extendDomain Cemb
      ((stageRot w n).extendDomain Pemb (rMinusCodeBoundaryDart w n Q (i, false)))) = y
  rw [hP, Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hnC,
    Equiv.Perm.extendDomain_apply_not_subtype _ Hemb hnH]

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the original candidate is geometrically
correct at the negative initial dart exactly when the hatted initial dart
is fixed. In particular, a nonfixed hatted star is an exact obstruction. -/
theorem rMinusCodeSpliceRotation_negative_initial_side_rotation_iff (hneg : k < 0) :
    let i : Fin ((F).active :: (F).UR).length := ⟨0, by simp only [List.length_cons]; omega⟩
    let d := rMinusCodeBoundaryDart w n Q (i, false)
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
    (S).rotation (D d).val (D (rMinusCodeSpliceRotation w n q d)).val ↔
      rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q c = c := by
  dsimp only
  rw [rMinusCodeSpliceRotation_negative_initial hτ hp P hqMode Tpath hfin hleft hk hneg,
    rMinusCodeBoundaryDart_eq_prefix,
    rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_prefix]
  change (S).rotation (act w n, false) (kmswLLCreatedEdge w n, false) ↔ _
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  have hr := rMinus_negative_initial_side_rotation_cases hτ hp P hqMode Tpath hfin hleft hk hneg
  dsimp only at hr
  by_cases hfix : Hrot c = c
  · rw [ite_eq_left hfix] at hr
    exact iff_of_true hr hfix
  · rw [ite_eq_right hfix] at hr
    refine iff_of_false ?_ hfix
    intro hb
    obtain ⟨t, ht, hte, hgap⟩ := hr
    obtain ⟨p, hp0, hpe, hpgap⟩ := hb
    have hmem : (EH (Hrot c).val.1, (Hrot c).val.2).1 ∈ (S).edges := by
      rw [← rMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk (Hrot c)]
      exact (D (rMinusCodeHattedDart F Q (Hrot c))).property
    have hmemb : kmswLLCreatedEdge w n ∈ (S).edges := by
      have hm := (D (rMinusCodePrefixDart F Q
        (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false))).property
      rw [rMinusCodeGluedDartEquiv_prefix] at hm
      exact hm
    have htp : t = p := by
      apply Nat.le_antisymm
      · by_contra hn
        exact hgap p hp0 (by omega) (hpe.symm ▸ hmemb)
      · by_contra hn
        exact hpgap t ht (by omega) (hte.symm ▸ hmem)
    have he : (EH (Hrot c).val.1, (Hrot c).val.2) =
        (kmswLLCreatedEdge w n, false) := hte.symm.trans (htp ▸ hpe)
    apply rMinus_negative_missing_not_hatted hτ hp P hqMode Tpath hfin hleft hk hneg
    refine ⟨Hrot c, ?_⟩
    apply (D).injective
    apply Subtype.ext
    rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix]
    exact he

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a nonfixed hatted initial successor cannot
lie in the prefix block. This follows from the actual geometric first return,
not from a source-star or cyclic-separation assumption. -/
theorem rMinus_negative_initial_hatted_successor_not_prefix (hneg : k < 0) :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
    let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
    Hrot c ≠ c → rMinusCodeHattedDart F Q (Hrot c) ∉
      Set.range (rMinusCodePrefixDart F Q) := by
  dsimp only
  intro hne
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  rintro ⟨a, ha⟩
  have hea := congrArg (fun z => (D z).val) ha
  rw [rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_hatted] at hea
  have hr := rMinus_negative_initial_side_rotation_cases hτ hp P hqMode Tpath hfin hleft hk hneg
  dsimp only at hr
  rw [ite_eq_right hne] at hr
  obtain ⟨t, ht, hte, hgap⟩ := hr
  obtain ⟨p, hp0, hpe, hpgap⟩ := rMinusPrefixDartImage_firstReturn (H := H)
    (h := h) (k := k) (⟨act w n, act_lt_nextEdge w le_rfl⟩, false)
  change (kmswInfRot w (H.1 0) : _ → _)^[p] (act w n, false) =
    ((stageRot w n (⟨act w n, act_lt_nextEdge w le_rfl⟩, false)).1.val,
      (stageRot w n (⟨act w n, act_lt_nextEdge w le_rfl⟩, false)).2) at hpe
  rw [rMinus_negative_prefix_initial_rotation w h hneg] at hpe
  have hbmem : kmswLLCreatedEdge w n ∈ (S).edges := by
    have hm := (D (rMinusCodePrefixDart F Q
      (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false))).property
    rw [rMinusCodeGluedDartEquiv_prefix] at hm
    exact hm
  have htp : t = p := by
    apply Nat.le_antisymm
    · by_contra hn
      exact hgap p hp0 (by omega) (hpe.symm ▸ hbmem)
    · by_contra hn
      apply hpgap t ht (by omega)
      exact ⟨a, hea.trans hte.symm⟩
  have he := hte.symm.trans (htp ▸ hpe)
  apply rMinus_negative_missing_not_hatted hτ hp P hqMode Tpath hfin hleft hk hneg
  refine ⟨Hrot c, ?_⟩
  apply (D).injective
  apply Subtype.ext
  rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix]
  exact he

end InitialGeometry

/-- Helper toward Lemma 5.5: conjugate the original candidate by the
transposition of the initial shared dart and its prefix successor. This
is an intrinsic, code-only permutation; its initial successor is certified
below. No whole-side certification is asserted by this definition. -/
@[expose] noncomputable def rMinusCodeInitialAdjustedRotation (w : ℕ → Fin 3) (n : ℕ)
    {x : XDP} (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    Equiv.Perm (RMinusCodeGluedDart (kmswStage w n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :=
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  let i : Fin ((kmswStage w n).active :: (kmswStage w n).UR).length :=
    ⟨0, by simp only [List.length_cons]; omega⟩
  let a := rMinusCodeBoundaryDart w n M (i, false)
  let b := rMinusCodePrefixDart (kmswStage w n) M
    (stageRot w n (rMinusPrefixBoundaryDart w n (i, false)))
  Equiv.swap a b * rMinusCodeSpliceRotation w n q * Equiv.swap a b

/-- Helper toward Lemma 5.5: the local initial adjustment is the identity
adjustment at stage zero, on every dart. -/
theorem rMinusCodeInitialAdjustedRotation_zero (w : ℕ → Fin 3)
    {x : XDP} (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    rMinusCodeInitialAdjustedRotation w 0 q = rMinusCodeSpliceRotation w 0 q := by
  unfold rMinusCodeInitialAdjustedRotation
  dsimp only
  rw [stageRot_zero]
  have heq : rMinusCodePrefixDart (kmswStage w 0)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
      (rMinusPrefixBoundaryDart w 0 (⟨0, by change 0 < 1; omega⟩, false)) =
      rMinusCodeBoundaryDart w 0
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (⟨0, by change 0 < 1; omega⟩, false) := rfl
  change Equiv.swap _ (rMinusCodePrefixDart _ _ (rMinusPrefixBoundaryDart w 0 _)) * _ *
    Equiv.swap _ (rMinusCodePrefixDart _ _ (rMinusPrefixBoundaryDart w 0 _)) = _
  rw [heq, Equiv.swap_self]
  rfl

section InitialAdjustedGeometry

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "w" => shiftedStream W 0
local notation "n" => boundaryHitTime (shiftedStream W 0) h k
local notation "F" => kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
local notation "q" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right q
local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "D" => rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the original candidate sends the missing
prefix dart to the hatted successor of the initial shared dart. -/
theorem rMinusCodeSpliceRotation_negative_missing (hneg : k < 0) :
    let b : StageDart (F).nextEdge :=
      (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
    rMinusCodeSpliceRotation w n q (rMinusCodePrefixDart F Q b) =
      rMinusCodeHattedDart F Q
        (rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q c) := by
  dsimp only
  let i : Fin ((F).active :: (F).UR).length := ⟨0, by simp only [List.length_cons]; omega⟩
  let d := rMinusCodeBoundaryDart w n Q (i, false)
  let b : StageDart (F).nextEdge :=
    (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  have hrot : stageRot w n b = rMinusPrefixBoundaryDart w n (i, false) := by
    have he := rMinus_negative_prefix_missing_rotation w h hneg
    dsimp only at he
    have hb := congrArg (fun z : ℕ × Bool => z.2) he
    have he' := congrArg (fun z : ℕ × Bool => z.1) he
    exact Prod.ext (Fin.ext he') hb
  have hP : (stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q b) = d := by
    have hh := (stageRot w n).extendDomain_apply_image Pemb b
    change (stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q b) =
      rMinusCodePrefixDart F Q (stageRot w n b) at hh
    rw [hrot] at hh
    exact hh
  have hC : (rMinusBoundaryCornerPerm _).extendDomain Cemb d = d := by
    have hh := (rMinusBoundaryCornerPerm _).extendDomain_apply_image Cemb (i, false)
    change (rMinusBoundaryCornerPerm _).extendDomain Cemb d = d at hh
    exact hh
  change Hrot.extendDomain Hemb ((rMinusBoundaryCornerPerm _).extendDomain Cemb
    ((stageRot w n).extendDomain Pemb (rMinusCodePrefixDart F Q b))) = _
  rw [hP, hC]
  have hd : d = rMinusCodeHattedDart F Q c :=
    rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk i false
  rw [hd]
  exact Hrot.extendDomain_apply_image Hemb c




theorem rMinusCodeInitialAdjustedRotation_initial_side_rotation :
    let i : Fin ((F).active :: (F).UR).length := ⟨0, by simp only [List.length_cons]; omega⟩
    let d := rMinusCodeBoundaryDart w n Q (i, false)
    (S).rotation (D d).val (D (rMinusCodeInitialAdjustedRotation w n q d)).val := by
  dsimp only
  let i : Fin ((F).active :: (F).UR).length := ⟨0, by simp only [List.length_cons]; omega⟩
  let d := rMinusCodeBoundaryDart w n Q (i, false)
  by_cases hk0 : k = 0
  · have ht : n = 0 := by rw [hk0, boundaryHitTime_zero]
    have heq : rMinusCodeInitialAdjustedRotation w n q = rMinusCodeSpliceRotation w n q := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [heq]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation hτ hp P hqMode Tpath hfin hleft hk hk0 d
  have hneg : k < 0 := by omega
  let b : StageDart (F).nextEdge :=
    (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
  let m := rMinusCodePrefixDart F Q b
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  have hrot : stageRot w n (rMinusPrefixBoundaryDart w n (i, false)) = b := by
    have he := rMinus_negative_prefix_initial_rotation w h hneg
    dsimp only at he
    have hb := congrArg (fun z : ℕ × Bool => z.2) he
    have he' := congrArg (fun z : ℕ × Bool => z.1) he
    exact Prod.ext (Fin.ext he') hb
  have heval : rMinusCodeInitialAdjustedRotation w n q d =
      Equiv.swap d m (rMinusCodeHattedDart F Q (Hrot c)) := by
    change Equiv.swap d
      (rMinusCodePrefixDart F Q (stageRot w n (rMinusPrefixBoundaryDart w n (i, false))))
      (rMinusCodeSpliceRotation w n q
        (Equiv.swap d
          (rMinusCodePrefixDart F Q (stageRot w n (rMinusPrefixBoundaryDart w n (i, false)))) d)) = _
    rw [hrot, Equiv.swap_apply_left]
    rw [rMinusCodeSpliceRotation_negative_missing hτ hp P hqMode Tpath hfin hleft hk hneg]
  have hd : rMinusCodeHattedDart F Q c = d :=
    (rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk i false).symm
  have hstart : (D d).val = (act w n, false) := by
    dsimp only [d]
    rw [rMinusCodeBoundaryDart_eq_prefix, rMinusCodeGluedDartEquiv_prefix]
    rfl
  rw [heval, hstart]
  have hr := rMinus_negative_initial_side_rotation_cases hτ hp P hqMode Tpath hfin hleft hk hneg
  dsimp only at hr
  by_cases hfix : Hrot c = c
  · rw [hfix, hd, Equiv.swap_apply_left, rMinusCodeGluedDartEquiv_prefix]
    rw [ite_eq_left hfix] at hr
    exact hr
  · have hnd : rMinusCodeHattedDart F Q (Hrot c) ≠ d := by
      intro he
      apply hfix
      exact rMinusCodeHattedDart_injective w n q (he.trans hd.symm)
    have hnm : rMinusCodeHattedDart F Q (Hrot c) ≠ m := by
      intro he
      exact rMinus_negative_missing_not_hatted hτ hp P hqMode Tpath hfin hleft hk hneg ⟨Hrot c, he⟩
    rw [Equiv.swap_apply_of_ne_of_ne hnd hnm, rMinusCodeGluedDartEquiv_hatted]
    rw [ite_eq_right hfix] at hr
    exact hr

end InitialAdjustedGeometry






















































end DirectedDistances.PaperProofs.Section5
