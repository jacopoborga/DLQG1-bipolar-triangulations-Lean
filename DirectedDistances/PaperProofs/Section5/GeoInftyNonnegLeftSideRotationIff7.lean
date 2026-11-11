/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff6

/-! Helper toward Lemma 5.5: left-data dependence of the terminal repair. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the next west dart of an old upper-left
attachment is allocated after the stopped stage. The triangle which consumes
the attachment fixes this next dart, even if the attachment is later missing
in the future presentation. -/
theorem lPlus_stage_upperLeft_west_successor_new (u : ℕ → Fin 3)
    (hu : BoundaryHitWitnesses u)
    (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
      ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite)
    (n e : ℕ) (he : e ∈ (kmswStage u n).UL.dropLast) :
    (kmswStage u n).nextEdge ≤ (kmswInfRot u hf (e, false)).1 := by
  have heUL := List.mem_of_mem_dropLast he
  have hout : (e, false) ∈ stageOuterWordVal u n := by
    rw [stageOuterWordVal_eq_runs]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨e, heUL, rfl⟩)))
  have heb := stage_face_dart_lt_nextEdge u n (e, false)
    (List.mem_append_left _ hout)
  have heact : e ≠ (kmswStage u n).active := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last u n
    have hnd := (kmswStageFrontierChain_all u n).UL_nodup
    rw [hes] at he hnd
    simp only [List.dropLast_concat] at he
    intro heq
    exact (List.nodup_append.mp hnd).2.2 e he _
      (List.mem_singleton_self _) heq
  have hnotact (j : ℕ) (hj : n ≤ j) : e ≠ (kmswStage u j).active := by
    intro heq
    rw [kmswStage_UL_eq] at heUL
    obtain ⟨m, hm, hme⟩ := List.mem_map.mp heUL
    have hmn := List.mem_range.mp (List.mem_filter.mp hm).1
    have hmj := CutConverse.act_injective u (hme.trans heq)
    have hnj : n = j := by omega
    exact heact (heq.trans (congrArg (fun t => (kmswStage u t).active) hnj.symm))
  have hL (a : ℤ) : ∃ m, L u m ≤ a := by
    obtain ⟨m, hm⟩ := hu.leftHit (min a (-1)) (by omega)
    exact ⟨m, by omega⟩
  have hR (a : ℤ) : ∃ m, R u m ≤ a := by
    obtain ⟨m, hm⟩ := hu.rightHit (max (-a) 1) (by omega)
    exact ⟨m, by omega⟩
  obtain hLL | hLR | ⟨j, hj, _⟩ := kmswRunInfDart_partition u hf hL hR (e, false)
  · obtain ⟨_, _, heq⟩ := hLL
    exact Bool.noConfusion (congrArg Prod.snd heq)
  · obtain ⟨_, _, heq⟩ := hLR
    exact Bool.noConfusion (congrArg Prod.snd heq)
  have hnj : n ≤ j.val := by
    by_contra hh
    have htri : (e, false) ∈ stageTriangleDartsVal u n :=
      List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes u n j).mpr (by omega), hj⟩
    exact List.disjoint_left.mp (stage_outer_triangle_disjoint u n) hout htri
  have hnew := kmswStage_nextEdge_mono u hnj
  have hna := hnotact j.val hnj
  have hc := kmswInfFaceSucc_stageTriangle_cycle u hf j
  by_cases h0 : u j.val = 0
  · cases hs : (kmswStage u j.val).UL.dropLast.reverse with
    | nil =>
      rw [stageTriangleDartList, stageTriangleDartTriple_left_fresh u j h0 hs] at hj
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq,
        Bool.false_eq_true, and_false, or_false, false_or, and_true] at hj
      rcases hj with heq | heq
      · exact (hna heq).elim
      · change e = (kmswStage u j.val).nextEdge + 1 at heq
        omega
    | cons a as =>
      rw [stageTriangleDartList, stageTriangleDartTriple_left_existing u j h0 a as hs] at hj
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq,
        Bool.false_eq_true, and_false, or_false, and_true] at hj
      rcases hj with hea | hea
      · rw [stageTriangleDartTriple_left_existing u j h0 a as hs] at hc
        have hface := hc.2.2.1
        change (kmswInfRot u hf).symm ((kmswStage u j.val).nextEdge, false) =
          (a, false) at hface
        have hr := congrArg (kmswInfRot u hf) hface
        rw [Equiv.apply_symm_apply] at hr
        rw [hea, ← hr]
        exact hnew
      · exact (hna hea).elim
  · have h1 : u j.val = 1 := j.property.resolve_left h0
    rw [stageTriangleDartList, stageTriangleDartTriple_up u j h1] at hj
    simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq,
      Bool.false_eq_true, and_false, or_false, and_true] at hj
    exact (hna hj).elim

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W} {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hk : 0 ≤ k)

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "F" => lPlusBlockDartImage (M := MH) hτ
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))

include H hfin in
/-- Helper toward Lemma 5.5: at every west attachment port, including the
terminal port, the ambient successor is a primed dart. -/
theorem lPlus_upperLeft_west_successor_mem_primed (i : Fin (ULedges).length) :
    kmswInfRot w (H.1 0) (ULedges[i.val], false) ∈
      Set.range (lMinusPrimedDartImage hτ) := by
  let a := ULedges[i.val]
  let d := kmswInfRot w (H.1 0) (a, false)
  have hnew := lPlus_stage_upperLeft_west_successor_new w h (H.1 0)
    (boundaryHitTime w h k) a (List.mem_reverse.mp (List.getElem_mem i.isLt))
  change (kmswStage w (boundaryHitTime w h k)).nextEdge ≤ d.1 at hnew
  have hfuture : d.1 ∈ Set.range (boundaryGluingEdgeMap W h k) := by
    have hall := (Set.ext_iff.mp (boundaryGluing_prefix_union_futureRange W h k) d.1).mpr
      (Set.mem_univ _)
    rcases hall with hpref | hfut
    · change d.1 < (kmswStage w (boundaryHitTime w h k)).nextEdge at hpref
      omega
    · exact hfut
  have hv : kmswLimitDartVertex w (a, false) = kmswLimitDartVertex w d :=
    (kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp ⟨1, by rw [pow_one]⟩
  have hprimed : d.1 ∈ boundaryGluingPrimedEdges W h k hτ := by
    have hc := (Set.ext_iff.mp
      (boundaryGluing_hatRange_union_primedEdges W h k hτ hfin) d.1).mpr hfuture
    rcases hc with ⟨e, he⟩ | hp
    · exact False.elim (lPlus_upperLeft_west_not_hatted hτ i.val a
        (List.getElem?_eq_getElem i.isLt) (e, d.2)
        (by simpa only [he] using hv))
    · exact hp
  obtain ⟨e, he⟩ := hprimed
  refine ⟨(e, d.2 ^^ primedLimitSideFlip U hτ e), ?_⟩
  apply Prod.ext he
  change ((d.2 ^^ primedLimitSideFlip U hτ e) ^^ primedLimitSideFlip U hτ e) = d.2
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

include H in
/-- Helper toward Lemma 5.5: every west upper-left port has a block-defined
code return, namely its extended primed rotation. This includes the terminal
port and uses no hatted right-side rotation. -/
theorem lPlusGluedCodeReturn_upperLeft_west (i : Fin (ULedges).length) :
    lPlusGluedCodeReturn (H := H) hτ hqMode
        (lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)) =
      lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)) := by
  let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
  let J := lPlusGluedCodeImageEquiv hτ hqMode
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  obtain ⟨p, hp, hclass⟩ := lPlusUpperLeftGluedDart_primed_representative
    hτ hqMode hfin hk i false
  have hnext := lPlus_upperLeft_west_successor_mem_primed (H := H) hτ hfin i
  obtain ⟨n, hn, hret, hgap⟩ := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin p
  have hTR : lMinusPrimedDartImage hτ (TR p) =
      kmswInfRot w (H.1 0) (ULedges[i.val], false) := by
    have hn1 : n = 1 := by
      by_contra hne
      apply hgap 1 (by omega) (by omega)
      simpa only [hp, Function.iterate_one] using hnext
    simpa only [hn1, hp, Function.iterate_one] using hret.symm
  have hmem : kmswInfRot w (H.1 0) (J d).val ∈ Set.range F := by
    change kmswInfRot w (H.1 0) (ULedges[i.val], false) ∈ Set.range F
    exact ⟨.inr (.inl (TR p)), hTR⟩
  have hr := subsetFirstReturn_eq_next (kmswInfRot w (H.1 0)) (Set.range F)
    (lPlusGluedCodeReturn_exists (H := H) hτ hqMode) (J d) hmem
  have hTE : lPlusPrimedExtendedRotation hτ hqMode hfin d = IT (TR p) := by
    rw [show d = IT p from hclass]
    exact TR.extendDomain_apply_image _ p
  rw [hTE]
  apply J.injective
  apply Subtype.ext
  change (J (J.symm _)).val = lMinusPrimedDartImage hτ (TR p)
  rw [J.apply_symm_apply]
  exact hr.trans hTR.symm

include H in
/-- Helper toward Lemma 5.5: the terminal code return is explicitly the
primed block's extended rotation at that same terminal port. -/
theorem lPlusGluedCodeReturn_terminal (hn : 0 < (ULedges).length) :
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    lPlusGluedCodeReturn (H := H) hτ hqMode t =
      lPlusPrimedExtendedRotation hτ hqMode hfin t := by
  dsimp only
  exact lPlusGluedCodeReturn_upperLeft_west (H := H) hτ hqMode hfin hk _

variable {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)

/-- Helper toward Lemma 5.5: the repaired permutation expressed using only
the prefix, primed and retained hatted block rotations and attachment ports.
The terminal output is computed by the primed block rotation. -/
@[expose] noncomputable def lPlusGluedBlockRotation2 : Equiv.Perm Q :=
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  if hn : 0 < (ULedges).length then
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    Equiv.swap (C t) (lPlusPrimedExtendedRotation hτ hqMode hfin t) * C
  else C

/-- Helper toward Lemma 5.5: the ambient-return repair equals the
permutation assembled from the three left blocks. This eliminates the ambient
rotation from the repair's terminal-output computation. -/
theorem lPlusGluedCorrectedRotation2_eq_blockRotation2 :
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk =
      lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft := by
  unfold lPlusGluedCorrectedRotation2 lPlusGluedBlockRotation2
  split_ifs with hn
  · dsimp only
    rw [lPlusGluedCodeReturn_upperLeft_west (H := H) hτ hqMode hfin hk]
  · rfl




































































end DirectedDistances.PaperProofs.Section5
