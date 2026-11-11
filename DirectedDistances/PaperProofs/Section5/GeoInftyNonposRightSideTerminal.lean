/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideRotation

/-! Terminal and endpoint rotation transport for the nonpositive right side. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: a dart already outside the finite outer face
keeps its immediate rotation successor in the infinite map. -/
theorem rMinusInfRot_of_not_outer (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge)
    (hd : d ∉ stageOuterWord w n) :
    kmswInfRot w hfin (d.1.val, d.2) =
      ((stageRot w n d).1.val, (stageRot w n d).2) := by
  obtain ⟨j, ⟨hjn, hdj⟩, _⟩ := (stage_dart_partition w n d).resolve_left hd
  have hstable (m : ℕ) (hnm : n ≤ m) :
      let D := outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d
      ((stageRot w m D).1.val, (stageRot w m D).2) =
        ((stageRot w n d).1.val, (stageRot w n d).2) := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      let D := outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d
      have hnot : D ∉ stageOuterWord w m :=
        stageTriangleDart_not_outer w m j (by omega) D hdj
      have he := congrArg (fun e => (e.1.val, e.2))
        (stageRot_castDart_of_not_outer w m (stageOuterWord_faceSucc w m) D hnot)
      exact he.trans ih
  obtain ⟨N, hN⟩ := kmswInfRot_eventually_eq_stage w hfin (d.1.val, d.2)
  obtain ⟨_, he⟩ := hN (max n N) (le_max_right _ _)
  exact he.trans (hstable (max n N) (le_max_left _ _))

/-- Helper toward Lemma 5.5: every reverse shared dart at a negative
boundary hit is already off the finite outer face. -/
theorem rMinus_negative_shared_reverse_not_outer (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k < 0)
    (i : Fin ((kmswStage w (boundaryHitTime w h k)).active ::
      (kmswStage w (boundaryHitTime w h k)).UR).length) :
    rMinusPrefixBoundaryDart w (boundaryHitTime w h k) (i, true) ∉
      stageOuterWord w (boundaryHitTime w h k) := by
  let n := boundaryHitTime w h k
  let F := kmswStage w n
  let e := (F.active :: F.UR)[i.val]
  have he : e ∈ F.active :: F.UR := List.getElem_mem i.isLt
  have hb : e < F.nextEdge := (rMinusPrefixBoundaryDart w n (i, true)).1.isLt
  have hnot : e ∉ F.LR ∧ e ∉ F.LL := by
    rcases List.mem_cons.mp he with ha | hu
    · have hp : F.present e = true := by
        rw [ha]
        exact (kmswStage_status w n).2.1 _ (by
          obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
          rw [hxs]
          exact List.mem_append_right _ (List.mem_singleton_self _))
      refine ⟨?_, fun hl => Bool.false_ne_true
        (((kmswStage_status w n).1 e hb).mpr (Or.inr hl) |>.symm.trans hp)⟩
      obtain ⟨m, hm, hc, hl⟩ := rMinus_negative_hit_fresh w h hk
      have hcode : kmswCodeStep (w m) = .left := by rw [hc]; rfl
      have hact : F.active = (kmswStage w m).nextEdge := by
        simp only [F, n, hm, kmswStage, kmswStep, hcode, kmswStepOfStep, hl]
      have hlr : F.LR = (kmswStage w m).LR := by
        simp only [F, n, hm, kmswStage, kmswStep, hcode, kmswStepOfStep, hl,
          State.addEdge]
      intro heLR
      rw [ha, hact, hlr] at heLR
      have hlt := (kmswStage_boundary_ids_lt_nextEdge w m).2 _
        (List.mem_append_right _ heLR)
      exact Nat.lt_irrefl _ hlt
    · have hp : F.present e = false :=
        ((kmswStage_status w n).1 e hb).mpr (Or.inl hu)
      exact ⟨fun hl => Bool.false_ne_true
        (hp.symm.trans ((kmswStage_status w n).2.2.1 e hl)),
        (kmswStage_status w n).2.2.2.2.2 e hu⟩
  intro ho
  have hm := (stageOuterWord_mem_iff w n _).mp ho
  rcases hm with ⟨hf, _⟩ | ⟨_, hl | hl⟩
  · exact Bool.noConfusion hf
  · exact hnot.1 hl
  · exact hnot.2 hl

/-- Helper toward Lemma 5.5: the fresh initial vertex has exactly the
new active and new missing prefix darts. Old prefix edges have older endpoints. -/
theorem rMinus_negative_initial_prefix_star (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k < 0)
    (d : StageDart (kmswStage w (boundaryHitTime w h k)).nextEdge)
    (hv : stageEndpoint (kmswStage w (boundaryHitTime w h k)) d =
      (kmswStage w (boundaryHitTime w h k)).west (act w (boundaryHitTime w h k))) :
    (d.1.val, d.2) = (act w (boundaryHitTime w h k), false) ∨
      (d.1.val, d.2) = (kmswLLCreatedEdge w (boundaryHitTime w h k), false) := by
  obtain ⟨m, hm, hc, hl⟩ := rMinus_negative_hit_fresh w h hk
  have hcode : kmswCodeStep (w m) = .left := by rw [hc]; rfl
  let s := kmswStage w m
  change s.UL.dropLast.reverse = [] at hl
  have hstage : kmswStage w (boundaryHitTime w h k) =
      kmswStepOfStep s .left := by
    rw [hm]
    change kmswStep s (w m) = _
    rw [kmswStep, hcode]
  have hsize : (kmswStage w (boundaryHitTime w h k)).nextEdge = s.nextEdge + 2 := by
    simp only [hstage, kmswStepOfStep, hl, State.addEdge]
  have hact : act w (boundaryHitTime w h k) = s.nextEdge := by
    simp only [act, hstage, kmswStepOfStep, hl]
  have hmiss : kmswLLCreatedEdge w (boundaryHitTime w h k) = s.nextEdge + 1 := by
    simp only [kmswLLCreatedEdge, hsize]
    omega
  have hw : (kmswStage w (boundaryHitTime w h k)).west (act w (boundaryHitTime w h k)) =
      s.nextVertex := by
    simp only [hact, hstage, kmswStepOfStep, hl, State.addEdge, ↓reduceIte,
      show s.nextEdge ≠ s.nextEdge + 1 by omega]
  rw [hw] at hv
  have hd : d.1.val < s.nextEdge + 2 := d.1.isLt.trans_eq hsize
  have hactive := kmswStage_endpoints_lt_nextVertex w m s.active
    (act_lt_nextEdge w le_rfl)
  by_cases hnew : d.1.val = s.nextEdge
  · left
    rw [hact]
    refine Prod.ext hnew ?_
    cases hb : d.2 with
    | false => rfl
    | true =>
      have hh : s.east s.active = s.nextVertex := by
        simpa only [stageEndpoint, hb, hstage, kmswStepOfStep, hl, State.addEdge,
          hnew, ↓reduceIte, show s.nextEdge ≠ s.nextEdge + 1 by omega] using hv
      exact (Nat.ne_of_lt hactive.2 hh).elim
  by_cases hnew' : d.1.val = s.nextEdge + 1
  · right
    rw [hmiss]
    refine Prod.ext hnew' ?_
    cases hb : d.2 with
    | false => rfl
    | true =>
      have hh : s.west s.active = s.nextVertex := by
        simpa only [stageEndpoint, hb, hstage, kmswStepOfStep, hl, State.addEdge,
          hnew', ↓reduceIte] using hv
      exact (Nat.ne_of_lt hactive.1 hh).elim
  have hold : d.1.val < s.nextEdge := by omega
  have hbnd := kmswStage_endpoints_lt_nextVertex w m d.1.val hold
  have hv' : (if d.2 then s.east d.1.val else s.west d.1.val) = s.nextVertex := by
    simpa only [stageEndpoint, hstage, kmswStepOfStep, hl, State.addEdge,
      hnew, hnew', ↓reduceIte] using hv
  cases hb : d.2 with
  | false => exact (Nat.ne_of_lt hbnd.1 (by simpa only [hb, Bool.false_eq_true,
      ↓reduceIte] using hv')).elim
  | true => exact (Nat.ne_of_lt hbnd.2 (by simpa only [hb, ↓reduceIte] using hv')).elim

section TerminalGeometry

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
local notation "N" => List.length (State.active (kmswStage (shiftedStream W 0)
  (boundaryHitTime (shiftedStream W 0) h k)) ::
  State.UR (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)))
local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "D" => rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hfin in
/-- Helper toward Lemma 5.5: hatted boundary edges beyond the shared
segment are not allocated prefix edges. -/
theorem rMinus_hatted_boundary_after_prefix (j : ℕ) (hj : N ≤ j) :
    EH (((Q).boundary j).1) ∉ boundaryGluingPrefixEdges W h k := by
  intro he
  obtain ⟨i, hi, hij⟩ := (rMinus_cross_edge_eq_iff hτ hqMode hfin
    ⟨_, he⟩ ⟨((Q).boundary j).1, rMinus_hatted_boundary_mem _ q j⟩).mp rfl
  have heq := rMinus_hatted_boundary_edge_injective _ q hij
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  omega

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the terminal prefix successor at a negative
hit lies strictly in the prefix block. -/
theorem rMinus_terminal_prefix_successor_not_hatted (hneg : k < 0) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    let d := rMinusPrefixBoundaryDart w n (i, true)
    rMinusCodePrefixDart F Q (stageRot w n d) ∉
      Set.range (rMinusCodeHattedDart F Q) := by
  dsimp only
  let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
  let d := rMinusPrefixBoundaryDart w n (i, true)
  let σ := kmswInfRot w (H.1 0)
  let c : {a : ℕ × Bool // a.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩
  let J : {a : ℕ × Bool // a.1 ∈ (Q).edges} → ℕ × Bool :=
    fun a => (EH a.val.1, a.val.2)
  have hstart : (d.1.val, d.2) = J c :=
    rMinusPrefixDartImage_boundary hτ hqMode i.val _
      (List.getElem?_eq_getElem i.isLt) true
  have hσ : σ (d.1.val, d.2) = ((stageRot w n d).1.val, (stageRot w n d).2) :=
    rMinusInfRot_of_not_outer w (H.1 0) n d
      (rMinus_negative_shared_reverse_not_outer w h hneg i)
  rintro ⟨a, ha⟩
  have hv := congrArg (fun z => (D z).val) ha
  rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix] at hv
  obtain ⟨t, ht, hte, hgap⟩ :=
    rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin c
  change (σ : _ → _)^[t] (J c) = J (rMinusHattedRotation _ q c) at hte
  change ∀ j : ℕ, 0 < j → j < t →
    (σ : _ → _)^[j] (J c) ∉ Set.range J at hgap
  have ht1 : t = 1 := by
    by_contra hn
    apply hgap 1 (by omega) (by omega)
    refine ⟨a, ?_⟩
    simpa only [Function.iterate_one, ← hstart, hσ] using hv
  rw [ht1, Function.iterate_one] at hte
  change σ (J c) = J
    (rMinusHattedRotation _ q
      ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ q i.val⟩) at hte
  rw [rMinusHattedRotation_boundary_corner hqMode i.val] at hte
  have he : EH (((Q).boundary (i.val + 1)).1) = (stageRot w n d).1.val :=
    congrArg Prod.fst (hte.symm.trans (hstart ▸ hσ))
  apply rMinus_hatted_boundary_after_prefix hτ hqMode hfin (i.val + 1) (by
    dsimp only [i]
    simp only [List.length_cons]
    omega)
  rw [he]
  exact (stageRot w n d).1.isLt

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the original terminal splice returns the
literal prefix successor at a negative hit. -/
theorem rMinusCodeSpliceRotation_negative_terminal (hneg : k < 0) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    rMinusCodeSpliceRotation w n q (rMinusCodeBoundaryDart w n Q (i, true)) =
      rMinusCodePrefixDart F Q
        (stageRot w n (rMinusPrefixBoundaryDart w n (i, true))) := by
  dsimp only
  let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
  let y := rMinusCodePrefixDart F Q
    (stageRot w n (rMinusPrefixBoundaryDart w n (i, true)))
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  have hyH : y ∉ Set.range (rMinusCodeHattedDart F Q) :=
    rMinus_terminal_prefix_successor_not_hatted hτ hp P hqMode Tpath hfin hleft hk hneg
  have hyC : y ∉ Set.range (rMinusCodeBoundaryDart w n Q) := by
    rintro ⟨⟨j, b⟩, hj⟩
    apply hyH
    rw [← hj, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩
  have hP : (stageRot w n).extendDomain Pemb
      (rMinusCodeBoundaryDart w n Q (i, true)) = y :=
    (stageRot w n).extendDomain_apply_image Pemb _
  change (rMinusHattedRotation _ q).extendDomain Hemb
    ((rMinusBoundaryCornerPerm N).extendDomain Cemb
      ((stageRot w n).extendDomain Pemb (rMinusCodeBoundaryDart w n Q (i, true)))) = y
  rw [hP, Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hyC,
    Equiv.Perm.extendDomain_apply_not_subtype _ Hemb hyH]

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: conjugation at the initial port fixes the
terminal successor at a negative hit, including both edge ID and bit. -/
theorem rMinusCodeInitialAdjustedRotation_negative_terminal (hneg : k < 0) :
    let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
    rMinusCodeInitialAdjustedRotation w n q (rMinusCodeBoundaryDart w n Q (i, true)) =
      rMinusCodePrefixDart F Q
        (stageRot w n (rMinusPrefixBoundaryDart w n (i, true))) := by
  dsimp only
  let i : Fin N := ⟨N - 1, by simp only [List.length_cons]; omega⟩
  let i₀ : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
  let d := rMinusCodeBoundaryDart w n Q (i, true)
  let a := rMinusCodeBoundaryDart w n Q (i₀, false)
  let b := rMinusCodePrefixDart F Q
    (stageRot w n (rMinusPrefixBoundaryDart w n (i₀, false)))
  let y := rMinusCodePrefixDart F Q
    (stageRot w n (rMinusPrefixBoundaryDart w n (i, true)))
  have hda : d ≠ a := by
    intro he
    have hh := congrArg Prod.snd he
    exact Bool.noConfusion hh
  have hdb : d ≠ b := by
    have he := rMinus_negative_prefix_initial_rotation w h hneg
    dsimp only at he
    intro heq
    have hh := congrArg Prod.snd heq
    change true = (stageRot w n (rMinusPrefixBoundaryDart w n (i₀, false))).2 at hh
    have hb := congrArg Prod.snd he
    exact Bool.noConfusion (hh.trans hb)
  have hya : y ≠ a := by
    have hyH := rMinus_terminal_prefix_successor_not_hatted
      hτ hp P hqMode Tpath hfin hleft hk hneg
    intro he
    apply hyH
    rw [show rMinusCodePrefixDart F Q
      (stageRot w n (rMinusPrefixBoundaryDart w n (i, true))) = a from he]
    dsimp only [a]
    rw [rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩
  have hyb : y ≠ b := by
    intro he
    have hh := (stageRot w n).injective (rMinusCodePrefixDart_injective w n q he)
    exact Bool.noConfusion (congrArg Prod.snd hh)
  change Equiv.swap a b (rMinusCodeSpliceRotation w n q (Equiv.swap a b d)) = y
  rw [Equiv.swap_apply_of_ne_of_ne hda hdb,
    rMinusCodeSpliceRotation_negative_terminal hτ hp P hqMode Tpath hfin hleft hk hneg,
    Equiv.swap_apply_of_ne_of_ne hya hyb]

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the adjusted candidate returns the newly
created missing initial dart directly to the initial shared dart. -/
theorem rMinusCodeInitialAdjustedRotation_negative_missing (hneg : k < 0) :
    let i : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
    let b : StageDart (F).nextEdge :=
      (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
    rMinusCodeInitialAdjustedRotation w n q (rMinusCodePrefixDart F Q b) =
      rMinusCodeBoundaryDart w n Q (i, false) := by
  dsimp only
  let i : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
  let b : StageDart (F).nextEdge :=
    (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
  have hrot : stageRot w n (rMinusPrefixBoundaryDart w n (i, false)) = b := by
    have he := rMinus_negative_prefix_initial_rotation w h hneg
    dsimp only at he
    have he' := congrArg (fun z : ℕ × Bool => z.1) he
    have hb := congrArg (fun z : ℕ × Bool => z.2) he
    exact Prod.ext (Fin.ext he') hb
  change Equiv.swap _
    (rMinusCodePrefixDart F Q (stageRot w n (rMinusPrefixBoundaryDart w n (i, false))))
    (rMinusCodeSpliceRotation w n q
      (Equiv.swap _
        (rMinusCodePrefixDart F Q (stageRot w n (rMinusPrefixBoundaryDart w n (i, false))))
        (rMinusCodePrefixDart F Q b))) = _
  rw [hrot, Equiv.swap_apply_right,
    rMinusCodeSpliceRotation_negative_initial hτ hp P hqMode Tpath hfin hleft hk hneg,
    Equiv.swap_apply_right]

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the remaining missing initial prefix dart
has its actual geometric successor under the adjusted candidate. -/
theorem rMinusCodeInitialAdjustedRotation_missing_side_rotation (hneg : k < 0) :
    let b : StageDart (F).nextEdge :=
      (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
    (S).rotation (D (rMinusCodePrefixDart F Q b)).val
      (D (rMinusCodeInitialAdjustedRotation w n q (rMinusCodePrefixDart F Q b))).val := by
  dsimp only
  rw [rMinusCodeInitialAdjustedRotation_negative_missing
    hτ hp P hqMode Tpath hfin hleft hk hneg,
    rMinusCodeBoundaryDart_eq_prefix, rMinusCodeGluedDartEquiv_prefix,
    rMinusCodeGluedDartEquiv_prefix]
  have he := boundaryHit_negative_source_predecessor w h (H.1 0) k (by omega)
  have hr := ((kmswInfRot w (H.1 0)).symm_apply_eq.mp he).symm
  exact ⟨1, Nat.zero_lt_one, hr, fun j hj hj1 _ => by omega⟩

include h in
/-- Helper toward Lemma 5.5: a geometric prefix dart at the fresh initial
vertex is one of its two literal prefix darts. -/
theorem rMinus_negative_initial_prefix_image_star (hneg : k < 0)
    (a : ℕ × Bool)
    (ha : a ∈ Set.range (rMinusPrefixDartImage (h := h) (k := k)))
    (hv : kmswLimitDartVertex w a = (F).west (act w n)) :
    a = (act w n, false) ∨ a = (kmswLLCreatedEdge w n, false) := by
  obtain ⟨d, rfl⟩ := ha
  have he := edge_endpoints_eq w d.1.isLt
  have hd : stageEndpoint F d = (F).west (act w n) := by
    change (if d.2 then (F).east d.1.val else (F).west d.1.val) = _
    change (if d.2 then edgeEast w d.1.val else edgeWest w d.1.val) = _ at hv
    simpa only [he.1, he.2] using hv
  exact rMinus_negative_initial_prefix_star w h hneg d hd

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the actual return from any hatted
initial-star dart inserts the missing prefix dart just before the shared port. -/
theorem rMinus_initial_hatted_side_rotation_cases (hneg : k < 0)
    (a : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex w (EH a.val.1, a.val.2) = (F).west (act w n)) :
    let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
    let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
    (S).rotation (EH a.val.1, a.val.2)
      (if Hrot a = c then (kmswLLCreatedEdge w n, false)
       else (EH (Hrot a).val.1, (Hrot a).val.2)) := by
  dsimp only
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  let σ := kmswInfRot w (H.1 0)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let x := J a
  let A : ℕ × Bool := (act w n, false)
  let b : ℕ × Bool := (kmswLLCreatedEdge w n, false)
  have hJA : J c = A :=
    (rMinusPrefixDartImage_boundary hτ hqMode 0 _ (by rfl) false).symm
  have hJ : Function.Injective J := by
    intro d e he
    have hs := congrArg (fun z : ℕ × Bool => z.2) he
    have ht := congrArg (fun z : ℕ × Bool => z.1) he
    apply Subtype.ext
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ ht) hs
  have hσb : σ b = A := by
    have he := boundaryHit_negative_source_predecessor w h (H.1 0) k (by omega)
    exact ((kmswInfRot w (H.1 0)).symm_apply_eq.mp he).symm
  have hbH : b ∉ Set.range J := by
    rintro ⟨d, hd⟩
    apply rMinus_negative_missing_not_hatted hτ hp P hqMode Tpath hfin hleft hk hneg
    refine ⟨d, ?_⟩
    apply (D).injective
    apply Subtype.ext
    rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix]
    exact hd
  have hvertex (j : ℕ) : kmswLimitDartVertex w ((σ : _ → _)^[j] x) =
      (F).west (act w n) := by
    induction j with
    | zero => exact hv
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (kmswLimitDartVertex_rot w (H.1 0) _).trans ih
  obtain ⟨t, ht, hte, hgap⟩ :=
    rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin a
  change (σ : _ → _)^[t] x = J (Hrot a) at hte
  change ∀ j : ℕ, 0 < j → j < t → (σ : _ → _)^[j] x ∉ Set.range J at hgap
  have hstep (j : ℕ) (he : (σ : _ → _)^[j] x = b) :
      (σ : _ → _)^[j + 1] x = A := by rw [Function.iterate_succ_apply', he, hσb]
  have hnoj (j : ℕ) (hj : 0 < j) (hjt : j < t) : (σ : _ → _)^[j] x ≠ A := by
    intro he
    apply hgap j hj hjt
    exact ⟨c, hJA.trans he.symm⟩
  by_cases hnext : Hrot a = c
  · rw [ite_eq_left hnext]
    have htA : (σ : _ → _)^[t] x = A := by rw [hte, hnext, hJA]
    have hprev : (σ : _ → _)^[t - 1] x = b := by
      apply σ.injective
      rw [hσb]
      have he : (σ : _ → _)^[t - 1 + 1] x = A := by
        simpa only [Nat.sub_add_cancel ht] using htA
      rw [Function.iterate_succ_apply'] at he
      exact he
    have ht2 : 1 < t := by
      by_contra hn
      have ht1 : t = 1 := by omega
      rw [ht1, Nat.sub_self, Function.iterate_zero_apply] at hprev
      exact hbH ⟨a, hprev⟩
    refine ⟨t - 1, by omega, hprev, ?_⟩
    intro j hj hjt hm
    rcases (Set.ext_iff.mp (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm with hpref | hh
    · rcases rMinus_negative_initial_prefix_image_star hneg _ hpref (hvertex j) with ha | hb
      · exact hnoj j hj (by omega) ha
      · exact hnoj (j + 1) (by omega) (by omega) (hstep j hb)
    · exact hgap j hj (by omega) hh
  · rw [ite_eq_right hnext]
    refine ⟨t, ht, hte, ?_⟩
    intro j hj hjt hm
    rcases (Set.ext_iff.mp (rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk) _).mp hm with hpref | hh
    · rcases rMinus_negative_initial_prefix_image_star hneg _ hpref (hvertex j) with ha | hb
      · exact hnoj j hj hjt ha
      · have hs := hstep j hb
        rcases lt_or_eq_of_le (by omega : j + 1 ≤ t) with hlt | heq
        · exact hnoj (j + 1) (by omega) hlt hs
        · apply hnext
          apply hJ
          exact hte.symm.trans ((heq ▸ hs).trans hJA.symm)
    · exact hgap j hj hjt hh

include hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every hatted dart in the initial star has
the adjusted geometric successor, with no star separation premise. -/
theorem rMinusCodeInitialAdjustedRotation_initial_hatted_star_side_rotation (hneg : k < 0)
    (a : {d : ℕ × Bool // d.1 ∈ (Q).edges})
    (hv : kmswLimitDartVertex w (EH a.val.1, a.val.2) = (F).west (act w n)) :
    (S).rotation (D (rMinusCodeHattedDart F Q a)).val
      (D (rMinusCodeInitialAdjustedRotation w n q (rMinusCodeHattedDart F Q a))).val := by
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), rMinus_hatted_boundary_mem _ q 0⟩
  let i : Fin N := ⟨0, by simp only [List.length_cons]; omega⟩
  let A := rMinusCodeBoundaryDart w n Q (i, false)
  let b : StageDart (F).nextEdge :=
    (⟨kmswLLCreatedEdge w n, (rMinus_negative_missing_properties w h hneg).1⟩, false)
  let B := rMinusCodePrefixDart F Q b
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  have hAc : A = rMinusCodeHattedDart F Q c :=
    rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk i false
  by_cases hac : a = c
  · rw [hac, ← hAc]
    exact rMinusCodeInitialAdjustedRotation_initial_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk
  have hnotB : B ∉ Set.range (rMinusCodeHattedDart F Q) :=
    rMinus_negative_missing_not_hatted hτ hp P hqMode Tpath hfin hleft hk hneg
  have hnotP : rMinusCodeHattedDart F Q a ∉ Set.range (rMinusCodePrefixDart F Q) := by
    rintro ⟨p, hp⟩
    have he := congrArg (fun z => (D z).val) hp
    rw [rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_hatted] at he
    have hmem : J a ∈ Set.range (rMinusPrefixDartImage (h := h) (k := k)) :=
      ⟨p, he⟩
    rcases rMinus_negative_initial_prefix_image_star hneg (J a) hmem hv with hA | hB
    · apply hac
      apply Subtype.ext
      have hc := (rMinusPrefixDartImage_boundary hτ hqMode 0 _ (by rfl) false).symm
      have hh : J a = J c := hA.trans hc.symm
      have hs := congrArg (fun z : ℕ × Bool => z.2) hh
      have ht := congrArg (fun z : ℕ × Bool => z.1) hh
      exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ ht) hs
    · apply hnotB
      refine ⟨a, ?_⟩
      apply (D).injective
      apply Subtype.ext
      rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix]
      exact hB
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective w n q)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart w n Q)
    (rMinusCodeBoundaryDart_injective w n q)
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective w n q)
  have hnotC : rMinusCodeHattedDart F Q a ∉ Set.range (rMinusCodeBoundaryDart w n Q) := by
    rintro ⟨d, hd⟩
    exact hnotP ⟨rMinusPrefixBoundaryDart w n d, hd⟩
  have hsplice : rMinusCodeSpliceRotation w n q (rMinusCodeHattedDart F Q a) =
      rMinusCodeHattedDart F Q (Hrot a) := by
    change Hrot.extendDomain Hemb ((rMinusBoundaryCornerPerm N).extendDomain Cemb
      ((stageRot w n).extendDomain Pemb (rMinusCodeHattedDart F Q a))) = _
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ Pemb hnotP,
      Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hnotC]
    exact Hrot.extendDomain_apply_image Hemb a
  have hrot : stageRot w n (rMinusPrefixBoundaryDart w n (i, false)) = b := by
    have he := rMinus_negative_prefix_initial_rotation w h hneg
    dsimp only at he
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) he))
      (congrArg (fun z : ℕ × Bool => z.2) he)
  have hneA : rMinusCodeHattedDart F Q a ≠ A := by
    intro he
    exact hac (rMinusCodeHattedDart_injective w n q (he.trans hAc))
  have hneB (d : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
      rMinusCodeHattedDart F Q d ≠ B := fun he => hnotB ⟨d, he⟩
  have heval : rMinusCodeInitialAdjustedRotation w n q (rMinusCodeHattedDart F Q a) =
      Equiv.swap A B (rMinusCodeHattedDart F Q (Hrot a)) := by
    change Equiv.swap A
      (rMinusCodePrefixDart F Q (stageRot w n (rMinusPrefixBoundaryDart w n (i, false))))
      (rMinusCodeSpliceRotation w n q
        (Equiv.swap A
          (rMinusCodePrefixDart F Q (stageRot w n (rMinusPrefixBoundaryDart w n (i, false))))
          (rMinusCodeHattedDart F Q a))) = _
    rw [hrot, Equiv.swap_apply_of_ne_of_ne hneA (hneB a), hsplice]
  rw [heval, rMinusCodeGluedDartEquiv_hatted]
  have hr := rMinus_initial_hatted_side_rotation_cases
    hτ hp P hqMode Tpath hfin hleft hk hneg a hv
  dsimp only at hr
  by_cases hnext : Hrot a = c
  · rw [hnext, ← hAc, Equiv.swap_apply_left, rMinusCodeGluedDartEquiv_prefix]
    rw [ite_eq_left hnext] at hr
    exact hr
  · have hnextA : rMinusCodeHattedDart F Q (Hrot a) ≠ A := by
      intro he
      exact hnext (rMinusCodeHattedDart_injective w n q (he.trans hAc))
    rw [Equiv.swap_apply_of_ne_of_ne hnextA (hneB (Hrot a)),
      rMinusCodeGluedDartEquiv_hatted]
    rw [ite_eq_right hnext] at hr
    exact hr

end TerminalGeometry

/-- Helper toward Lemma 5.5: all prefix darts in the initial star have
the adjusted geometric successor; the source-star classification is proved. -/
theorem rMinusCodeInitialAdjustedRotation_initial_prefix_star_side_rotation
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
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
    (d : StageDart (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).nextEdge)
    (hv : stageEndpoint (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)) d =
      (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)).west
        (act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k))) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime .right q
    let n := boundaryHitTime (shiftedStream W 0) h k
    let F := kmswStage (shiftedStream W 0) n
    let D := rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
    (m0GeodesicSide hp P .right).rotation (D (rMinusCodePrefixDart F M d)).val
      (D (rMinusCodeInitialAdjustedRotation (shiftedStream W 0) n q
        (rMinusCodePrefixDart F M d))).val := by
  dsimp only
  by_cases hk0 : k = 0
  · have ht : boundaryHitTime (shiftedStream W 0) h k = 0 := by
      rw [hk0, boundaryHitTime_zero]
    have heq : rMinusCodeInitialAdjustedRotation (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)
        ⟨boundaryFutureHattedPath k W, hqMode⟩ =
        rMinusCodeSpliceRotation (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h k)
          ⟨boundaryFutureHattedPath k W, hqMode⟩ := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [heq]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 _
  have hneg : k < 0 := by omega
  rcases rMinus_negative_initial_prefix_star (shiftedStream W 0) h hneg d hv with ha | hb
  · have hd : d = rMinusPrefixBoundaryDart (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)
        (⟨0, by simp only [List.length_cons]; omega⟩, false) :=
      Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) ha))
        (congrArg (fun z : ℕ × Bool => z.2) ha)
    rw [hd]
    exact rMinusCodeInitialAdjustedRotation_initial_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk
  · have hd : d = (⟨kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k),
        (rMinus_negative_missing_properties (shiftedStream W 0) h hneg).1⟩, false) :=
      Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) hb))
        (congrArg (fun z : ℕ × Bool => z.2) hb)
    rw [hd]
    exact rMinusCodeInitialAdjustedRotation_missing_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hneg

/-- Helper toward Lemma 5.5: the adjusted permutation has the actual
terminal successor for every nonpositive boundary index. -/
theorem rMinusCodeInitialAdjustedRotation_terminal_side_rotation
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime .right q
    let n := boundaryHitTime (shiftedStream W 0) h k
    let F := kmswStage (shiftedStream W 0) n
    let i : Fin (F.active :: F.UR).length :=
      ⟨(F.active :: F.UR).length - 1, by simp only [List.length_cons]; omega⟩
    let d := rMinusCodeBoundaryDart (shiftedStream W 0) n M (i, true)
    (m0GeodesicSide hp P .right).rotation
      (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val
      (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
        (rMinusCodeInitialAdjustedRotation (shiftedStream W 0) n q d)).val := by
  dsimp only
  let w := shiftedStream W 0
  let n := boundaryHitTime w h k
  let F := kmswStage w n
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime .right q
  let i : Fin (F.active :: F.UR).length :=
    ⟨(F.active :: F.UR).length - 1, by simp only [List.length_cons]; omega⟩
  let d := rMinusCodeBoundaryDart w n M (i, true)
  let D := rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  change (m0GeodesicSide hp P .right).rotation
    (D d).val (D (rMinusCodeInitialAdjustedRotation w n q d)).val
  by_cases hk0 : k = 0
  · have ht : n = 0 := by dsimp only [n]; rw [hk0, boundaryHitTime_zero]
    have he : rMinusCodeInitialAdjustedRotation w n q =
        rMinusCodeSpliceRotation w n q := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [he]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 d
  have hneg : k < 0 := by omega
  rw [rMinusCodeInitialAdjustedRotation_negative_terminal
    hτ hp P hqMode Tpath hfin hleft hk hneg]
  dsimp only [d, D]
  rw [rMinusCodeBoundaryDart_eq_prefix,
    rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_prefix]
  let p := rMinusPrefixBoundaryDart w n (i, true)
  have he := rMinusInfRot_of_not_outer w (H.1 0) n p
    (rMinus_negative_shared_reverse_not_outer w h hneg i)
  exact ⟨1, Nat.zero_lt_one, he, fun j hj hj1 _ => by omega⟩

/-- Helper toward Lemma 5.5: every intrinsic dart at the initial endpoint
has the adjusted geometric successor, including both retained blocks. -/
theorem rMinusCodeInitialAdjustedRotation_initial_star_side_rotation
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime .right q
    let n := boundaryHitTime (shiftedStream W 0) h k
    let F := kmswStage (shiftedStream W 0) n
    let D := rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
    ∀ d : RMinusCodeGluedDart F M,
      kmswLimitDartVertex (shiftedStream W 0) (D d).val =
        F.west (act (shiftedStream W 0) n) →
      (m0GeodesicSide hp P .right).rotation (D d).val
        (D (rMinusCodeInitialAdjustedRotation (shiftedStream W 0) n q d)).val := by
  dsimp only
  intro d hv
  let w := shiftedStream W 0
  let n := boundaryHitTime w h k
  let F := kmswStage w n
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime .right q
  let D := rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  by_cases hk0 : k = 0
  · have ht : n = 0 := by dsimp only [n]; rw [hk0, boundaryHitTime_zero]
    have he : rMinusCodeInitialAdjustedRotation w n q =
        rMinusCodeSpliceRotation w n q := by
      rw [ht, rMinusCodeInitialAdjustedRotation_zero]
    rw [he]
    exact rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 d
  have hneg : k < 0 := by omega
  have hm : (D d).val ∈ {a : ℕ × Bool | a.1 ∈ (m0GeodesicSide hp P .right).edges} :=
    (D d).property
  rw [rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk] at hm
  rcases hm with ⟨p, hpval⟩ | ⟨a, haval⟩
  · have hpd : rMinusCodePrefixDart F M p = d := by
      apply D.injective
      apply Subtype.ext
      rw [rMinusCodeGluedDartEquiv_prefix]
      exact hpval
    have he := edge_endpoints_eq w p.1.isLt
    have hpv : stageEndpoint F p = F.west (act w n) := by
      have hh := (congrArg (kmswLimitDartVertex w) hpval).trans hv
      change (if p.2 then edgeEast w p.1.val else edgeWest w p.1.val) = _ at hh
      change (if p.2 then F.east p.1.val else F.west p.1.val) = _
      have hew : F.west p.1.val = edgeWest w p.1.val := he.1
      have hee : F.east p.1.val = edgeEast w p.1.val := he.2
      simpa only [hew, hee] using hh
    rw [← hpd]
    exact rMinusCodeInitialAdjustedRotation_initial_prefix_star_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk p hpv
  · have had : rMinusCodeHattedDart F M a = d := by
      apply D.injective
      apply Subtype.ext
      rw [rMinusCodeGluedDartEquiv_hatted]
      exact haval
    have hav : kmswLimitDartVertex w
        (boundaryGluingHatEdgeMap W h k hτ a.val.1, a.val.2) = F.west (act w n) :=
      (congrArg (kmswLimitDartVertex w) haval).trans hv
    rw [← had]
    exact rMinusCodeInitialAdjustedRotation_initial_hatted_star_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hneg a hav



















































end DirectedDistances.PaperProofs.Section5
