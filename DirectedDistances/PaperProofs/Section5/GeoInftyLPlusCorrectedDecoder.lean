/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso12

/-! Formalization-internal decoder correction, not a manuscript change.
The terminal cap is assembled from the finite prefix rotation and the
three-block permutation. No actual-side rotation enters the construction.
The general terminal-star comparison remains a proof obligation below;
this file makes no paper-completion claim. -/

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
local notation "C" => lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
local notation "PE" => lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
local notation "UL" => lPlusUpperLeftGluedDart hτ hqMode hfin hk
local notation "w" => shiftedStream W 0
local notation "es" => List.reverse (List.dropLast
  (State.UL (kmswStage w (boundaryHitTime w h k))))

/-- Helper toward Lemma 5.5: every fresh-left triangle fixes the
lower-left successor, both in the ambient rotation and at every later
finite stage. This allows the fresh-left event at an arbitrary time. -/
theorem lPlus_fresh_left_lowerLeft_rotations (u : ℕ → Fin 3)
    (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
      ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite)
    (n m : ℕ) (hnm : n < m) (hc : u n = 0)
    (hUL : (kmswStage u n).UL.dropLast.reverse = []) :
    kmswInfRot u hf ((kmswStage u n).nextEdge + 1, false) =
        ((kmswStage u n).nextEdge, false) ∧
      ∃ ha : (kmswStage u n).nextEdge < (kmswStage u m).nextEdge,
      ∃ hb : (kmswStage u n).nextEdge + 1 < (kmswStage u m).nextEdge,
        stageRot u m (⟨(kmswStage u n).nextEdge + 1, hb⟩, false) =
          (⟨(kmswStage u n).nextEdge, ha⟩, false) := by
  let j : TriangleCreationTime u := ⟨n, Or.inl hc⟩
  have ht := stageTriangleDartTriple_left_fresh u j hc hUL
  have hi := (kmswInfFaceSucc_stageTriangle_cycle u hf j).2.1
  rw [ht] at hi
  change (kmswInfRot u hf).symm ((kmswStage u n).nextEdge, false) =
    ((kmswStage u n).nextEdge + 1, false) at hi
  have hsize : (kmswStage u (n + 1)).nextEdge = (kmswStage u n).nextEdge + 2 := by
    simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hUL, State.addEdge]
  have hmono := kmswStage_nextEdge_mono u (show n + 1 ≤ m by omega)
  have ha : (kmswStage u n).nextEdge < (kmswStage u m).nextEdge := by omega
  have hb : (kmswStage u n).nextEdge + 1 < (kmswStage u m).nextEdge := by omega
  have hs := (stageTriangle_isFace u j m (by exact hnm)).2.1
  simp only [stageTriangleDart₂, stageTriangleDart₃, stageTriangleDartAt, ht] at hs
  change (stageRot u m).symm (⟨(kmswStage u n).nextEdge, ha⟩, false) =
    (⟨(kmswStage u n).nextEdge + 1, hb⟩, false) at hs
  exact ⟨((kmswInfRot u hf).symm_apply_eq.mp hi).symm,
    ha, hb, ((stageRot u m).symm_apply_eq.mp hs).symm⟩

/-- Helper toward Lemma 5.5: the terminal cap exchanges the attachment
dart with its finite-prefix successor after the block rotation. The same
formula applies to every nonempty attachment; the empty attachment is
unchanged. Both exchanged darts are determined by the prefix code. -/
@[expose] noncomputable def lPlusGluedCorrectedRotation4 : Equiv.Perm Q :=
  if hn : 0 < (es).length then
    let t := UL (⟨(es).length - 1, by omega⟩, false)
    Equiv.swap t (PE t) *
      lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft
  else lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft

/-- Helper toward Lemma 5.5: the terminal-cap construction is a
permutation, including when the two selected darts coincide. -/
theorem lPlusGluedCorrectedRotation4_bijective :
    Function.Bijective
      (lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk) :=
  (lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk).bijective

/-- Helper toward Lemma 5.5: evaluate the terminal correction against
rotation 2. No rotation-transport premise is used. -/
theorem lPlusGluedCorrectedRotation4_apply (hn : 0 < (es).length) (d : Q) :
    let t := UL (⟨(es).length - 1, by omega⟩, false)
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d =
      Equiv.swap t (PE t) (C d) := by
  rw [lPlusGluedCorrectedRotation4, dite_eq_left hn,
    ← lPlusGluedCorrectedRotation2_eq_blockRotation2 hτ hqMode hfin hk hp P Tpath hleft]
  rfl

/-- Helper toward Lemma 5.5: the empty attachment requires no terminal
correction. -/
theorem lPlusGluedCorrectedRotation4_eq_rotation2_of_empty
    (hn : ¬ 0 < (es).length) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk = C := by
  rw [lPlusGluedCorrectedRotation4, dite_eq_right hn,
    ← lPlusGluedCorrectedRotation2_eq_blockRotation2 hτ hqMode hfin hk hp P Tpath hleft]

/-- Helper toward Lemma 5.5: only outputs equal to one of the two
code-selected terminal darts can change. -/
theorem lPlusGluedCorrectedRotation4_eq_rotation2_of_ne
    (hn : 0 < (es).length) (d : Q)
    (ht : C d ≠ UL (⟨(es).length - 1, by omega⟩, false))
    (hpref : C d ≠ PE (UL (⟨(es).length - 1, by omega⟩, false))) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = C d := by
  rw [lPlusGluedCorrectedRotation4_apply hτ hp P hqMode Tpath hfin hleft hk hn d]
  exact Equiv.swap_apply_of_ne_of_ne ht hpref

/-- Helper toward Lemma 5.5: the extended finite-prefix permutation
preserves the ambient vertex of every quotient dart. -/
theorem lPlusPrefixExtendedRotation_vertex (d : Q) :
    kmswLimitDartVertex w (D (PE d)).val = kmswLimitDartVertex w (D d).val := by
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  by_cases hd : d ∈ Set.range IP
  · obtain ⟨p, rfl⟩ := hd
    have he : PE (IP p) = IP (PR p) := PR.extendDomain_apply_image _ p
    rw [he]
    change kmswLimitDartVertex w (PR p).val = kmswLimitDartVertex w p.val
    have hkpos := lPlus_prefix_dart_pos hk p
    rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos]
    obtain ⟨n, _, hend, _⟩ := lPlusPrefixDartImage_firstReturn
      (H := H) hτ longest hqMode hkpos p
    exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow, lPlusBlockDartImage] using hend⟩).symm
  · have he : PE d = d := Equiv.Perm.extendDomain_apply_not_subtype _ _ hd
    rw [he]

/-- Helper toward Lemma 5.5: away from the terminal vertex, all cases of
rotation 2 reduce to the already proved root, interior and beta cases. -/
theorem lPlusGluedCorrectedRotation2_rotation_iff_of_ne_terminal
    (hn : 0 < (es).length) (d e : Q)
    (hd : kmswLimitDartVertex w (D d).val ≠
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    C d = e ↔ (S).rotation (D d).val (D e).val := by
  by_cases hUL : ∃ f : ℕ, f ∈ boundaryGluingUpperLeftEdges W h k ∧
      (kmswLimitDartVertex w (f, false) = kmswLimitDartVertex w (D d).val ∨
        kmswLimitDartVertex w (f, true) = kmswLimitDartVertex w (D d).val)
  · obtain ⟨f, hf, hvertex⟩ := hUL
    have hf' : f ∈ es := List.mem_reverse.mpr hf
    obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem hf'
    let i : Fin (es).length := ⟨j, hj⟩
    rcases hvertex with hv | hv
    · by_cases hi : j + 1 < (es).length
      · exact lPlusGluedCorrectedRotation2_upperLeft_vertex_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk d i hi (by simpa only [i, hfj] using hv.symm) e
      · have hjlast : j = (es).length - 1 := by omega
        exact (hd (hv.symm.trans (congrArg (fun f => kmswLimitDartVertex w (f, false))
          (by simpa only [hjlast] using hfj.symm)))).elim
    · cases j with
      | zero =>
        have hroot : kmswLimitDartVertex w (D d).val = boundaryVertex w h k := by
          obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hn)
          have hstart := lPlusPrefixUpperLeftDarts_first_starts_at_xk (W := W) (h := h) has
          have hfa : f = a := by simpa only [has, List.getElem_cons_zero] using hfj.symm
          exact hv.symm.trans (hfa ▸ hstart)
        exact lPlusGluedCorrectedRotation2_initial_vertex_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk d hroot e
      | succ j =>
        have hj₀ : j < (es).length := by omega
        obtain ⟨n, _, _, _, hend, _⟩ := lPlus_upperLeft_rotation_separation
          (H := H) hτ hqMode hfin
          (lPlus_upperLeft_nonempty_pos (W := W) (h := h) hk hn)
          j (es[j]) (es[j + 1])
          (List.getElem?_eq_getElem hj₀) (List.getElem?_eq_getElem hj)
        have hv' := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
          (es[j], false) (es[j + 1], true)).mp
            ⟨n, by simpa only [Equiv.Perm.coe_pow] using hend⟩
        apply lPlusGluedCorrectedRotation2_upperLeft_vertex_rotation_iff
          hτ hp P hqMode Tpath hfin hleft hk d ⟨j, hj₀⟩ hj _ e
        exact hv.symm.trans ((congrArg (fun f => kmswLimitDartVertex w (f, true))
          hfj.symm).trans hv'.symm)
  · exact lPlusGluedCorrectedRotation2_rotation_iff_of_not_upperLeft_vertex
      hτ hp P hqMode Tpath hfin hleft hk d e hUL

/-- Helper toward Lemma 5.5: rotation 4 agrees with rotation 2 at every
input away from the terminal vertex star. -/
theorem lPlusGluedCorrectedRotation4_eq_rotation2_of_ne_terminal
    (hn : 0 < (es).length) (d : Q)
    (hd : kmswLimitDartVertex w (D d).val ≠
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = C d := by
  let t := UL (⟨(es).length - 1, by omega⟩, false)
  have hrot := (lPlusGluedCorrectedRotation2_rotation_iff_of_ne_terminal
    hτ hp P hqMode Tpath hfin hleft hk hn d (C d) hd).mp rfl
  obtain ⟨n, _, hend, _⟩ := hrot
  have hv : kmswLimitDartVertex w (D (C d)).val = kmswLimitDartVertex w (D d).val :=
    ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
      ⟨n, by simpa only [Equiv.Perm.coe_pow] using hend⟩).symm
  apply lPlusGluedCorrectedRotation4_eq_rotation2_of_ne
    hτ hp P hqMode Tpath hfin hleft hk hn d
  · intro he
    exact hd (hv.symm.trans (congrArg (fun a => kmswLimitDartVertex w (D a).val) he))
  · intro he
    exact hd (hv.symm.trans ((congrArg (fun a => kmswLimitDartVertex w (D a).val) he).trans
      (lPlusPrefixExtendedRotation_vertex hτ hp P hqMode Tpath hfin hleft hk t)))

/-- Helper toward Lemma 5.5: every nonterminal star is transported by
the corrected decoder, with no premise asserting a rotation identity. -/
theorem lPlusGluedCorrectedRotation4_rotation_iff_of_ne_terminal
    (hn : 0 < (es).length) (d e : Q)
    (hd : kmswLimitDartVertex w (D d).val ≠
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
      (S).rotation (D d).val (D e).val := by
  rw [lPlusGluedCorrectedRotation4_eq_rotation2_of_ne_terminal
    hτ hp P hqMode Tpath hfin hleft hk hn d hd]
  exact lPlusGluedCorrectedRotation2_rotation_iff_of_ne_terminal
    hτ hp P hqMode Tpath hfin hleft hk hn d e hd

/-- Helper toward Lemma 5.5: for every terminal configuration, the
attachment port still has its correct successor. That successor is allocated
after the stopped prefix and is outside the exchanged prefix pair. -/
theorem lPlusGluedCorrectedRotation4_terminal_eq_rotation2
    (hn : 0 < (es).length) :
    let t := UL (⟨(es).length - 1, by omega⟩, false)
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk t = C t := by
  let i : Fin (es).length := ⟨(es).length - 1, by omega⟩
  let t := UL (i, false)
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let F := lPlusBlockDartImage
    (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
  let p : LPlusPrefixDart W h k :=
    ⟨(es[i.val], false), lPlusUpperLeftEdge_mem_prefix hτ hfin hk i⟩
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  have hPE : PE t = IP (PR p) := PR.extendDomain_apply_image _ p
  have hnext : kmswInfRot w (H.1 0) (D t).val ∈ Set.range F := by
    obtain ⟨q, hq⟩ := lPlus_upperLeft_west_successor_mem_primed
      (H := H) hτ hfin i
    exact ⟨.inr (.inl q), hq⟩
  obtain ⟨n, hnpos, hend, hgap⟩ := lPlusGluedCorrectedRotation2_terminal_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk hn
  change (kmswInfRot w (H.1 0) : _ → _)^[n] (D t).val = (D (C t)).val at hend
  have hn1 : n = 1 := by
    by_contra hne
    exact hgap 1 (by omega) (by omega) (by simpa only [Function.iterate_one] using hnext)
  have hbound := lPlus_stage_upperLeft_west_successor_new w h (H.1 0)
    (boundaryHitTime w h k) (es[i.val])
    (List.mem_reverse.mp (List.getElem_mem i.isLt))
  have hnew : (kmswStage w (boundaryHitTime w h k)).nextEdge ≤ (D (C t)).val.1 := by
    rw [hn1, Function.iterate_one] at hend
    exact hend ▸ hbound
  have hnotP (q : LPlusPrefixDart W h k) : C t ≠ IP q := by
    intro he
    have hq := boundaryGluingPrefixMinusEdges_subset W h k q.property
    change q.val.1 < (kmswStage w (boundaryHitTime w h k)).nextEdge at hq
    have he' := congrArg (fun a => (D a).val.1) he
    change (D (C t)).val.1 = q.val.1 at he'
    omega
  apply lPlusGluedCorrectedRotation4_eq_rotation2_of_ne
    hτ hp P hqMode Tpath hfin hleft hk hn t
  · exact hnotP p
  · rw [hPE]
    exact hnotP (PR p)

/-- Helper toward Lemma 5.5: the terminal attachment port transports
rotation for every nonempty attachment and every output dart. -/
theorem lPlusGluedCorrectedRotation4_terminal_rotation_iff
    (hn : 0 < (es).length) (e : Q) :
    let t := UL (⟨(es).length - 1, by omega⟩, false)
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk t = e ↔
      (S).rotation (D t).val (D e).val := by
  dsimp only
  rw [lPlusGluedCorrectedRotation4_terminal_eq_rotation2
    hτ hp P hqMode Tpath hfin hleft hk hn]
  exact lPlusGluedCorrectedRotation2_upperLeft_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk _ false e

/-- Helper toward Lemma 5.5: when the attachment is empty, rotation
transport is already complete on every dart. -/
theorem lPlusGluedCorrectedRotation4_rotation_iff_of_empty
    (hn : ¬ 0 < (es).length) (d e : Q) :
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
      (S).rotation (D d).val (D e).val := by
  rw [lPlusGluedCorrectedRotation4_eq_rotation2_of_empty
    hτ hp P hqMode Tpath hfin hleft hk hn]
  apply lPlusGluedCorrectedRotation2_rotation_iff_of_not_upperLeft_vertex
    hτ hp P hqMode Tpath hfin hleft hk d e
  rintro ⟨f, hf, _⟩
  have hf' : f ∈ es := List.mem_reverse.mpr hf
  have hemp : es = [] := List.length_eq_zero_iff.mp (by omega)
  rw [hemp] at hf'
  exact List.not_mem_nil hf'

/-- Helper toward Lemma 5.5: reversing the finite prefix at its terminal
cap corrects the obstructing left/down dart. All witness binders are retained. -/
theorem lPlusGluedCorrectedRotation4_transports_left_down
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    ∃ d t : Q, (D d).val = (2, false) ∧ (D t).val = (1, false) ∧
      lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = t ∧
      (S).rotation (D d).val (D t).val := by
  subst k
  let D₁ := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  let PE₁ := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let C₁ := lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
  let S₁ := m0GeodesicSide hp P ThinMapSide.left
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let es₁ := List.reverse (List.dropLast
    (State.UL (kmswStage w (boundaryHitTime w h 1))))
  have htime := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hprev : boundaryHitTime w h 1 - 1 = 1 := by omega
  have hes : es₁ = [1] := by
    dsimp only [es₁]
    rw [htime]
    simp [kmswStage, hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hn : 0 < es₁.length := by rw [hes]; decide
  let i : Fin es₁.length := ⟨es₁.length - 1, by omega⟩
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
  have htv : (D₁ t).val = (1, false) := by
    change (es₁[i.val], false) = _
    simp [i, hes]
  have hmem (e : ℕ) (he : e < 3) : e ∈ boundaryGluingPrefixMinusEdges W h 1 := by
    rw [lPlusPrefixMinusEdges_eq_previousStage (W := W) (h := h) (by omega : 0 < (1 : ℤ))]
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
    rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk (by omega : 0 < (1 : ℤ))]
    apply Subtype.ext
    have hlocal : ∀ (n : ℕ) (hn : n = 1) (he : 1 < (kmswStage w n).nextEdge),
        ((stageRot w n (⟨1, he⟩, false)).1.val,
          (stageRot w n (⟨1, he⟩, false)).2) = (2, false) := by
      intro n hn he
      subst n
      exact congrArg (fun q : StageDart (kmswStage w 1).nextEdge => (q.1.val, q.2)) hstage
    exact hlocal _ hprev _
  have hpt : IP p = t := by
    apply D₁.injective
    exact Subtype.ext htv.symm
  have hPE : PE₁ t = IP r := by
    rw [← hpt]
    exact (PR.extendDomain_apply_image _ p).trans (congrArg IP hPR)
  obtain ⟨d, hdv, hfix, _⟩ :=
    lPlusGluedCorrectedRotation2_terminal_nonport_obstruction
      hτ hp P hqMode Tpath hfin hleft hk rfl hc₀ hc₁
  have hrd : IP r = d := by
    apply D₁.injective
    exact Subtype.ext hdv.symm
  have hnew : lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = t := by
    rw [lPlusGluedCorrectedRotation4_apply hτ hp P hqMode Tpath hfin hleft hk hn d]
    change Equiv.swap t (PE₁ t) (C₁ d) = t
    rw [hfix, hPE, hrd, Equiv.swap_apply_right]
  have hrot : (S₁).rotation (D₁ d).val (D₁ t).val := by
    refine ⟨1, by omega, ?_, ?_⟩
    · rw [hdv]
      exact (lPlus_first_left_lowerLeft_rotations (H := H) hc₀).1.trans htv.symm
    · intro j hj hj1
      omega
  exact ⟨d, t, hdv, htv, hnew, hrot⟩

/-- Helper toward Lemma 5.5: replace the block side's rotation by the
terminal-cap candidate. All other geometric fields retain their original
IDs and markings; this definition asserts no general marked isomorphism. -/
@[expose] noncomputable def lPlusCodeBlockSide4 : GeometricSideSubmap :=
  { lPlusCodeBlockSide hτ hp P hqMode Tpath hfin hleft hk with
    rotation := fun d e => ∃ a b : Q, (D a).val = d ∧
      lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk a = b ∧
        (D b).val = e }

local notation "B4" => lPlusCodeBlockSide4 hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: replacing the rotation retains every
nonrotation field of the actual side. -/
theorem lPlusCodeBlockSide4_nonrotation_fields :
    { B4 with rotation := (S).rotation } = S :=
  lPlusCodeBlockSide_nonrotation_fields hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the actual and corrected code sides have
the same vertex and dart carriers, via the existing fixed-ID equivalence. -/
@[expose] noncomputable def lPlusActualCodeBlockCellEquiv4 :
    GeometricSideCell S ≃ GeometricSideCell B4 :=
  lPlusActualCodeBlockCellEquiv hτ hp P hqMode Tpath hfin hleft hk

local notation "E4" => lPlusActualCodeBlockCellEquiv4 hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the corrected carrier equivalence preserves
every tag other than rotation, including all exterior boundary marks. -/
theorem lPlusActualCodeBlockCellEquiv4_relation_iff_of_ne_rotation
    (t : TruncationRelation) (ht : t ≠ .rotation)
    (u v : GeometricSideCell S) :
    geometricSideRelation S t u v ↔ geometricSideRelation B4 t (E4 u) (E4 v) := by
  cases t <;> cases u <;> cases v <;>
    first | exact False.elim (ht rfl) | rfl

/-- Helper toward Lemma 5.5: the new side relation reads exactly the
candidate permutation on quotient darts. -/
theorem lPlusCodeBlockSide4_rotation_glued_iff (d e : Q) :
    (B4).rotation (D d).val (D e).val ↔
      lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk d = e := by
  change (∃ a b : Q, (D a).val = (D d).val ∧
    lPlusGluedCorrectedRotation4 hτ hp P hqMode Tpath hfin hleft hk a = b ∧
      (D b).val = (D e).val) ↔ _
  constructor
  · rintro ⟨a, b, ha, hab, hb⟩
    have had : a = d := (D).injective (Subtype.ext ha)
    have hbe : b = e := (D).injective (Subtype.ext hb)
    exact had ▸ hbe ▸ hab
  · intro hde
    exact ⟨d, e, rfl, hde, rfl⟩

/-- Helper toward Lemma 5.5: rotation is preserved by the cell equivalence
at every nonterminal vertex star. -/
theorem lPlusActualCodeBlockCellEquiv4_rotation_iff_of_ne_terminal
    (hn : 0 < (es).length)
    (d e : {d : ℕ × Bool // d.1 ∈ (S).edges})
    (hd : kmswLimitDartVertex w d.val ≠
      kmswLimitDartVertex w (es[(es).length - 1], false)) :
    geometricSideRelation S .rotation (.inr d) (.inr e) ↔
      geometricSideRelation B4 .rotation (E4 (.inr d)) (E4 (.inr e)) := by
  change (S).rotation d.val e.val ↔ (B4).rotation d.val e.val
  obtain ⟨a, rfl⟩ := (D).surjective d
  obtain ⟨b, rfl⟩ := (D).surjective e
  exact (lPlusGluedCorrectedRotation4_rotation_iff_of_ne_terminal
    hτ hp P hqMode Tpath hfin hleft hk hn a b hd).symm.trans
      (lPlusCodeBlockSide4_rotation_glued_iff hτ hp P hqMode Tpath hfin hleft hk a b).symm

/-- Helper toward Lemma 5.5: the empty-attachment case has a complete
marked isomorphism, including every rotation and nonrotation tag. -/
theorem boundaryGluing_nonneg_left_markedIso_lPlusCodeBlockSide4_of_empty
    (hn : ¬ 0 < (es).length) :
    Nonempty (GeometricSideMarkedIso S B4) := by
  refine ⟨{ equiv := E4, relation_iff := ?_ }⟩
  intro t u v
  by_cases ht : t = .rotation
  · subst t
    cases u with
    | inl u => cases v <;> rfl
    | inr d =>
      cases v with
      | inl v => rfl
      | inr e =>
        change (S).rotation d.val e.val ↔ (B4).rotation d.val e.val
        obtain ⟨a, rfl⟩ := (D).surjective d
        obtain ⟨b, rfl⟩ := (D).surjective e
        exact (lPlusGluedCorrectedRotation4_rotation_iff_of_empty
          hτ hp P hqMode Tpath hfin hleft hk hn a b).symm.trans
            (lPlusCodeBlockSide4_rotation_glued_iff
              hτ hp P hqMode Tpath hfin hleft hk a b).symm
  · exact lPlusActualCodeBlockCellEquiv4_relation_iff_of_ne_rotation
      hτ hp P hqMode Tpath hfin hleft hk t ht u v

end DirectedDistances.PaperProofs.Section5

































































































































