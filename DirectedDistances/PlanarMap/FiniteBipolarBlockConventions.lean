/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarIncomingBlock

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- At the source, the rightmost outgoing dart is followed in `rot⁻¹` order
by the canonical leftmost outgoing dart. This is the source-corner convention
from the marked outer face. Helper toward `lem-lr-ind` and the inverse KMSW -/
theorem source_rightmostOutgoing_corner_eq_leftmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.map.toCombinatorialMap.rot.symm
        (rightmostOutgoing B B.source (bipolar_source_ne_sink B)) =
      leftmostOutgoing B B.source (bipolar_source_ne_sink B) := by
  rw [rightmostOutgoing_source_eq_firstRightDart,
    leftmostOutgoing_source_eq_firstLeftDart]
  simpa [CombinatorialMap.faceSucc, B.map.toCombinatorialMap.edgeInv_invol] using
    outerFace_sourceCorner_eq_firstLeftDart B

/-- At a non-pole vertex, the successor of the leftmost outgoing dart in
`rot` order is the leftmost incoming reverse dart. Helper toward `lem-lr-ind`
and the inverse KMSW trees; not the paper result -/
theorem leftmostOutgoing_rot_eq_leftmostIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    B.map.toCombinatorialMap.rot (leftmostOutgoing B v ht) =
      leftmostIncoming B v hs := by
  let q := B.map.toCombinatorialMap.rot (leftmostOutgoing B v ht)
  have hO := leftmostOutgoing_internal_characterization B v hs ht
  have hrotSame : dartTailVertex B.map
      (B.map.toCombinatorialMap.rot (leftmostOutgoing B v ht)) =
      dartTailVertex B.map (leftmostOutgoing B v ht) := by
    apply Quotient.sound
    change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.rot (leftmostOutgoing B v ht))
      (leftmostOutgoing B v ht)
    exact Equiv.Perm.sameCycle_inv.mp ⟨1, by simp⟩
  have hqv : dartTailVertex B.map q = v := by
    simpa [q] using hrotSame.trans hO.1
  have hqnot : ¬ B.map.tail q := by
    simpa [q] using hO.2.2.1
  have hnext : B.map.tail (B.map.toCombinatorialMap.rot.symm q) := by
    simpa [q] using hO.2.1
  exact (leftmostIncoming_internal_characterization B v hs ht).2.2.2
    q hqv hqnot hnext

/-- At the sink, the last left-boundary dart is followed on the marked outer
face by the reverse of the last right-boundary dart. This is the sink-corner
identity supplied by `outerSplit`. Helper toward `lem-lr-ind` and the inverse -/
theorem outerFace_sinkCorner_eq_lastRightReverse
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.map.toCombinatorialMap.faceSucc
        (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) =
      B.map.toCombinatorialMap.edgeInv
        (pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos)) := by
  let xs := B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv
  let dL := pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)
  let dR := pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos)
  have hℓpos : 0 < ℓ := Nat.zero_lt_of_lt B.left_length_pos
  have hrpos : 0 < r := Nat.zero_lt_of_lt B.right_length_pos
  have hlen : xs.length = ℓ + r := by
    simp [xs, B.leftPath.darts_length, B.rightPath.darts_length]
  have hnodup : xs.Nodup := by
    simpa [xs] using B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hi : ℓ - 1 < xs.length := by rw [hlen]; omega
  have hnexti : ℓ < xs.length := by rw [hlen]; omega
  have hleftmem : dL ∈ B.leftPath.darts := by
    exact List.get_mem B.leftPath.darts
      ⟨ℓ - 1, by rw [B.leftPath.darts_length]; omega⟩
  have houter : B.map.IsOuter dL := by
    have hul : dL ∈ B.map.ulDarts :=
      (B.outerSplit.2.2.1 dL).mp hleftmem
    change ¬ B.map.missing dL ∧ B.map.tail dL ∧ B.map.IsOuter dL at hul
    exact hul.2.2
  have hword : dL ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 dL).mpr houter
  have hfaceWord : B.map.toCombinatorialMap.faceSucc dL =
      B.outerWord.letters.formPerm dL := B.outerSplit.1.2.2 dL hword
  have hface : B.map.toCombinatorialMap.faceSucc dL = xs.formPerm dL := by
    calc
      B.map.toCombinatorialMap.faceSucc dL = B.outerWord.letters.formPerm dL := hfaceWord
      _ = xs.formPerm dL := by
        simpa [xs] using congrArg (fun p : Equiv.Perm D => p dL)
          (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)
  have hform := List.formPerm_apply_getElem xs hnodup (ℓ - 1) hi
  have hmod : (ℓ - 1 + 1) % xs.length = ℓ := by
    rw [Nat.sub_add_cancel (show 1 ≤ ℓ by omega)]
    rw [hlen]
    rw [Nat.mod_eq_of_lt (show ℓ < ℓ + r by omega)]
  have hidxL : dL = xs[ℓ - 1]'hi := by
    dsimp [dL, pathLastDart, xs]
    rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; omega)]
  have hcorner : B.map.toCombinatorialMap.faceSucc dL = xs[ℓ]'hnexti := by
    calc
      B.map.toCombinatorialMap.faceSucc dL = xs.formPerm dL := hface
      _ = xs[(ℓ - 1 + 1) % xs.length]'(by rw [hmod]; exact hnexti) := by
        rw [hidxL]
        exact hform
      _ = xs[ℓ]'hnexti := by simp only [hmod]
  have hrightmem : dR ∈ B.rightPath.darts := by
    exact List.get_mem B.rightPath.darts
      ⟨r - 1, by rw [B.rightPath.darts_length]; omega⟩
  have hrightLast : (B.rightPath.darts.reverse.map
      B.map.toCombinatorialMap.edgeInv)[0]'(by
        simpa [B.rightPath.darts_length] using hrpos) =
      B.map.toCombinatorialMap.edgeInv dR := by
    simp [dR, pathLastDart, List.get_eq_getElem, B.rightPath.darts_length]
  have hright : xs[ℓ]'hnexti =
      B.map.toCombinatorialMap.edgeInv dR := by
    simpa [xs, List.getElem_append_right, B.leftPath.darts_length] using hrightLast
  simpa [dL, dR] using hcorner.trans hright

/-- At the sink, `leftmostIncoming` is followed in `rot⁻¹` order by
`rightmostIncoming`, as forced by the outer-face corner. Helper toward
`lem-lr-ind` and the inverse KMSW trees; not the paper result -/
theorem sink_leftmostIncoming_corner_eq_rightmostIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.map.toCombinatorialMap.rot.symm
        (leftmostIncoming B B.sink (bipolar_source_ne_sink B).symm) =
      rightmostIncoming B B.sink (bipolar_source_ne_sink B).symm := by
  rcases incomingSelectors_sink_boundary B with ⟨hl, hr⟩
  rw [hl, hr]
  simpa [CombinatorialMap.faceSucc] using outerFace_sinkCorner_eq_lastRightReverse B

/-- At a non-pole vertex, the successor of the rightmost incoming reverse
dart in `rot` order is the rightmost outgoing dart. Helper toward `lem-lr-ind`
and the inverse KMSW trees; not the paper result -/
theorem rightmostIncoming_rot_eq_rightmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    B.map.toCombinatorialMap.rot (rightmostIncoming B v hs) =
      rightmostOutgoing B v ht := by
  let q := B.map.toCombinatorialMap.rot (rightmostIncoming B v hs)
  have hI := rightmostIncoming_internal_characterization B v hs ht
  have hO := rightmostOutgoing_internal_characterization B v hs ht
  have hrotSame : dartTailVertex B.map
      (B.map.toCombinatorialMap.rot (rightmostIncoming B v hs)) =
      dartTailVertex B.map (rightmostIncoming B v hs) := by
    apply Quotient.sound
    change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.rot (rightmostIncoming B v hs))
      (rightmostIncoming B v hs)
    exact Equiv.Perm.sameCycle_inv.mp ⟨1, by simp⟩
  have hqv : dartTailVertex B.map q = v := by
    simpa [q] using hrotSame.trans hI.1
  have hq : B.map.tail q := by simpa [q] using hI.2.2.1
  have hprev : ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm q) := by
    simpa [q] using hI.2.1
  exact hO.2.2.2 q hqv hq hprev

/-- In `rot⁻¹` order, the leftmost incoming reverse dart is followed by the
leftmost outgoing dart. Helper toward `lem-lr-ind` and the inverse KMSW trees; -/
theorem leftmostIncoming_rot_symm_eq_leftmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    B.map.toCombinatorialMap.rot.symm (leftmostIncoming B v hs) =
      leftmostOutgoing B v ht := by
  calc
    B.map.toCombinatorialMap.rot.symm (leftmostIncoming B v hs) =
        B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.rot (leftmostOutgoing B v ht)) :=
      congrArg B.map.toCombinatorialMap.rot.symm
        (leftmostOutgoing_rot_eq_leftmostIncoming B v hs ht).symm
    _ = leftmostOutgoing B v ht := by simp

/-- In `rot⁻¹` order, the rightmost outgoing dart is followed by the
rightmost incoming reverse dart. Helper toward `lem-lr-ind` and the inverse -/
theorem rightmostOutgoing_rot_symm_eq_rightmostIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    B.map.toCombinatorialMap.rot.symm (rightmostOutgoing B v ht) =
      rightmostIncoming B v hs := by
  calc
    B.map.toCombinatorialMap.rot.symm (rightmostOutgoing B v ht) =
        B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.rot (rightmostIncoming B v hs)) :=
      congrArg B.map.toCombinatorialMap.rot.symm
        (rightmostIncoming_rot_eq_rightmostOutgoing B v hs ht).symm
    _ = rightmostIncoming B v hs := by simp

/-- At a non-pole vertex, the outgoing darts form the initial segment of the
`rot⁻¹` cycle from `leftmostOutgoing` through `rightmostOutgoing`. Every
outgoing dart occurs on this segment, every intermediate iterate is outgoing,
and its number of darts is the out-degree. Helper toward `lem-lr-ind` and the
inverse KMSW trees; not the paper result -/
theorem internal_outgoing_block_segment
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ∃ k₀,
      B.map.toCombinatorialMap.rot.symm^[k₀] (leftmostOutgoing B v ht) =
        rightmostOutgoing B v ht ∧
      k₀ + 1 = Nat.card {q : D // dartTailVertex B.map q = v ∧ B.map.tail q} ∧
      (∀ q, dartTailVertex B.map q = v → B.map.tail q →
        ∃ k ≤ k₀,
          B.map.toCombinatorialMap.rot.symm^[k] (leftmostOutgoing B v ht) = q ∧
          ∀ j ≤ k, B.map.tail
            (B.map.toCombinatorialMap.rot.symm^[j] (leftmostOutgoing B v ht))) ∧
      (∃ k₁,
        B.map.toCombinatorialMap.rot.symm^[k₁] (rightmostIncoming B v hs) =
          leftmostIncoming B v hs ∧
        ∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
          ∃ k ≤ k₁,
            B.map.toCombinatorialMap.rot.symm^[k] (rightmostIncoming B v hs) = q ∧
            ∀ j ≤ k, ¬ B.map.tail
              (B.map.toCombinatorialMap.rot.symm^[j] (rightmostIncoming B v hs))) := by
  classical
  let p : Equiv.Perm D := B.map.toCombinatorialMap.rot.symm
  let x := leftmostOutgoing B v ht
  let ro := rightmostOutgoing B v ht
  let li := leftmostIncoming B v hs
  let hblock := incoming_block B v hs ht
  let blockLi := blockLeftIncoming B v hs ht
  let blockRo := blockRightOutgoing B v hs ht
  rcases Classical.choose_spec (Classical.choose_spec hblock) with
    ⟨hbliV, hbliNot, hbroV, hbroTail, hbliNext, hbroNext,
      hstayIn, hstayOut, _, _⟩
  have hO := leftmostOutgoing_internal_characterization B v hs ht
  have hRo := rightmostOutgoing_internal_characterization B v hs ht
  have hLi := leftmostIncoming_internal_characterization B v hs ht
  have hRi := rightmostIncoming_internal_characterization B v hs ht
  have hliEq : li = blockLi := by simp [li, leftmostIncoming, ht, blockLi]
  have hroEq : ro = blockRo := by simp [ro, rightmostOutgoing, hs, blockRo]
  have hOtail : B.map.tail x := hO.2.1
  have hcycleRo : Equiv.Perm.SameCycle p x ro := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hO.1.trans hRo.1.symm)
  have hcycleLi : Equiv.Perm.SameCycle p x li := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hO.1.trans hLi.1.symm)
  have hperiodOrder : p^[orderOf p] x = x := by
    rw [Equiv.Perm.iterate_eq_pow]
    exact congrArg (fun e : Equiv.Perm D => e x) (pow_orderOf_eq_one p)
  let returns (n : ℕ) : Prop := 0 < n ∧ p^[n] x = x
  have hexReturns : ∃ n, returns n := ⟨orderOf p, orderOf_pos p, hperiodOrder⟩
  let T := Nat.find hexReturns
  have hT : 0 < T ∧ p^[T] x = x := Nat.find_spec hexReturns
  have hTmin (n : ℕ) (hn : n < T) : ¬ returns n := Nat.find_min hexReturns hn
  let xs := List.ofFn (fun i : Fin T => p^[i.val] x)
  have hlen : xs.length = T := by simp [xs]
  have hlenPos : 0 < xs.length := by rw [hlen]; exact hT.1
  have hnodup : xs.Nodup := by
    apply List.nodup_iff_injective_getElem.mpr
    intro i j heq
    have hpow : p^[i.val] x = p^[j.val] x := by simpa [xs] using heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hdecomp : p^[j.val] x = p^[i.val] (p^[j.val - i.val] x) := by
        have hsum : i.val + (j.val - i.val) = j.val :=
          Nat.add_sub_of_le (Nat.le_of_lt hij)
        simpa [hsum] using Function.iterate_add_apply p i.val (j.val - i.val) x
      have hcancel : p^[i.val] (p^[j.val - i.val] x) = p^[i.val] x :=
        hdecomp.symm.trans hpow.symm
      have hreturn : p^[j.val - i.val] x = x :=
        (Equiv.injective (p ^ i.val)) (by
          simpa [Equiv.Perm.iterate_eq_pow] using hcancel)
      exact (hTmin _ (by omega)) ⟨by omega, hreturn⟩
    · have hdecomp : p^[i.val] x = p^[j.val] (p^[i.val - j.val] x) := by
        have hsum : j.val + (i.val - j.val) = i.val :=
          Nat.add_sub_of_le (Nat.le_of_lt hji)
        simpa [hsum] using Function.iterate_add_apply p j.val (i.val - j.val) x
      have hcancel : p^[j.val] (p^[i.val - j.val] x) = p^[j.val] x :=
        hdecomp.symm.trans hpow
      have hreturn : p^[i.val - j.val] x = x :=
        (Equiv.injective (p ^ j.val)) (by
          simpa [Equiv.Perm.iterate_eq_pow] using hcancel)
      exact (hTmin _ (by omega)) ⟨by omega, hreturn⟩
  have hiter (i : ℕ) (hi : i < xs.length) : xs[i] = p^[i] x := by
    simp [xs]
  have hcycleMem (q : D) (hq : Equiv.Perm.SameCycle p x q) : q ∈ xs := by
    obtain ⟨n, hn, hpow⟩ := hq.exists_pow_eq'
    let k := n % T
    have hk : k < T := Nat.mod_lt _ hT.1
    have hpowIter : p^[n] x = q := by simpa [Equiv.Perm.iterate_eq_pow] using hpow
    have hmultiple : p^[T * (n / T)] x = x := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hT.2 (n / T)
    have hmodEq : n % T + T * (n / T) = n := Nat.mod_add_div n T
    have hreduce : p^[n] x = p^[k] x := by
      calc
        p^[n] x = p^[n % T + T * (n / T)] x :=
          congrArg (fun m : ℕ => p^[m] x) hmodEq.symm
        _ = p^[n % T] (p^[T * (n / T)] x) :=
          Function.iterate_add_apply p (n % T) (T * (n / T)) x
        _ = p^[n % T] x := by rw [hmultiple]
    have hpowReduced : p^[k] x = q := by simpa [k] using hreduce.symm.trans hpowIter
    change q ∈ List.ofFn (fun i : Fin T => p^[i.val] x)
    rw [List.mem_ofFn']
    exact ⟨⟨k, hk⟩, hpowReduced⟩
  have hvertexIter : ∀ i, dartTailVertex B.map (p^[i] x) = v := by
    intro i
    induction i with
    | zero => simpa [x] using hO.1
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact vertexRotationCycle_successor_mem B v ⟨p^[i] x, ih⟩
  have hxsVertex (i : ℕ) (hi : i < xs.length) :
      dartTailVertex B.map xs[i] = v := by
    rw [hiter i hi]
    exact hvertexIter i
  have hstep (i : ℕ) (hi : i + 1 < xs.length) :
      xs[i + 1] = p (xs[i]) := by
    have hi0 : i < xs.length := by omega
    rw [hiter (i + 1) hi, hiter i hi0]
    rw [show i + 1 = Nat.succ i by omega, Function.iterate_succ_apply']
  have hcycleSupportRo : ro ∈ xs := hcycleMem ro hcycleRo
  obtain ⟨k, hk, hgetRo⟩ := List.getElem_of_mem hcycleSupportRo
  have hgetZero : xs[0]'hlenPos = x := by
    exact hiter 0 (by rw [hlen]; exact hT.1)
  have hroTail : B.map.tail ro := hRo.2.1
  have hriNotTail : ¬ B.map.tail (rightmostIncoming B v hs) := hRi.2.1
  have hriNeX : rightmostIncoming B v hs ≠ x := by
    intro heq
    exact hriNotTail (heq ▸ hOtail)
  have hkSucc : k + 1 < xs.length := by
    by_contra hbound
    have heqLen : k + 1 = T := by rw [← hlen]; omega
    have hpowNext : p^[k + 1] x = rightmostIncoming B v hs := by
      calc
        p^[k + 1] x = p (p^[k] x) := by
          rw [show k + 1 = Nat.succ k by omega, Function.iterate_succ_apply']
        _ = p (xs[k]) := by rw [← hiter k hk]
        _ = p ro := by rw [hgetRo]
        _ = rightmostIncoming B v hs := rightmostOutgoing_rot_symm_eq_rightmostIncoming B v hs ht
    have hreturn : p^[k + 1] x = x := by simpa [heqLen] using hT.2
    exact hriNeX (hpowNext.symm.trans hreturn)
  have hgetRi : xs[k + 1]'hkSucc = rightmostIncoming B v hs := by
    calc
      xs[k + 1] = p^[k + 1] x := hiter _ hkSucc
      _ = rightmostIncoming B v hs := by
        calc
          p^[k + 1] x = p (p^[k] x) := by
            rw [show k + 1 = Nat.succ k by omega, Function.iterate_succ_apply']
          _ = p (xs[k]) := by rw [← hiter k hk]
          _ = p ro := by rw [hgetRo]
          _ = rightmostIncoming B v hs :=
            rightmostOutgoing_rot_symm_eq_rightmostIncoming B v hs ht
  have hleftAdj : p li = x := leftmostIncoming_rot_symm_eq_leftmostOutgoing B v hs ht
  have hprefix : ∀ i (hi : i < xs.length), i ≤ k → B.map.tail xs[i] := by
    intro i hi
    induction i with
    | zero =>
        intro _
        rw [hgetZero]
        exact hOtail
    | succ i ih =>
        intro hle
        have hlenI : i + 1 < xs.length := by simpa using hi
        have hiLen : i < xs.length := by omega
        have hprev := ih hiLen (by omega)
        have hneRo : xs[i] ≠ ro := by
          intro heq
          have hidx : i = k := hnodup.getElem_inj_iff.mp (heq.trans hgetRo.symm)
          omega
        have hneBlockRo : xs[i] ≠ blockRo := by
          intro heq
          exact hneRo (heq.trans hroEq.symm)
        have hstay := hstayOut (xs[i]) (hxsVertex i hiLen) hprev hneBlockRo
        rw [← hstep i hlenI] at hstay
        exact hstay
  have hsuffix : ∀ i (hi : i < xs.length), k + 1 ≤ i → ¬ B.map.tail xs[i] := by
    intro i hi
    induction i with
    | zero => intro hlo; omega
    | succ i ih =>
        intro hlo
        have hlenI : i + 1 < xs.length := by simpa using hi
        by_cases hik : i = k
        · subst i
          rw [hgetRi]
          exact hriNotTail
        · have hprevBound : k + 1 ≤ i := by omega
          have hiLen : i < xs.length := by omega
          have hprev := ih hiLen hprevBound
          have hneLi : xs[i] ≠ li := by
            intro heq
            have hnextX : xs[i + 1] = x := by rw [hstep i hlenI, heq, hleftAdj]
            have hdup : xs[i + 1] = xs[0]'hlenPos := hnextX.trans hgetZero.symm
            have hidx : i + 1 = 0 := hnodup.getElem_inj_iff.mp hdup
            omega
          have hneBlockLi : xs[i] ≠ blockLi := by
            intro heq
            exact hneLi (heq.trans hliEq.symm)
          have hstay := hstayIn (xs[i]) (hxsVertex i hiLen) hprev hneBlockLi
          rw [← hstep i hlenI] at hstay
          exact hstay
  let Out := {q : D // dartTailVertex B.map q = v ∧ B.map.tail q}
  let f : Fin (k + 1) → Out := fun i =>
    ⟨xs[i.val], ⟨hxsVertex i.val (by omega), hprefix i.val (by omega) (by omega)⟩⟩
  have hfInj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hnodup.getElem_inj_iff.mp (congrArg Subtype.val hij)
  have hfSurj : Function.Surjective f := by
    intro q
    have hcycleQ : Equiv.Perm.SameCycle p x q.1 := by
      apply Equiv.Perm.sameCycle_inv.mpr
      exact Quotient.exact (hO.1.trans q.2.1.symm)
    have hmem : q.1 ∈ xs := hcycleMem q.1 hcycleQ
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    have hiLe : i ≤ k := by
      by_contra hnot
      have hgt : k + 1 ≤ i := by omega
      have htailAtI : B.map.tail xs[i] := by simpa [hget] using q.2.2
      exact hsuffix i hi hgt htailAtI
    refine ⟨⟨i, by omega⟩, ?_⟩
    apply Subtype.ext
    exact hget
  let e : Fin (k + 1) ≃ Out := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
  have hcard : Nat.card Out = k + 1 := by
    calc
      Nat.card Out = Nat.card (Fin (k + 1)) := Nat.card_congr e.symm
      _ = k + 1 := by simp
  refine ⟨k, ?_, hcard.symm, ?_, ?_⟩
  · simpa [x, ro] using (hiter k hk).symm.trans hgetRo
  · intro q hqv hqt
    obtain ⟨i, hEq⟩ := hfSurj ⟨q, hqv, hqt⟩
    have hget : xs[i.val] = q := congrArg Subtype.val hEq
    refine ⟨i.val, by omega, ?_, ?_⟩
    · simpa [x] using (hiter i.val (by omega)).symm.trans hget
    · intro j hj
      have htail := hprefix j (by omega) (by omega)
      rw [hiter j (by omega)] at htail
      simpa [x, p] using htail
  · let ki := T - (k + 1) - 1
    have hki : k + 1 + ki = T - 1 := by
      dsimp [ki]
      omega
    have hlastPow : p^[T - 1] x = li := by
      have hsubadd : T - 1 + 1 = T := by omega
      have hT' : p^[T - 1 + 1] x = x := by rw [hsubadd]; exact hT.2
      have hstepLast : p^[T - 1 + 1] x = p (p^[T - 1] x) := by
        rw [show T - 1 + 1 = Nat.succ (T - 1) by omega,
          Function.iterate_succ_apply']
      have hprev : p (p^[T - 1] x) = x := hstepLast.symm.trans hT'
      exact p.injective (hprev.trans hleftAdj.symm)
    have hstartIn : p^[k + 1] x = rightmostIncoming B v hs := by
      exact (hiter (k + 1) hkSucc).symm.trans hgetRi
    have hendIn : p^[ki] (rightmostIncoming B v hs) = li := by
      calc
        p^[ki] (rightmostIncoming B v hs) = p^[ki] (p^[k + 1] x) :=
          congrArg (fun z => p^[ki] z) hstartIn.symm
        _ = p^[ki + (k + 1)] x := (Function.iterate_add_apply p ki (k + 1) x).symm
        _ = p^[T - 1] x := by rw [show ki + (k + 1) = T - 1 by omega]
        _ = li := hlastPow
    refine ⟨ki, ?_, ?_⟩
    · simpa [li] using hendIn
    · intro q hqv hqnot
      have hcycleQ : Equiv.Perm.SameCycle p x q := by
        apply Equiv.Perm.sameCycle_inv.mpr
        exact Quotient.exact (hO.1.trans hqv.symm)
      have hmem : q ∈ xs := hcycleMem q hcycleQ
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
      have hqAt : ¬ B.map.tail xs[i] := by simpa [hget] using hqnot
      have hiLower : k + 1 ≤ i := by
        by_contra hle
        have hiUpper : i ≤ k := by omega
        exact hqAt (hprefix i hi hiUpper)
      let m := i - (k + 1)
      have hmLe : m ≤ ki := by dsimp [m, ki]; omega
      have hdecomp : m + (k + 1) = i := by dsimp [m]; omega
      have hqIter : p^[m] (rightmostIncoming B v hs) = q := by
        calc
          p^[m] (rightmostIncoming B v hs) = p^[m] (p^[k + 1] x) :=
            congrArg (fun z => p^[m] z) hstartIn.symm
          _ = p^[m + (k + 1)] x := (Function.iterate_add_apply p m (k + 1) x).symm
          _ = p^[i] x := by rw [hdecomp]
          _ = xs[i] := (hiter i hi).symm
          _ = q := hget
      refine ⟨m, hmLe, ?_, ?_⟩
      · simpa [m, p] using hqIter
      · intro j hj
        have hjIndex : k + 1 + j < xs.length := by rw [hlen]; omega
        have hjAfter : k + 1 ≤ k + 1 + j := by omega
        have hiterRel : p^[j] (rightmostIncoming B v hs) = xs[k + 1 + j] := by
          calc
            p^[j] (rightmostIncoming B v hs) = p^[j] (p^[k + 1] x) :=
              congrArg (fun z => p^[j] z) hstartIn.symm
            _ = p^[j + (k + 1)] x := (Function.iterate_add_apply p j (k + 1) x).symm
            _ = p^[k + 1 + j] x := by rw [Nat.add_comm j (k + 1)]
            _ = xs[k + 1 + j] := (hiter _ hjIndex).symm
        have hnot := hsuffix (k + 1 + j) hjIndex hjAfter
        simpa [p] using (show ¬ B.map.tail (p^[j] (rightmostIncoming B v hs)) by
          rw [hiterRel]
          exact hnot)

/-- At either pole, the canonical boundary corner starts a full rotation scan
of the corresponding uniform orientation class. Every dart at that pole is
reached within `orderOf rot.symm`, and each intermediate dart has the pole's
orientation. Helper toward `lem-lr-ind` and the inverse KMSW trees; not the -/
theorem pole_rotation_cycle_segments
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (∀ q, dartTailVertex B.map q = B.source →
      ∃ k < orderOf B.map.toCombinatorialMap.rot.symm,
        B.map.toCombinatorialMap.rot.symm^[k]
            (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) = q ∧
        ∀ j ≤ k, B.map.tail
          (B.map.toCombinatorialMap.rot.symm^[j]
            (leftmostOutgoing B B.source (bipolar_source_ne_sink B)))) ∧
    (∀ q, dartTailVertex B.map q = B.sink →
      ∃ k < orderOf B.map.toCombinatorialMap.rot.symm,
        B.map.toCombinatorialMap.rot.symm^[k]
            (rightmostIncoming B B.sink (bipolar_source_ne_sink B).symm) = q ∧
        ∀ j ≤ k, ¬ B.map.tail
          (B.map.toCombinatorialMap.rot.symm^[j]
            (rightmostIncoming B B.sink (bipolar_source_ne_sink B).symm))) := by
  let p := B.map.toCombinatorialMap.rot.symm
  have hrpos : 0 < r := Nat.zero_lt_of_lt B.right_length_pos
  have hxSource : dartTailVertex B.map
      (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) = B.source := by
    have h := dartTailVertex_finiteXDPLeftmostCorner B B.source
    rw [finiteXDPLeftmostCorner_source] at h
    rw [leftmostOutgoing_source_eq_firstLeftDart]
    exact h
  have hxSink : dartTailVertex B.map
      (rightmostIncoming B B.sink (bipolar_source_ne_sink B).symm) = B.sink := by
    rcases incomingSelectors_sink_boundary B with ⟨_, hr⟩
    rw [hr]
    have hstep := B.rightPath.edge_step
      ⟨r - 1, by rw [B.rightPath.darts_length]; omega⟩
    have hindex : (r - 1) + 1 = r := by omega
    have hhead : dartHeadVertex B.map
        (pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos)) = B.sink := by
      have hlast : B.rightPath.vertices.get
          ⟨r, by rw [B.rightPath.vertices_length]; omega⟩ =
          dartHeadVertex B.map
            (pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos)) := by
        simpa [pathLastDart, List.get_eq_getElem, hindex] using hstep.2.2.2
      exact hlast.symm.trans B.rightPath.end_vertex
    simpa [dartTailVertex, dartHeadVertex] using hhead
  have hvertexIter (x : D) (v : MapVertex B.map) (hx : dartTailVertex B.map x = v) :
      ∀ j, dartTailVertex B.map (p^[j] x) = v := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact vertexRotationCycle_successor_mem B v ⟨p^[j] x, ih⟩
  constructor
  · intro q hq
    have hcycle : Equiv.Perm.SameCycle p
        (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) q := by
      apply Equiv.Perm.sameCycle_inv.mpr
      exact Quotient.exact (hxSource.trans hq.symm)
    obtain ⟨k, hk, hpow⟩ := hcycle.exists_pow_eq'
    refine ⟨k, ?_, ?_, ?_⟩
    · simpa [p] using hk
    · simpa [p, Equiv.Perm.iterate_eq_pow] using hpow
    · intro j hj
      exact source_vertexRotationCycle_all_outgoing B
        ⟨p^[j] (leftmostOutgoing B B.source (bipolar_source_ne_sink B)),
          hvertexIter _ _ hxSource j⟩
  · intro q hq
    have hcycle : Equiv.Perm.SameCycle p
        (rightmostIncoming B B.sink (bipolar_source_ne_sink B).symm) q := by
      apply Equiv.Perm.sameCycle_inv.mpr
      exact Quotient.exact (hxSink.trans hq.symm)
    obtain ⟨k, hk, hpow⟩ := hcycle.exists_pow_eq'
    refine ⟨k, ?_, ?_, ?_⟩
    · simpa [p] using hk
    · simpa [p, Equiv.Perm.iterate_eq_pow] using hpow
    · intro j hj
      have hrev := sink_vertexRotationCycle_all_reverseIncoming B
        ⟨p^[j] (rightmostIncoming B B.sink (bipolar_source_ne_sink B).symm),
          hvertexIter _ _ hxSink j⟩
      obtain ⟨e, he, _, heq⟩ := hrev
      have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv e) :=
        (B.map.tail_iff e (B.noMissingDarts e)).mp he
      rw [show p^[j] (rightmostIncoming B B.sink
          (bipolar_source_ne_sink B).symm) =
          B.map.toCombinatorialMap.edgeInv e by simpa using heq]
      exact hnot

end DirectedDistances.PlanarMap
